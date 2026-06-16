{
  description = "Geometry is Your Friend";

  inputs = {
    shed.url = "github:must-show-your-work/shed";
    nixpkgs.follows = "shed/nixpkgs";
    flake-parts.follows = "shed/flake-parts";

    # Pinned Python interpreter (3.13.1). nixpkgs-python is per-project
    # because shed's base shell uses whatever python3 nixpkgs ships; giyf
    # needs an exact version for repro of the wheel pin in requirements.txt.
    nixpkgs-python = {
      url = "github:cachix/nixpkgs-python";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  nixConfig = {
    extra-substituters = [ "https://cache.garnix.io" ];
    extra-trusted-public-keys = [ "cache.garnix.io:CTFPyKSLcx5RMJKfLo5EEPUObbA78b0YQ2DTCJXqr9g=" ];
  };

  outputs = { self, nixpkgs, flake-parts, shed, nixpkgs-python, ... } @ inputs:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [ "x86_64-linux" "aarch64-darwin" ];

      perSystem = { config, pkgs, system, ... }: with builtins; let
        # Skip non-attrset entries (e.g. `deps.ci = []` is a flat list
        # consumed directly by `packages.ci.runtimeInputs`, not a
        # dev/ci-split sub-bucket like `deps.python`/`deps.tools`).
        collect = f: deps: concatMap f (filter isAttrs (attrValues deps));

        pythonFlake = nixpkgs-python.packages.${system};
        pythonInterp = pythonFlake."3.13.1";
        pip = pkgs.python3Packages;

        # Runtime libs — `LD_LIBRARY_PATH` so dlopen at import time
        # (kuzu wheel → libstdc++, lean.nvim → libresvg.so) finds them.
        # Keep MINIMAL: extra entries here cause version conflicts with
        # other shell tools (e.g. newer libuv shadows nvim's libluv).
        runtime_deps = [
          pkgs.stdenv.cc.cc.lib
          pkgs.resvg
        ];

        # Link-time libs — `LIBRARY_PATH` so `clang -l<x>` resolves
        # `lib<x>.{so,a}` during `lake exe` compilation. NOT on
        # LD_LIBRARY_PATH; runtime uses RPATH or system loader.
        linker_deps = [
          pkgs.gmp
          pkgs.libuv
          pkgs.llvmPackages.libcxx
        ];

        deps = with pkgs; {
          ci = [];

          python = {
            dev = [];
            ci = [
              pythonInterp
              pip.pip
              pip.venvShellHook
            ];
          };

          tools = {
            dev = [
              bc
              cloc
              curl
              coreutils
              eplot
              gnuplot
              graphviz
              jq
              kuzu
              pandoc
              # `resvg` is on PATH for lean.nvim's terminal-graphics
              # feature (rasterizes ProofWidgets SVG into kitty graphics
              # protocol images). Without it, lean.nvim text-serializes.
              resvg
              ripgrep
              timg
              texlivePackages.pdfcrop
              texlivePackages.dvisvgm
              texlivePackages.latexmk
              watch
              yq-go
              texlive.combined.scheme-full
              pdf2svg
              ghostscript
              poppler-utils
            ];
            ci = [];
          };
        };

        ci_deps = collect (v: v.ci) deps;
        dev_deps = (collect (v: v.dev) deps) ++ ci_deps;

      in {
        packages.ci = pkgs.writeShellApplication {
          name = "ci";
          runtimeInputs = deps.ci;
          text = /* bash */ ''
            just ci
          '';
        };

        devShells.default = shed.lib.mkLeanShell {
          inherit pkgs system;
          name = "giyf dev shell";

          # Toolchain manifest inherited from shed/lib/lean-toolchain-manifest.nix
          # (workspace-wide pin). Override `manifest = { tag, toolchain }` here
          # if giyf ever needs to lag/lead the rest of the workspace.

          extraPackages = dev_deps;

          extraShellHook = /* bash */ ''
            SOURCE_DATE_EPOCH=$(date +%s)
            VENV=.venv

            if test ! -d $VENV; then
              python -m venv $VENV
            fi
            source ./$VENV/bin/activate
            export PYTHONPATH=`pwd`/$VENV/${pkgs.python3.sitePackages}/:$PYTHONPATH
            pip install -r requirements.txt

            export LD_LIBRARY_PATH="${pkgs.lib.makeLibraryPath runtime_deps}''${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
            export LIBRARY_PATH="${pkgs.lib.makeLibraryPath (runtime_deps ++ linker_deps)}''${LIBRARY_PATH:+:$LIBRARY_PATH}"
          '';
        };
      };
    };
}
