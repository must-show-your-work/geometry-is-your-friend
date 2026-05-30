{
  description = "Geometry is Your Friend";

  inputs = {
    # Host-specific absolute path: nix can't follow `path:../shed` once
    # this tree is copied into /nix/store. Long-term, publish shed.
    shed.url = "path:/storage/code/must-show-your-work/shed";
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

          # Bump when ./lean-toolchain changes: refetch with
          #   nix store prefetch-file --hash-type sha256 <url>
          manifest = {
            tag = "v4.30.0-rc2";
            toolchain = {
              x86_64-linux = {
                url  = "https://github.com/leanprover/lean4/releases/download/v4.30.0-rc2/lean-4.30.0-rc2-linux.tar.zst";
                hash = "sha256-W1FiXxVPChOze9iS8dlfeen9W58NCVtBJiFe4ryNvoY=";
              };
              aarch64-linux = {
                url  = "https://github.com/leanprover/lean4/releases/download/v4.30.0-rc2/lean-4.30.0-rc2-linux_aarch64.tar.zst";
                hash = "sha256-sZb0HaI5YOhC/A/AR0nRY51Eg5/q/AQU5Tyy22sWeQ8=";
              };
              x86_64-darwin = {
                url  = "https://github.com/leanprover/lean4/releases/download/v4.30.0-rc2/lean-4.30.0-rc2-darwin.tar.zst";
                hash = "sha256-kqj9gZ002SDuWS8Ay449dEloLEsuQ6B2DCkhpuDn83A=";
              };
              aarch64-darwin = {
                url  = "https://github.com/leanprover/lean4/releases/download/v4.30.0-rc2/lean-4.30.0-rc2-darwin_aarch64.tar.zst";
                hash = "sha256-aiPSYkH9eLzD0cJL6XNBv+P0Y18ub+q8u1hjA1KQqxs=";
              };
            };
          };

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
