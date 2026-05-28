{
  description = "Geometry is Your Friend";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";

    nixpkgs-python = {
      url = "github:cachix/nixpkgs-python";
      inputs = { nixpkgs.follows = "nixpkgs"; };
    };

    lean4-nix = {
      url = "github:lenianiva/lean4-nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  # Garnix binary cache: lean4-nix's CI publishes built Lean binaries
  nixConfig = {
    extra-substituters = [ "https://cache.garnix.io" ];
    extra-trusted-public-keys = [ "cache.garnix.io:CTFPyKSLcx5RMJKfLo5EEPUObbA78b0YQ2DTCJXqr9g=" ];
  };

  outputs = { self, nixpkgs, nixpkgs-python, lean4-nix, flake-parts, ... } @ inputs:
    flake-parts.lib.mkFlake { inherit inputs; } {
      imports = [
      ];

      systems = [ "x86_64-linux" "aarch64-darwin" ];

      perSystem = { config, pkgs, system, ... }: with builtins; let
        # ---- Lean toolchain (v4.30.0-rc2 binary via fetchBinaryLean) ----
        leanToolchain = pkgs.callPackage "${lean4-nix.outPath}/lib/toolchain.nix" {};
        leanManifest = {
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
        leanBin = leanToolchain.fetchBinaryLean leanManifest;
        leanOverlay = final: prev: { lean = leanBin; };
        pkgsLean = import nixpkgs {
          inherit system;
          overlays = [ leanOverlay ];
        };

        # ---- Python tooling (kept as-is, moved into its own shell) ------
        # Skip non-attrset entries (e.g. `deps.ci = []` is a flat list
        # consumed directly by `packages.ci.runtimeInputs`, not a
        # dev/ci-split sub-bucket like `deps.python`/`deps.tools`).
        collect = f: deps: concatMap f (filter isAttrs (attrValues deps));
        pythonFlake = nixpkgs-python.packages.${system};
        pythonInterp = pythonFlake."3.13.1";
        pip = pkgs.python3Packages;
        # Runtime libs — go on `LD_LIBRARY_PATH` so dlopen at import time
        # (e.g. the `kuzu` Python wheel pulling in libstdc++, or lean.nvim's
        # Lua FFI dlopen of `libresvg.so` for SVG rendering) finds them.
        # Keep this set MINIMAL: putting linker-only deps here causes
        # version conflicts with other tools (e.g. shipping a newer
        # libuv shadows nvim's libluv expectations, breaking symbol
        # lookups like `uv_tcp_keepalive_ex`).
        runtime_deps = [
          pkgs.stdenv.cc.cc.lib
          # `libresvg.so` — lean.nvim's `lua/tui/svg.lua` FFI-loads this
          # to rasterize ProofWidgets SVG output into the Kitty graphics
          # protocol. Without it on LD_LIBRARY_PATH, the InfoView falls
          # back to printing the SVG tree as text.
          pkgs.resvg
        ];

        # Link-time libs — go on `LIBRARY_PATH` so `clang -l<x>` resolves
        # `lib<x>.{so,a}` during `lake exe` compilation. Lean's codegen
        # emits `-lc++ -lc++abi -lgmp -luv`; without these the build
        # fails with the classic "cannot find -lc++" cascade.
        # These are NOT exported to `LD_LIBRARY_PATH` — at runtime,
        # binaries either have RPATH baked in or use the system loader's
        # default search.
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

          # General tooling
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
              just
              kuzu
              pandoc
              # `resvg` is needed by lean.nvim's terminal-graphics feature
              # to rasterize ProofWidgets SVG output into inline kitty
              # graphics-protocol images. Without it on PATH, lean.nvim
              # falls back to text-serializing the SVG tree.
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
        packages = {
          ci = pkgs.writeShellApplication {
            name = "ci";
            runtimeInputs = deps.ci;
            text = /* bash */ ''
              just ci
            '';
          };
        };

        devShells = {
          # Single combined dev shell. `nix develop --impure` (impure
          # required for the venvShellHook + pip flow that writes ./.venv
          # outside the nix store). Contains the Nix-built Lean toolchain
          # (pkgsLean.lean), elan (only so `lake` can update
          # lake-manifest.json -- the actual `lean` binary on PATH is the
          # Nix one), Python venv setup, and all general tooling.
          default = pkgsLean.mkShell {
            name = "giyf dev shell";
            venvDir = "./.venv";
            nativeBuildInputs = [ ];
            buildInputs = ci_deps;
            packages = dev_deps ++ [
              pkgsLean.lean
              pkgs.elan
              pkgs.git
              pkgs.just
            ];

            shellHook = /* bash */ ''
              # Prepend our Nix-built Lean toolchain so it wins over any
              # `lean`/`lake` shims inherited from the outer shell (e.g.
              # nixpkgs' `lean4-elan-stub` shipped via some neovim envs,
              # which has a broken self-reference resolution that causes
              # `exec` to loop and burn CPU).
              export PATH="${pkgsLean.lean}/bin:$PATH"

              # Workaround for nixpkgs #409490: `lake build` fails with the
              # default gcc linker on NixOS. Switch to clang.
              export LEAN_CC=clang

              SOURCE_DATE_EPOCH=$(date +%s)
              VENV=.venv

              if test ! -d $VENV; then
                python -m venv $VENV
              fi
              source ./$VENV/bin/activate
              export PYTHONPATH=`pwd`/$VENV/${pkgs.python3.sitePackages}/:$PYTHONPATH
              pip install -r requirements.txt

              # Runtime libs (e.g. libstdc++) on `LD_LIBRARY_PATH` so
              # dlopen-at-import-time wheels like `kuzu` find them.
              # MINIMAL set — keeping linker-only deps off this list
              # avoids version conflicts with other shell tools.
              export LD_LIBRARY_PATH="${pkgs.lib.makeLibraryPath runtime_deps}''${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
              # `LIBRARY_PATH` is the LINK-time counterpart — `clang -l<x>`
              # uses this to find `lib<x>.{so,a}` during `lake exe`
              # compilation. Doesn't affect runtime dlopen behavior.
              export LIBRARY_PATH="${pkgs.lib.makeLibraryPath (runtime_deps ++ linker_deps)}''${LIBRARY_PATH:+:$LIBRARY_PATH}"
            '';
          };
        };
      };
    };
}
