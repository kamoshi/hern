{
  description = "Hern – a statically-typed functional language (compiler + LSP)";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    crane.url = "github:ipetkov/crane";
    fenix = {
      url = "github:nix-community/fenix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs =
    {
      self,
      nixpkgs,
      crane,
      fenix,
      flake-utils,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs { inherit system; };
        pkgsUnsupported = import nixpkgs {
          inherit system;
          config.allowUnsupportedSystem = true;
        };
        inherit (pkgs) lib;

        # ── Source filtering ────────────────────────────────────────────
        # Include Cargo sources + std/ (embedded via include_str! at compile time).
        craneLibForFilter = crane.mkLib pkgs;
        src = lib.cleanSourceWith {
          src = ./.;
          filter =
            path: type:
            (lib.hasInfix "/std/" path)
            || (lib.hasInfix "/tests/" path)
            || (craneLibForFilter.filterCargoSources path type);
        };

        # ── Native toolchain ───────────────────────────────────────────
        nativeToolchain = fenix.packages.${system}.stable.withComponents [
          "cargo"
          "rustc"
          "rust-std"
          "clippy"
          "rustfmt"
        ];
        nativeCrane = (crane.mkLib pkgs).overrideToolchain nativeToolchain;

        commonArgs = {
          inherit src;
          pname = "hern-workspace";
          version = "0.1.0";
          cargoExtraArgs = "--workspace";
        };

        nativeArtifacts = nativeCrane.buildDepsOnly commonArgs;

        # ── Cross-compilation helper ───────────────────────────────────
        mkCross =
          {
            rustTarget,
            depsBuildBuild ? [ ],
            extraEnv ? { },
          }:
          let
            toolchain = fenix.packages.${system}.combine [
              fenix.packages.${system}.stable.cargo
              fenix.packages.${system}.stable.rustc
              fenix.packages.${system}.targets.${rustTarget}.stable.rust-std
            ];
            crossCrane = (crane.mkLib pkgs).overrideToolchain toolchain;
            baseArgs =
              commonArgs
              // {
                CARGO_BUILD_TARGET = rustTarget;
                HOST_CC = "${pkgs.stdenv.cc.nativePrefix}cc";
                doCheck = false;
                inherit depsBuildBuild;
              }
              // extraEnv;
            crossArtifacts = crossCrane.buildDepsOnly baseArgs;
          in
          {
            hern = crossCrane.buildPackage (
              baseArgs
              // {
                cargoArtifacts = crossArtifacts;
                cargoExtraArgs = "--package hern";
                postInstall = ''
                  for f in "$out/bin/"*; do
                    base="$(basename "$f")"
                    name="''${base%%.*}"
                    ext="''${base#"$name"}"
                    mv "$f" "$out/bin/$name.${rustTarget}$ext"
                  done
                '';
              }
            );
            hern-lsp = crossCrane.buildPackage (
              baseArgs
              // {
                cargoArtifacts = crossArtifacts;
                cargoExtraArgs = "--package hern-lsp";
                postInstall = ''
                  for f in "$out/bin/"*; do
                    base="$(basename "$f")"
                    name="''${base%%.*}"
                    ext="''${base#"$name"}"
                    mv "$f" "$out/bin/$name.${rustTarget}$ext"
                  done
                '';
              }
            );
          };

        # ── Per-target cross builds ────────────────────────────────────
        # LuaJIT (vendored via mlua) redirects fopen → fopen64 etc. on
        # __linux__; musl doesn't provide the *64 symbols.
        muslCflags = builtins.concatStringsSep " " [
          "-Dfopen64=fopen"
          "-Dfseeko64=fseeko"
          "-Dftello64=ftello"
          "-Dtmpfile64=tmpfile"
          "-Dmkstemp64=mkstemp"
          "-Dmmap64=mmap"
          "-U_FORTIFY_SOURCE"
        ];

        x86_64-linux = mkCross {
          rustTarget = "x86_64-unknown-linux-musl";
          depsBuildBuild = [ pkgs.pkgsCross.musl64.stdenv.cc ];
          extraEnv.CARGO_TARGET_X86_64_UNKNOWN_LINUX_MUSL_LINKER = "${pkgs.pkgsCross.musl64.stdenv.cc.targetPrefix}cc";
          extraEnv.CC_x86_64_unknown_linux_musl = "${pkgs.pkgsCross.musl64.stdenv.cc.targetPrefix}cc";
          extraEnv.AR_x86_64_unknown_linux_musl = "${pkgs.pkgsCross.musl64.stdenv.cc.targetPrefix}ar";
          extraEnv.CFLAGS_x86_64_unknown_linux_musl = muslCflags;
        };

        x86_64-windows = mkCross {
          rustTarget = "x86_64-pc-windows-gnu";
          depsBuildBuild = [ pkgs.pkgsCross.mingwW64.stdenv.cc ];
          extraEnv.CARGO_TARGET_X86_64_PC_WINDOWS_GNU_LINKER = "${pkgs.pkgsCross.mingwW64.stdenv.cc.targetPrefix}cc";
          extraEnv.CC_x86_64_pc_windows_gnu = "${pkgs.pkgsCross.mingwW64.stdenv.cc.targetPrefix}cc";
          extraEnv.AR_x86_64_pc_windows_gnu = "${pkgs.pkgsCross.mingwW64.stdenv.cc.targetPrefix}ar";
          extraEnv.CARGO_TARGET_X86_64_PC_WINDOWS_GNU_RUSTFLAGS = "-L ${pkgsUnsupported.pkgsCross.mingwW64.windows.pthreads}/lib";
        };

      in
      {
        # ── Packages ─────────────────────────────────────────────────────
        packages = {
          # Native (host) builds
          hern = nativeCrane.buildPackage (
            commonArgs
            // {
              cargoArtifacts = nativeArtifacts;
              cargoExtraArgs = "--package hern";
            }
          );
          hern-lsp = nativeCrane.buildPackage (
            commonArgs
            // {
              cargoArtifacts = nativeArtifacts;
              cargoExtraArgs = "--package hern-lsp";
            }
          );
          default = self.packages.${system}.hern;

          # Cross: Linux (static musl)
          hern-x86_64-linux = x86_64-linux.hern;
          hern-lsp-x86_64-linux = x86_64-linux.hern-lsp;

          # Cross: Windows
          hern-x86_64-windows = x86_64-windows.hern;
          hern-lsp-x86_64-windows = x86_64-windows.hern-lsp;
        };

        # ── Checks ───────────────────────────────────────────────────────
        checks = {
          workspace-clippy = nativeCrane.cargoClippy (
            commonArgs
            // {
              cargoArtifacts = nativeArtifacts;
              cargoClippyExtraArgs = "--all-targets -- --deny warnings";
            }
          );
          workspace-test = nativeCrane.cargoTest (
            commonArgs
            // {
              cargoArtifacts = nativeArtifacts;
            }
          );
          workspace-fmt = nativeCrane.cargoFmt { inherit src; };
        };

        # ── Dev shell ────────────────────────────────────────────────────
        devShells.default = nativeCrane.devShell {
          checks = self.checks.${system};
          packages = [ pkgs.rust-analyzer ];
        };
      }
    );
}
