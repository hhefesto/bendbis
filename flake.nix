{
  description = "bendbis: Bend implemented in Bend, a port of upstream Bend's bend2 checked against upstream bend";

  # ana's nixpkgs (its flake.lock, 2026-11): the same nixpkgs builds the same
  # Lean v4.34.0, so nix/lean4.nix is a store path delfos and olimpo have.
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/0bb7ec54c8483066ec9d7720e780a5caa71f8612";
  # Upstream Bend, the oracle, at the commit bendbis is gated against
  # (bendlang/bend 0e2f38f7, 2026-11-18). Its own flake packages a release
  # archive (2.0.40 at this commit), whose bendtt.lean is not this commit's,
  # so bendbis takes the sources and runs bend2/main.ts under bun, as the
  # gates' bend-head does.
  inputs.bend-src = {
    url = "github:bendlang/bend/0e2f38f759cc830849e489307f3d256a7d148288";
    flake = false;
  };

  outputs =
    { self, nixpkgs, bend-src }:
    let
      systems = [
        "x86_64-linux"
        "aarch64-linux"
      ];
      forAllSystems = f: nixpkgs.lib.genAttrs systems (system: f (import nixpkgs { inherit system; }));
      # Lean v4.34.0, the one release `bend --verdict` accepts (bend2/safe.ts
      # LEAN_VERSION); nixpkgs never shipped it, so it builds from source
      leanFor = pkgs: pkgs.callPackage ./nix/lean4.nix { };
      # BendTT, the kernel `bend --verdict` checks a book with: the pinned
      # commit's bend2/bendtt.lean, built as bend2/safe.ts kernel_bin builds
      # it (lean -c, then leanc -O3 -DNDEBUG), once, in the store. bend takes
      # it from $BENDTT and builds nothing in ~/.bend.
      bendttFor =
        pkgs:
        pkgs.runCommandCC "bendtt" { nativeBuildInputs = [ (leanFor pkgs) ]; } ''
          export HOME=$TMPDIR LEAN_CC=${pkgs.stdenv.cc}/bin/cc
          cp ${bend-src}/bend2/bendtt.lean .
          lean -c bendtt.c bendtt.lean
          leanc -O3 -DNDEBUG bendtt.c -o bendtt
          install -Dm755 bendtt $out/bin/bendtt
        '';
      # upstream bend at the pinned commit, from its sources: clang on PATH
      # (bend -o needs clang 14+), telemetry off (main.ts's daily version
      # check), bun's stack as the gates run it, and $BENDTT unless set
      bendFor =
        pkgs:
        pkgs.writeShellScriptBin "bend" ''
          export BEND_NO_TELEMETRY=1 BUN_JSC_maxPerThreadStackUsage=33554432
          export BENDTT="''${BENDTT:-${bendttFor pkgs}/bin/bendtt}"
          export PATH=${pkgs.clang}/bin:$PATH
          exec ${pkgs.bun}/bin/bun ${bend-src}/bend2/main.ts "$@"
        '';
    in
    {
      packages = forAllSystems (pkgs: {
        bend = bendFor pkgs;
        lean4 = leanFor pkgs;
        bendtt = bendttFor pkgs;
        default = bendFor pkgs;
      });

      # `nix develop`: bend (upstream, the pinned commit) with $BENDTT, so
      # `bend FILE --verdict` works, and Lean v4.34.0 itself (lean, lake,
      # leanc). Nothing goes in ~/.elan or ~/.bend/bendtt.
      devShells = forAllSystems (pkgs: {
        default = pkgs.mkShell {
          packages = [
            (bendFor pkgs)
            (leanFor pkgs)
          ];
          BENDTT = "${bendttFor pkgs}/bin/bendtt";
        };
      });
    };
}
