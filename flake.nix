{
  description = "insaturo — le spec come concetti insaturi (Frege) in Agda";

  inputs = {
    nixpkgs.url = "https://flakehub.com/f/NixOS/nixpkgs/0.2511.912939";
    piforge = {
      url   = "github:avit-io/piforge";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, nixpkgs, piforge }:
    let
      system   = "x86_64-linux";
      pkgs     = nixpkgs.legacyPackages.${system};
      stdlib28 = piforge.packages.${system}."stdlib-28";

      insaturoLib = pkgs.stdenv.mkDerivation {
        name      = "insaturo-agda-lib";
        src       = builtins.path { path = ./.; name = "insaturo-src"; };
        dontBuild = true;
        installPhase = ''
          mkdir -p $out
          cp -r Insaturo $out/
          printf 'name: insaturo\ninclude: .\ndepend: standard-library\n' \
            > $out/insaturo.agda-lib
        '';
      };

      # insaturo è una RADICE: solo standard-library. La grammatica nuda.
      copyStdlib = ''
        _cache="''${XDG_CACHE_HOME:-$HOME/.cache}/piforge"
        _stdlib="$_cache/stdlib-2.3"
        if [ ! -d "$_stdlib" ]; then
          echo "insaturo: copying stdlib 2.3 to $_stdlib (one-time setup)..." >&2
          mkdir -p "$_stdlib"
          cp -r ${stdlib28}/. "$_stdlib/"
          chmod -R u+w "$_stdlib"
        fi
      '';

      # Sentinel sul nix store path: invalida la cache quando la lib cambia.
      copyInsaturo = ''
        _insaturo="$_cache/insaturo"
        _insaturo_tag="${insaturoLib}"
        if [ ! -f "$_insaturo/.nix-tag" ] || [ "$(cat "$_insaturo/.nix-tag")" != "$_insaturo_tag" ]; then
          echo "insaturo: copying library to $_insaturo..." >&2
          rm -rf "$_insaturo"
          mkdir -p "$_insaturo"
          cp -r ${insaturoLib}/. "$_insaturo/"
          chmod -R u+w "$_insaturo"
          printf 'name: insaturo\ninclude: .\ndepend: standard-library\n' \
            > "$_insaturo/insaturo.agda-lib"
          echo "$_insaturo_tag" > "$_insaturo/.nix-tag"
        fi
      '';

    in
    {
      packages.${system} = {
        lib     = insaturoLib;
        default = insaturoLib;
      };

      # Dev shell per sviluppare insaturo: solo stdlib in AGDA_DIR.
      devShells.${system}.default = piforge.lib.agda.mkShell {
        inherit pkgs;
        version             = "v28";
        useRuntimeLibraries = true;
        extraPackages       = with pkgs; [ watchexec ];
        shellHook           = copyStdlib + ''
          mkdir -p "$_cache/insaturo-dev"
          printf '%s\n' "$_stdlib/standard-library.agda-lib" \
            > "$_cache/insaturo-dev/libraries"
          export AGDA_DIR="$_cache/insaturo-dev"
        '';
      };

      # Per i consumer: stdlib + insaturo.
      lib.mkShell = { pkgs, extraPackages ? [], shellHook ? "" }:
        piforge.lib.agda.mkShell {
          inherit pkgs;
          version             = "v28";
          useRuntimeLibraries = true;
          inherit extraPackages;
          shellHook = copyStdlib + copyInsaturo + ''
            mkdir -p "$_cache/insaturo-env"
            printf '%s\n%s\n' \
              "$_stdlib/standard-library.agda-lib" \
              "$_insaturo/insaturo.agda-lib" \
              > "$_cache/insaturo-env/libraries"
            export AGDA_DIR="$_cache/insaturo-env"
          '' + shellHook;
        };
    };
}
