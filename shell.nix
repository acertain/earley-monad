{ nixpkgs ? import <nixpkgs> {}, compiler ? "ghc844", f ? import ./default.nix }:

let

  inherit (nixpkgs) pkgs;

  # jailbreak = pkgs.haskell.lib.doJailbreak;

  haskellPackages = (if compiler == "default"
                       then pkgs.haskellPackages
                       else pkgs.haskell.packages.${compiler}).override {
  overrides = self: super: with pkgs.haskell.lib; {
    ghc = super.ghc // { withPackages = super.ghc.withHoogle; };
    ghcWithPackages = self.ghc.withPackages;
    
    # unordered-containers = dontCheck super.unordered-containers;
    # charset = doJailbreak super.charset;
    
    # # cryptohash-sha256 = doJailbreak super.cryptohash-sha256;
    
    # doctest = doJailbreak super.doctest;
    # ghc-tcplugins-extra = doJailbreak super.ghc-tcplugins-extra;
    # ghc-typelits-natnormalise = dontCheck super.ghc-typelits-natnormalise;
    # hspec-core = dontCheck super.hspec-core;
    # polyparse = doJailbreak super.polyparse;
    # tasty-expected-failure = doJailbreak super.tasty-expected-failure;
    # unliftio-core = doJailbreak super.unliftio-core;
    # Glob = doJailbreak (dontCheck super.Glob);
    # megaparsec = dontCheck super.megaparsec;
    # HTTP = doJailbreak super.HTTP;

    # singletons = doJailbreak super.singletons_2_5;
    # th-expand-syns = doJailbreak super.th-expand-syns;
    # th-desugar = super.th-desugar_1_9;

    # contravariant = super.contravariant_1_5;
    # base-orphans = super.base-orphans_0_8;
    # semigroupoids = super.semigroupoids_5_3_1;

    # lens = dontCheck super.lens_4_17;

    # foldl = doJailbreak super.foldl;
    # free = doJailbreak super.free;

    # sbv = dontCheck super.sbv;

    # mkDerivation = args: super.mkDerivation (args // {
    #   # doCheck = false;
    #   #enableLibraryProfiling = true;
    #   #doCheck = false; doBenchmark = false; doCoverage = false;
    # });
    
    };};

  drv = pkgs.haskell.lib.overrideCabal (haskellPackages.callPackage f {}) (drv: rec {
    # executableHaskellDepends = [];
    buildDepends = (drv.buildDepends or []) ++ (with haskellPackages;
      [cabal-install
      #hoogle
      #ghcid
      # [hsdev cabal-install]);
  ]);});

in drv.env
  #if pkgs.lib.inNixShell then drv.env else drv
