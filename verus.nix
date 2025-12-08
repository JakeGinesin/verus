{ lib
, rustPlatform
, fetchFromGitHub
, makeBinaryWrapper
, rust-bin
, rustup
, z3
}:

let
  version = "latest";
  src = ./.;
  vargo = rustPlatform.buildRustPackage (finalAttrs: {
    pname = "vargo";
    inherit version src;

    # sourceRoot = "./tools/vargo";
    buildAndTestSubdir = "tools/vargo";
    # src = ./tools/vargo;
    cargoLock = {
      lockFile = ./tools/vargo/Cargo.lock;
    };
    postPatch = ''
    cp ${./tools/vargo/Cargo.lock} Cargo.lock
    cp rust-toolchain.toml source/
      '';
    # cargoLock = {
      # lockFile = ./source/Cargo.lock;     
      # # outputHashes = {
        # # "getopts-0.2.21" = "sha256-N/QJvyOmLoU5TabrXi8i0a5s23ldeupmBUzP8waVOiU=";
        # # "smt2parser-0.6.1" = "sha256-AKBq8Ph8D2ucyaBpmDtOypwYie12xVl4gLRxttv5Ods=";
      # # };
    # };

    cargoHash = "sha256-0WJEW3FtoWxMaedqBoCmaS0HLsLjxtBlBClAXcjf/6s=";
    # cargoHash = "";

    meta = meta // { mainProgram = "vargo"; };
  });
  meta = {
    homepage = "https://github.com/verus-lang/verus";
    description = "Verified Rust for low-level systems code";
    license = lib.licenses.mit;
    maintainers = with lib.maintainers; [ stephen-huan ];
    platforms = [
      "x86_64-linux"
      "x86_64-darwin"
      "aarch64-darwin"
      "x86_64-windows"
    ];
  };
in
rustPlatform.buildRustPackage {
  pname = "verus";
  inherit version src;

  # sourceRoot = "source/source";
  # sourceRoot = "source";

  buildAndTestSubdir = "source";
  # cargoLock = {
    # lockFile = ./source/Cargo.lock;
  # };
  cargoLock = {
    lockFile = ./source/Cargo.lock;
    outputHashes = {
      "getopts-0.2.21" = "sha256-N/QJvyOmLoU5TabrXi8i0a5s23ldeupmBUzP8waVOiU=";
      "smt2parser-0.6.1" = "sha256-AKBq8Ph8D2ucyaBpmDtOypwYie12xVl4gLRxttv5Ods=";
    };
  };

  postPatch = ''
    cp ${./source/Cargo.lock} Cargo.lock
    '';

  cargoHash = "sha256-y3SmOo6pCfJfPNN+9yUN7FeFcrmJ8xL4rQrjqtSe96M=";

  nativeBuildInputs = [ makeBinaryWrapper rust-bin rustup vargo z3 ];

  buildInputs = [ rustup z3 ];

  buildPhase = ''
    runHook preBuild
    cd source


    ln -s ${lib.getExe z3} ./z3
    ln -sf ../rust-toolchain.toml rust-toolchain.toml
    vargo build --release

    runHook postBuild
  '';

  installPhase = ''
    runHook preInstall

    mkdir -p $out
    cp -r target-verus/release -T $out

    mkdir -p $out/bin
    ln -s $out/verus $out/bin/verus
    ln -s $out/rust_verify $out/bin/rust_verify
    ln -s $out/cargo-verus $out/bin/cargo-verus
    ln -s $out/z3 $out/bin/z3

    # wrapProgram $out/bin/verus --prefix PATH : ${lib.makeBinPath [ rustup ]}
    wrapProgram $out/bin/verus --prefix PATH : ${lib.makeBinPath [ rustup rust-bin z3 ]}

    runHook postInstall
  '';

  # no tests, verified when built
  doCheck = false;

  passthru = { inherit vargo; };

  meta = meta // { mainProgram = "verus"; };
}
