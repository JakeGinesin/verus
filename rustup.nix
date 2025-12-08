{ lib
, stdenvNoCC
, python3
, rust-bin
}:

stdenvNoCC.mkDerivation {
  name = "rustup";
  src = ./nix;

  strictDeps = true;
  buildInputs = [ python3 ];
  preferLocalBuild = true;

  postPatch = ''
    substituteInPlace rustup.py \
      --subst-var-by rustVersion "${rust-bin}"
  '';

  installPhase = ''
    runHook preInstall

    install -Dm755 rustup.py -T $out/bin/rustup

    runHook postInstall
  '';

  meta = {
    description = "Spoof rustup";
    mainProgram = "rustup";
    maintainers = with lib.maintainers; [ stephen-huan ];
  };
}
