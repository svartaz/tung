class Tung < Formula
  desc "Dependently typed functional language with checked proofs"
  homepage "https://github.com/svartaz/tung"
  url "https://github.com/svartaz/tung.git",
      revision: "b63b57a1afca95e89a81e37b5e61247d21c5c882"
  version "0.1.0.0"
  license "LGPL-3.0-or-later"

  head "https://github.com/svartaz/tung.git", branch: "main"

  depends_on "cabal-install" => :build
  depends_on "ghc@9.12" => :build

  def fetch
    ENV.prepend_path "PATH", formula_opt_bin("ghc@9.12")

    cd "tongue" do
      system "cabal", "v2-update"
      system "cabal", "v2-build", "exe:tung", "--only-download"
    end
  end

  def install
    ENV.prepend_path "PATH", formula_opt_bin("ghc@9.12")

    cd "tongue" do
      system "cabal", "v2-build", "exe:tung", "--offline", "--jobs=#{ENV.make_jobs}"
      bin.install Utils.safe_popen_read("cabal", "list-bin", "exe:tung").strip
    end
  end

  test do
    source = "let identity: [@α: *, value: α, α] ≔ value\n"
    assert_equal "type ok", pipe_output("#{bin}/tung --check-stdin", source).strip
  end
end
