# Usage
`java -jar JARFILE CONSTRAINT [STRATEGY]`
- CONSTRAINT は `.smt2` ファイル
- STRATEGY は `preimage` または `jssst`
    - `jssst` は JSSST2021大会予稿で示したアルゴリズム（デフォルト）
    - `preimage` は OSTRICH 風の逆像計算によるアルゴリズム

# インストール
## Docker を使う場合
```bash
docker pull kamasaki/expresso:jssst2021
```

使い方
```bash
docker run --rm -i -v $(pwd):/workdir kamasaki/expresso:jssst2021 CONSTRAINT [STRATEGY]
```

## 手動ビルド

Ubuntu 20.04 LTS と macOS Ventura でのビルドをサポートする．
なお，Windows では WSL2 により Ubuntu を利用できる．

必要なもの
- OpenJDK 11+
- sbt
- Z3 4.8.14

セットアップスクリプト ([./setup.sh](./setup.sh)) はZ3を準備してからビルドし，
成果物が実行できるか確認する（JDK と sbt は事前に準備すること）．
スクリプトは最初の一回だけ使えば良い．
あとは通常通り sbt を使える．

### [Z3](https://github.com/Z3Prover/z3)
プログラムは Z3 バージョン 4.8.14 の Java API を利用しているため，
ビルド時と実行時にそれぞれライブラリが必要．
[ここ](https://github.com/Z3Prover/z3/releases/tag/z3-4.8.14)から
環境に応じた Zip ファイルをダウンロードする．

- Z3 の `bin` ディレクトリから共有ライブラリを適切な場所にコピーする．
   + Ubuntu の場合．`libz3.so` と `libz3java.so` を `/usr/local/lib`
	 などに配置
   + macOS Big Sur の場合．`libz3.dylib` と `libz3java.dylib` を，
     `java -jar`を実行するのと同じディレクトリに配置（`/usr/local/lib`
     などに配置すると System Integrity Protection により読み込みがブロッ
     クされる）
- Z3 の `bin/com.microsoft.z3.jar` を，ビルドディレクトリの `lib/` に
  配置する．

# 制約
[./constraints](./constraints/) 以下に制約例がある．
[./constraints/bench](./constraints/bench/) の例 (の多く) は [ParikhSolverTest](./src/test/scala/ParikhSolverTest.scala) クラスから実行される．
JSSST2021大会予稿に例として取り上げた制約は以下：
- [indexof2_sat](./constraints/bench/indexof2_sat.smt2)
- [indexof2_unsat](./constraints/bench/indexof2_unsat.smt2)
- [deleteall](./constraints/bench/deleteall.smt2)
- [substr_equiv](./constraints/bench/substr_equiv.smt2)
- [inverse_sat](./constraints/bench/inverse_sat.smt2)
- [inverse_unsat](./constraints/bench/inverse_unsat.smt2)

