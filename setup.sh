#!/bin/bash -x
oldpwd="$(pwd)"
script_dir="$(dirname "${BASH_SOURCE[0]}")"
cd "${script_dir}"

scala_version=3.2.2
case "$(uname)" in
    "Darwin") platform="osx-10.16"; ext="dylib";;
    "Linux") platform="glibc-2.31"; ext="so";;
    *) echo 'not supported system: $(uname)'; exit;;
esac

mkdir -p ./lib

echo "#### Z3..."
z3version=4.8.14
z3=z3-${z3version}-x64-${platform}
curl -sSLO "https://github.com/Z3Prover/z3/releases/download/z3-${z3version}/${z3}.zip"
unzip "${z3}.zip" > /dev/null
cp ${z3}/bin/libz3*.${ext} .
cp "${z3}/bin/com.microsoft.z3.jar" ./lib
echo "#### Z3 done"

read -p "try to build? (y/N)" yn; case "$yn" in [nN]*) exit;; esac
sbt assembly
read -p "try to solve one? (y/N)" yn; case "$yn" in [nN]*) exit;; esac
java -jar target/scala-${scala_version}/*.jar constraints/bench/deleteall.smt2 --strategy preimage

cd "${oldpwd}"
