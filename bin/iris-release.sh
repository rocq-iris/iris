#!/usr/bin/env bash

# iris-release.sh prepares a commit for https://github.com/rocq-prover/opam to
# add a new version of std++ and Iris to the Rocq opam repository.
#
# Requires a clone of opam-rocq-archive. The opam files from std++ and Iris are
# retrieved by downloading their releases by tag.

set -eu

usage() {
  echo "Usage: $0 [--opam-rocq-archive PATH] [--stdpp VERSION] [--iris VERSION]" 1>&2
  echo 1>&2
  echo "--opam-rocq-archive should point to a clone of https://github.com/rocq-prover/opam" 1>&2
}

opam_rocq_archive_path=""
stdpp_version=""
iris_version=""
orig_path="$PWD"

while [[ "$#" -gt 0 ]]; do
  case "$1" in
  --opam-rocq-archive)
    shift
    opam_rocq_archive_path="$1"
    shift
    ;;
  --stdpp)
    shift
    stdpp_version="$1"
    shift
    ;;
  --iris)
    shift
    iris_version="$1"
    shift
    ;;
  -help | --help)
    usage
    exit 0
    ;;
  -*)
    echo "error: unexpected flag $1" 2>&1
    usage
    exit 1
    ;;
  *)
    break
    ;;
  esac
done

# We rely on GNU sed flags. On macOS try to use gsed hoping the user has
# installed it with brew install gnu-sed.
SED="sed"
# try to use GNU sed
if command -v gsed &>/dev/null; then
  SED="gsed"
fi
if ! "$SED" --version >/dev/null 2>&1; then
  echo "could not find GNU sed" 1>&2
  exit 1
fi

TAR="tar"
# if tar is GNU tar, we need --wildcards
# BSD tar interprets patterns with wildcards by default and has no such option
if "$TAR" --version | grep "GNU tar" >/dev/null 2>&1; then
  TAR="$TAR --wildcards"
fi

if [ -z "$opam_rocq_archive_path" ] || [ -z "$stdpp_version" ] ||
  [ -z "$iris_version" ]; then
  echo "error: arguments are all required" 1>&2
  usage
  exit 1
fi

cd "$opam_rocq_archive_path"
git checkout master 1>/dev/null 2>&1
git pull 1>/dev/null

## these functions use $pkg, $version, and $tarfile as global variables

set_pkg() {
  export pkg="rocq-$1"
  export version="$2"

  cd "$orig_path"
  cd "$opam_rocq_archive_path/released/packages"
  mkdir -p "$pkg/$pkg.$version"
  cd "$pkg/$pkg.$version"
}

download_tarball() {
  export url="$1"
  export tarfile="$pkg-$version.tar.gz"
  if ! wget -q -O "$tarfile" "$url"; then
    echo "Error: failed to download $url" >&2
    rm -f "$tarfile"
    return 1
  fi
  checksum=$(sha512sum "$tarfile" | awk '{ print $1 }')
  export checksum
  tarfile="$PWD/$tarfile"
}

extract_opam() {
  echo "extract opam $pkg.opam version $version"
  # */$pkg.opam is a pattern to extract
  # it is interpreted as a wildcard due to the setup of $TAR (which handles BSD
  # tar vs GNU tar differences)
  $TAR -O -xf "$tarfile" "*/$pkg.opam" >opam

  ## these changes are always needed
  # delete version line
  "$SED" -i '/^version:/d' opam
  # add today's date as a tag
  local date
  date="$(date +'%Y-%m-%d')"
  # need an escape to insert a literal space to the beginning of the line
  "$SED" -i "/^tags:/a \  \"date:$date\"" opam

  echo "
url {
  src:
    \"$url\"
  checksum:
    \"sha512=$checksum\"
}" >>opam
}

set_stdpp_dep() {
  local stdpp_dep="(= \"$stdpp_version\") | (= \"dev\")"
  "$SED" -E -i "/rocq-stdpp/s/\{ .* \}/{ $stdpp_dep }/" opam
}

delete_tarball() {
  rm "$tarfile"
}

set_pkg stdpp "$stdpp_version"
download_tarball "https://gitlab.mpi-sws.org/iris/stdpp/-/archive/stdpp-$version.tar.gz"
extract_opam

set_pkg stdpp-bitvector "$stdpp_version"
extract_opam
delete_tarball

set_pkg iris "$iris_version"
download_tarball "https://gitlab.mpi-sws.org/iris/iris/-/archive/iris-$version.tar.gz"
extract_opam
set_stdpp_dep

set_pkg iris-heap-lang "$iris_version"
extract_opam
delete_tarball

echo "# Run the following in your clone of rocq-prover/opam (at $opam_rocq_archive_path):"
echo
echo "git checkout -b iris-$iris_version"
echo "git add ."
echo "git commit -m \"Release Iris $iris_version and std++ $stdpp_version\""
