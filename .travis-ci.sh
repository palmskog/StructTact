pushd ..
wget 'http://homes.cs.washington.edu/~jrw12/coq-8.5-build-local.tgz'
tar xf coq-8.5-build-local.tgz
export PATH=$PWD/coq-8.5/bin:$PATH
popd

if [ -z "$DOWNSTREAM" ]; then
    ./build.sh
else
    BUILD_CMD="${BUILD_CMD:-bash -ex ./.travis-ci.sh}"
    pushd ..
    git clone $DOWNSTREAM downstream
    cd downstream
    $BUILD_CMD
fi
