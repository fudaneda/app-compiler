# set env for built LLVM
export LLVM_HOME=/usr/lib/llvm-15/bin
export PATH=$LLVM_HOME:$PATH

# cmake & make
cmake -B build -G Ninja
cmake --build build
