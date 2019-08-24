#! /bin/sh

if [ $# -eq 1 -a "$1" = "-x" ]; then
    CMD="sbt"
else
    echo "Showing commands that would be executed. Use -x to run."
    CMD="echo sbt"
fi

COMPILER_VERSIONS="2.11.0 2.11.1 2.11.2 2.11.4 2.11.5 2.11.6 2.11.7 2.11.8 2.11.11 2.11.12 2.12.1 2.12.2 2.12.3 2.12.4 2.12.5 2.12.6 2.12.7 2.12.8 2.13.0"
BIN_VERSIONS="2.11.12 2.12.8 2.13.0"
JVM_BIN_VERSIONS="2.11.12 2.12.8"
SBT_VERSION="2.12.8"

COMPILER="compiler jUnitPlugin"
LIBS="library irJS loggingJS linkerJS testInterface testBridge jUnitRuntime"
JVM_LIBS="ir logging linker jsEnvs jsEnvsTestKit nodeJSEnv testAdapter"

# Publish compiler
for v in $COMPILER_VERSIONS; do
    ARGS="++$v"
    for p in $COMPILER; do
        ARGS="$ARGS $p/publishSigned"
    done
    $CMD $ARGS
done

# Publish libraries
for v in $BIN_VERSIONS; do
    ARGS="++$v"
    for p in $LIBS; do
        ARGS="$ARGS $p/publishSigned"
    done
    $CMD $ARGS
done

# Publish JVM libraries
for v in $JVM_BIN_VERSIONS; do
    ARGS="++$v"
    for p in $JVM_LIBS; do
        ARGS="$ARGS $p/publishSigned"
    done
    $CMD $ARGS
done

# Publish sbt-plugin
$CMD "++$SBT_VERSION" sbtPlugin/publishSigned"
