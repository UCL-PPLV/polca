#!/usr/bin/env bash

export JAVA_ARGS="$@"
export MAVEN_OPTS="-ea --add-opens=java.base/java.util=ALL-UNNAMED --add-opens=java.base/java.util.reflect=ALL-UNNAMED --add-opens=java.base/java.lang=ALL-UNNAMED --add-opens=java.base/java.lang.reflect=ALL-UNNAMED"
mvn -q exec:java -e -Dexec.mainClass=net.vwzq.polca.Polca -Dexec.args="${JAVA_ARGS}"
