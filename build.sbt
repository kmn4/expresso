name := "expresso"

version := "0.3.0-SNAPSHOT"

scalaVersion := "3.2.2"

libraryDependencies ++= Seq(
  "org.scalatest"              %% "scalatest"       % "3.2.14" % "test",
  "com.typesafe.scala-logging" %% "scala-logging"   % "3.9.5",
  "ch.qos.logback"              % "logback-classic" % "1.2.3",
  "com.regblanc"               %% "scala-smtlib"    % "0.2.1-42-gc68dbaa" cross CrossVersion.for3Use2_13,
  "com.monovore"               %% "decline"         % "2.2.0",
)

scalacOptions ++= Seq(
  "-encoding",
  "utf8",
  // "-Xfatal-warnings",
  "-deprecation",
  "-feature",
  "-unchecked",
  // "-Xlint",
  // "Wdead-code",
  "-language:implicitConversions"
)

Compile / console / scalacOptions --= Seq(
  "-Xlint",
  "-Xfatal-warnings"
)

fork in run          := true
fork in Test         := true
cancelable in Global := true

assembly / test      := {}
assembly / mainClass := Some("com.github.kmn4.expresso.machine.Eqlisp")

run / javaOptions += "-Xss8m"
