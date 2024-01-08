ThisBuild / scalaVersion := "3.3.0"

lazy val root = project
  .in(file("."))
  .enablePlugins(StainlessPlugin)
  .settings(
    name             := "lang",
    stainlessEnabled := false
  )

libraryDependencies ++= Seq(
  "org.scalatest" %% "scalatest" % "3.2.17" % Test
)
