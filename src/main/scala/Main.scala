package com.github.kmn4.expresso

import ch.qos.logback.{classic => logback}
import com.github.kmn4.expresso.strategy.JSSST2021Strategy
import com.github.kmn4.expresso.strategy.PreImageStrategy
import com.microsoft.z3.Version
import com.typesafe.scalalogging.Logger

import java.io.File

object Main extends App {

  for {
    arguments <- ArgumentParser.parse(args)
    file <- arguments.constraintFile
    logger = Logger(s"bench.${file.getName().split('.').dropRight(1).mkString}")
    _ = arguments.loggingLevel map ArgumentParser.loggingLevels foreach
      logger.underlying.asInstanceOf[logback.Logger].setLevel
    parser = new smtlib.parser.Parser(new smtlib.lexer.Lexer(new java.io.FileReader(file)))
    script = parser.parseScript // might throw an exception
    checker = ArgumentParser.strategies(arguments.strategyName)(logger)
    // alpahbet to be added
    alphabet = {
      val Seq(from, to) = arguments.alphabet.split("-").toSeq
      (from(0) to to(0)).toSet[Char]
    }
  } {
    logger.trace(s"checker=$checker")
    logger.trace(s"logger=$logger")
    logger.trace(s"alphabet=$alphabet")
    new Solver(
      checker = checker,
      print = true,
      logger = logger,
      alphabet = alphabet
    ).executeScript(script)
  }

}

private case class Arguments(
    constraintFile: Option[java.io.File] = None,
    strategyName: String = "jssst",
    alphabet: String = "a-c", // "!-~" for all printable except whitespace
    loggingLevel: Option[String] = None
)

private object ArgumentParser {
  import scopt.OParser

  def parse(args: Array[String]): Option[Arguments] = OParser.parse(parser, args, Arguments())

  val strategies = Map(
    "jssst" -> (logger => new JSSST2021Strategy(logger)),
    "preimage" -> (logger => new PreImageStrategy(logger))
  )

  val loggingLevels = scala.collection.immutable.SeqMap(
    "all" -> logback.Level.TRACE,
    "trace" -> logback.Level.TRACE,
    "debug" -> logback.Level.DEBUG,
    "info" -> logback.Level.INFO,
    "warn" -> logback.Level.WARN,
    "error" -> logback.Level.ERROR,
    "off" -> logback.Level.OFF
  )

  private val parser = {
    val builder = OParser.builder[Arguments]
    import builder._

    OParser.sequence(
      programName("expresso"),
      head("Expresso", "SNAPSHOT", "with", Version.getFullVersion()),
      help('h', "help"),
      version('v', "version"),
      arg[File]("<constraint file>")
        .action((file, args) => args.copy(constraintFile = Some(file)))
        .validate(file => if (file.isFile()) success else failure(s"<constraint file> $file does not exist"))
        .text("name of a constraint file to be solved"),
      arg[String]("<strategy>")
        .optional()
        .action((name, args) => args.copy(strategyName = name))
        .validate(name =>
          if (strategies.keySet.contains(name)) success
          else failure("<strategy> must be either \"preimage\" or \"jssst\"")
        )
        .text("either \"preimage\" or \"jssst\""), //
      {
        val keys = loggingLevels.keys
        val msg = s"one of ${keys.init.mkString(", ")}, or ${keys.last}"
        val keySet = keys.toSet
        opt[String]("logging-level")
          .action((level, args) => args.copy(loggingLevel = Some(level)))
          .validate(level => if (keySet contains level) success else failure(s"invalid level: $level"))
          .text(msg)
      },
      opt[String]("alphabet")
        .action((value, args) => args.copy(alphabet = value))
        .validate(value =>
          value.split("-").toSeq match {
            case Seq(from, to) if from.length() == 1 && to.length() == 1 => success
            case _                                                       => failure(s"argument to --alphabet must be in the form <char>-<char>")
          }
        )
        .text("alphabet to be considered additionally to those contained in a given constraint")
    )
  }

}
