# Eqlisp

単純なストリーミングデータ文字列トランスデューサに基づく、リスト操作プログラムの等価性判定器。

1. `./setup.sh`
1. `sbt assembly`

`java -jar target/scala-XXX/expresso-assembly-YYY.jar -h`

```
Usage: eqlisp [--logging-with-time] [--print-machine-summary] [<script file>...]

decide equivalence of list programs

Options and flags:
    --help
        Display this help text.
    --logging-with-time
        prepend local time string to each line of output
    --print-machine-summary
        print size of state sets and transition sets
```

`java -jar target/scala-XXX/expresso-assembly-YYY.jar ./eqlisp/{funcs,progs,script_01}.eql`

```
defop take
defop drop
defop identity
defop take-even
defop reverse
defop swap
defprog concat-split
defprog identity
defprog te-rev
defprog rev-te
defprog drop-drop
defprog drop-sum
defprog drop-reverse
defprog reverse-take
defprog take-all
defprog concat-split
defprog identity
equivalent
()
```
