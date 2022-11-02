次のような記述から SDST を構成したい。

```smtlib
;; defop -- define operator
;; 引数は整数が先で、最後は必ず入力リスト。
;;      シグネチャ   定義
(defop (take n l) (t nil n l)
  ;; 補助関数の引数の種類のリスト
  ;; acc   - 蓄積 (accumulator) であり、SDST のリスト変数に対応する
  ;; param - 整数パラメタ
  ;; input - 入力リスト
  :aux-args acc param input
  :where ; 補助関数の定義たち
  ;; 各節の car は関数名、引数名と、入力リストについてのパターンマッチを持つ。
  ((t acc n nil) acc)    ; 入力リストが空
  ((t acc n (cons x xs)) ; 入力リストが非空
   (cond ; 整数引数に関するガードによる場合分け
    ((> n 0)  (t (++ acc (x)) (- n 1) xs)) 
    ;; ↑ (x) は関数呼び出しでなくシングルトンリストを意図している
    ((<= n 0) nil))))

(defop (take l) (r nil l) :aux-args acc input
  :where
  ((r acc nil) acc)
  ((r acc (cons x xs)) (r (cons x acc) xs)))

;; 複数の補助関数が必要になる例。
;; 偶数番目だけを取ってくる。
(defop (take-even l) (te0 nil l)
  :aux-args acc input
  :where
  ((te0 acc nil)         acc)
  ((te0 acc (cons x xs)) (te1 acc xs))
  ((te1 acc nil)         acc)
  ((te1 acc (cons x xs)) (te0 (++ acc (x)) xs)))
```

- 関数定義を他のファイルからロードできる (`require`)
- 直線プログラムを定義できる (`defprog`)
- 単なる合成なら短く定義できる (`defcomp`)
- 等価性を判定できる (`equiv?!`)

```smtlib
;; 他のファイルから関数定義をロードする。
(require funcs)

;; 関数合成を定義する
;; e.g. (defcomp NAME F2 F1) のとき NAME == F2 . F1
(defcomp rev-rev reverse reverse)
;; 等価性を判定する
(equiv?! rev-rev identity)

;; 直線プログラムの定義
(defprog concat-split
  :param n   ; 整数引数に名前をつける
  :input inp ; 入力リストに名前をつける
  :inter x y ; 中間生成物に名前をつける
  :ouput z   ; 出力リストに名前をつける
  :body ; 定義本体
  (:= x (take n inp))
  (:= y (drop n inp))
  (:= z (++ x y)))
;; ↑ 気持ちとしては concat-split :: (n: Int) -> [a] -> [a]
(equiv?! concat-split identity)

;; 入力列の長さに制限をかける例
(defcomp rev-to reverse take-odd)
(defcomp to-rev take-odd reverse)
(equiv?! rev-to to-rev :assuming (= (% length 2) 1))
;; ↑ length は入力列の長さを表す特別な記号

;; 途中で入力列の長さにアクセスする例
(defprog take-length
  :param n
  :input inp
  :output out
  :body (:= out (take (length x) inp)))
```
