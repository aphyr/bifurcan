(ns bifurcan.immutable-test
  "This test generates ASTs for simple programs involving sets (later maps
  etc.) and evaluates them both as Clojure and forked Bifurcan structures,
  testing that they are equivalent. This is already handled by collection-test,
  but we *also* check that the intermediate collections are left unchanged as
  we combine them in various ways. For example, this test can show that if you
  take a set and union it with another, that union function actually alters its
  arguments."
  (:refer-clojure :exclude [eval])
  (:require [bifurcan.test-utils :as u :refer [iterations]]
            [clojure [datafy :refer [datafy]]
                     [pprint :refer [pprint]]
                     [set :as set]
                     [test :refer [deftest is are]]]

            [clojure.test.check [generators :as gen]
                                [properties :as prop]
                                [clojure-test :as ct :refer [defspec]]]
            [com.gfredericks.test.chuck.clojure-test :refer [checking]])
  (:import (java.util HashMap
                      HashSet
                      ArrayList
                      ArrayDeque
                      Collection)
           (io.lacuna.bifurcan.utils Encodings
                                     BitVector
                                     Bits
                                     Iterators)
           (io.lacuna.bifurcan.nodes ListNodes$Node)
           (io.lacuna.bifurcan ICollection
                               IntMap
                               IntSet
                               FloatMap
                               SortedMap
                               Map
                               Maps
                               List
                               Lists
                               Set
                               Sets
                               IMap
                               IEntry
                               IList
                               ISet
                               LinearList
                               LinearMap
                               LinearSet
                               SortedSet)))

(def max-program-size
  "How long can programs be? This generator is very bad at shrinking, so when
  debugging you probably want to lower this."
  64)

(def max-basic-size
  "How many elements can we put in a basic collection, like Set.of(1,2,3...)?"
  ; TODO: you should raise this when it starts passing; this is just to get
  ; minimal examples
  8)

(def value-gen
  "Generator of basic values."
  gen/large-integer)

(defn fallback-expr
  "We use these to generate expressions of a given type when rewrite-var
  fails."
  [type]
  (case type
    :list :list/empty
    :set  :set/empty
    :map  :map/empty))

(defn expr-type
  "Given an expression, and optionally a program, returns the type of an
  expression in it. For instance, :set/empty is a :set, as is [:set/union]. The
  type of [:var 2] is the type of the third expression in the program."
  ([expr]
   (expr-type expr []))
  ([expr program]
   (if (vector? expr)
     (case (first expr)
       (:list/of
        :list/add-first
        :list/add-last
        :list/remove-first
        :list/remove-last
        :list/set
        :list/slice
        :list/concat)
       :list

       (:map/of
        :map/put
        :map/union
        :map/intersection
        :map/difference)
       :map

       (:set/of
         :set/add
         :set/remove
         :set/union
         :set/intersection
         :set/difference)
       :set

       :var
       (recur (nth program (second expr)) program))

     (case expr
       :list/empty :list
       :map/empty  :map
       :set/empty  :set))))

(defn var-gen
  "Generator of [:var 2 type] expressions. We just pick random numbers, and
  rewrite them later to refer to previous elements of the correct type, based
  on the program."
  [type]
  (gen/fmap (fn [x]
              [:var x type])
            gen/nat))

(defn or-var
  "Wraps a generator in one that emits variables of the given type."
  [type gen]
  (gen/one-of [gen (var-gen type)]))

(def basic-list-gen
  "Generators of basic list expressions."
  (gen/one-of
    [(gen/return :list/empty)
     (gen/fmap (fn [elements] (into [:list/of] elements))
               (gen/vector value-gen 1 max-basic-size))]))

(def basic-set-gen
  "Generators of basic set expressions."
  (gen/one-of
    [; Empty set
     (gen/return :set/empty)
     ; [:set/of 1 2 3]
     (gen/fmap (fn [elements]
                 (into [:set/of] elements))
               (gen/vector value-gen 1 max-basic-size))]))

(def basic-map-gen
  "Generator of basic map expressions."
  (gen/one-of
    [(gen/return :map/empty)
     (gen/fmap (fn [pairs]
                 (into [:map/of] (mapcat identity pairs)))
               (gen/vector (gen/tuple value-gen value-gen)
                           1 max-basic-size))]))

(def basic-list-gen+ (or-var :list basic-list-gen))
(def basic-set-gen+ (or-var :set basic-set-gen))
(def basic-map-gen+ (or-var :map basic-map-gen))

(def composite-list-gen
  "Generators of composite list expressions like [:list/add [:var 0] 5]"
  (gen/one-of
    [(gen/tuple (gen/elements [:list/add-first :list/add-last])
                basic-list-gen+
                value-gen)
     (gen/tuple (gen/elements [:list/remove-first :list/remove-last])
                basic-list-gen+)
     (gen/tuple (gen/elements [:list/concat])
                basic-list-gen+
                basic-list-gen+)
     #_(gen/tuple (gen/return :list/slice)
                basic-list-gen+
                gen/nat
                gen/nat)]))

(def composite-set-gen
  "Generators of composite set expressions like [:set/add [:var 2] 3]"
  (gen/one-of
    [(gen/tuple (gen/elements [:set/add
                               :set/remove])
                basic-set-gen+
                value-gen)
     (gen/tuple (gen/elements [:set/union
                               :set/intersection
                               :set/difference])
                basic-set-gen+
                basic-set-gen+)]))

(def composite-map-gen
  "Generators of composite map expressions like [:map/union [:var 2]
  :map/empty]"
  (gen/one-of
    [(gen/tuple (gen/return :map/put)
                basic-map-gen+
                value-gen
                value-gen)
     (gen/tuple (gen/elements [:map/union
                               :map/intersection])
                basic-map-gen+
                basic-map-gen+)
     (gen/tuple (gen/return :map/difference)
                basic-map-gen+
                basic-set-gen+)]))

(defn expr-gen
  "Generator of expressions of the given types."
  [types]
  (->> types
       (mapcat {:list [basic-list-gen composite-list-gen]
                :set [basic-set-gen composite-set-gen]
                :map [basic-map-gen composite-map-gen]})
       vec
       gen/one-of))

(defn rewrite-var*
  "Given an index of types to vectors of available expression indices, and a
  var expression like [:var 2 :set], returns a var expression like [:var 5],
  where that variable is a set defined before index. If no var of that type is
  available, uses a fallback expression."
  [by-type [_ i type]]
  (let [; What indices in the program are of the right type?
        indices (get by-type type [])
        n (count indices)]
    (if (zero? n)
      (fallback-expr type)
      [:var (nth indices (mod i n))])))

(defn rewrite-var
  "Like rewrite-var*, but rewrites expressions recursively."
  [by-type expr]
  (cond (not (vector? expr))
        expr

        ; Found it
        (identical? :var (first expr))
        (rewrite-var* by-type expr)

        ; Recur
        true
        (into [(first expr)]
              (map (partial rewrite-var by-type) (rest expr)))))

(defn rewrite-vars
  "Runs through a program and rewrites any occurrence of [:var 2 :set] to a
  previous set expression, or the empty set."
  ([program]
   ; We step through the program line by line, rewriting expressions and
   ; resolving their types.
   (loop [i       0
          by-type {} ; A map of types to vectors of expression indices
          program program]
     (if (= i (count program))
       program
       (let [expr     (rewrite-var by-type (nth program i))
             program  (assoc program i expr)
             type     (expr-type expr program)]
         (recur (inc i)
                (update by-type type
                        (fn [indices] (conj (or indices []) i)))
                program))))))

(defn program-gen
  "A generator of abstract programs. Takes a set of types. Each program is a
  vector of operations to be performed sequentially, which evaluate to that
  type. Operations can refer to earlier operations by their index, as if they
  were all variables in a `let` binding. For example:

  [[:set/of 1 2 3]
  [:set/empty]
  [:set/union [:var 0] [:var 1]]]

  This program computes a set containing 1, 2, and 3, then an empty set, then
  takes the union of those two."
  [types]
  (gen/fmap rewrite-vars
            (gen/vector (expr-gen types) 1 max-program-size)))

(defn eval-expr-clj
  "Takes a trace of program results so far, and evaluates a new expression in
  that context."
  [trace expr]
  (if (vector? expr)
    (let [[f a b c] expr]
      (case f
        :list/of           (vec (rest expr))
        :list/add-first    (vec (cons b a))
        :list/add-last     (conj a b)
        :list/remove-first (if (seq a)
                             (subvec a 1)
                             [])
        :list/remove-last  (if (seq a)
                             (pop a)
                             [])
        :list/concat       (into a b)
        :list/slice        (subvec a b c)

        :map/of           (apply hash-map (rest expr))
        :map/put          (assoc a b c)
        :map/union        (merge a b)
        :map/intersection (select-keys a (keys b))
        :map/difference   (reduce dissoc a b)

        :set/of           (set (rest expr))
        :set/add          (conj a b)
        :set/remove       (disj a b)
        :set/union        (set/union a b)
        :set/intersection (set/intersection a b)
        :set/difference   (set/difference a b)
        :var              (:res (nth trace a))))
    (case expr
      :list/empty []
      :map/empty {}
      :set/empty #{}
      expr)))

(defn eval-expr-bifurcan
  "Takes a trace of program results so far, and evaluates a new expression in
  that context."
  [trace expr]
  (if (vector? expr)
    (let [[f a b c] expr]
      (case f
        :list/of           (List/from (rest expr))
        :list/add-first    (.addFirst a b)
        :list/add-last     (.addLast a b)
        :list/remove-first (.removeFirst a)
        :list/remove-last  (.removeLast a)
        :list/concat       (.concat a b)
        :list/slice        (.slice a b c)

        :map/of           (Map/from (apply hash-map (rest expr)))
        :map/put          (.put a b c)
        :map/union        (.union a b)
        :map/intersection (.intersection a b)
        :map/difference   (.difference a b)

        :set/of           (Set/from (rest expr))
        :set/add          (.add a b)
        :set/remove       (.remove a b)
        :set/union        (.union a b)
        :set/intersection (.intersection a b)
        :set/difference   (.difference a b)
        :var              (:res (nth trace a))))
    (case expr
      :list/empty List/EMPTY
      :map/empty Map/EMPTY
      :set/empty Set/EMPTY
      expr)))

(defn eval-recursive
  "To simplify our node evaluators, they don't recur themselves. This takes an
  evaluation function, a trace, an expression, and evaluates it
  recursively--depth first, left to right."
  [eval-expr trace expr]
  (if (vector? expr)
    ; Do args first
    (let [args-evaled (into [(first expr)]
                            (mapv (partial eval-recursive eval-expr trace)
                                  (rest expr)))]
      (eval-expr trace args-evaled))
    ; Leaf node; evaluate directly
    (eval-expr trace expr)))

(defn eval-trace
  "Evaluates a program using the given function for evaluating an expression.
  Returns a trace: a vector of results from evaluating the program in order.
  Each trace element is a map like:

      {:expr  [:union ...]
       :res    #<Set ...>
       :clj    #{...}}

  The :res is the result of evaluating the expression. :clj is a datafied
  version of result. We expect that if Bifurcan is truly immutable, at the end
  of the evaluation (datafy bifurcan) = clj. The last element in the trace is
  the result of our top-level AST eval."
  [eval-expr program]
  (reduce (fn [trace expr]
            (let [res (eval-recursive eval-expr trace expr)]
              (conj trace
                    {:expr expr
                     :res res
                     :clj (datafy res)})))
          []
          program))

(defn print-trace
  "Prints out a trace."
  [trace]
  (->> trace
       (map-indexed (fn [i {:keys [expr res clj]}]
                      (println
                        (format "%3d" i)
                        (pr-str expr)
                        "->"
                        (pr-str clj))))
       dorun))


(defn eval-check-immutable
  "Evaluates a program using the given function for evaluating an expression.
  Ensures that at the end, expressions are left unchanged from their original
  values. Returns the trace."
  ([eval-expr program]
   (let [trace (eval-trace eval-expr program)]
     ; Check the trace elements are still stable.
     (doseq [{:keys [expr res clj]} trace]
       (is (= clj (datafy res))
           (when (instance? ICollection res)
             (str
               (with-out-str (print-trace trace))
               "\n\nExpr:         " (pr-str expr)
               "\nWas:          " (pr-str clj)
               "\nNow:          " (pr-str (datafy res))
               "\nRes:          " res
               "\nSize:         " (.size res)
               "\niterator-seq: " (pr-str (mapv datafy
                                                (iterator-seq (.iterator res))))
               "\nnths:         " (mapv #(try
                                           (.nth res %)
                                           (catch IndexOutOfBoundsException e
                                             :out-of-bounds))
                                        (range 0 (inc (max (count clj)
                                                      (.size res)))))

               ))))
     trace)))

(defn eval-compare
  "Evaluates a program using both Clojure and Bifurcan evaluators, testing that
  the two yield equivalent traces."
  [program]
  (let [clj      (eval-check-immutable eval-expr-clj      program)
        bifurcan (eval-check-immutable eval-expr-bifurcan program)]
    (mapv (fn [clj bifurcan]
            (is (= (:clj clj) (:clj bifurcan))))
          clj
          bifurcan)
    {:clj clj
     :bifurcan bifurcan}))

(defmacro def-imm-test
  "Defines a new test for immutability. Takes a var name, a text description,
  the number of iterations, and a vector of types."
  [name desc iterations types]
  `(deftest ~name
     (checking ~desc ~iterations
               [program# (program-gen ~types)]
               (let [res# (eval-compare program#)]
                 ; (prn)
                 ;(print-trace (:bifurcan res#))
                 ))))

(def-imm-test list-test "Lists are immutable" iterations [:list])
(def-imm-test map-test  "Maps are immutable"  iterations [:map])
(def-imm-test set-test  "Sets are immutable"  iterations [:set])
