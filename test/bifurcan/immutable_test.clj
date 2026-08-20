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

(def max-basic-size
  "How many elements can we put in a basic collection, like Set.of(1,2,3...)?"
  ; TODO: you should raise this when it starts passing; this is just to get
  ; minimal examples
  8)

(def value-gen
  "Generator of basic values."
  gen/large-integer)

(def set-basic-gen
  "Generator of basic sets AST"
  (gen/one-of [(gen/return :set/empty)
               (gen/fmap (fn [args] (into [:set/of] args))
                         (gen/vector value-gen 1 max-basic-size))]))

(def set-gen
  "Generator of ASTs for sets."
  (gen/recursive-gen
    (fn rec [inner]
      (gen/one-of
        [(gen/tuple (gen/elements [:set/add
                                   :set/remove])
                    inner value-gen)
         (gen/tuple (gen/elements [:set/union
                                   :set/intersection
                                   :set/difference])
                    inner
                    inner)]))
    set-basic-gen))

(defn eval-node-clj
  "Evaluates an AST node using Clojure data structures."
  [ast]
  (if (vector? ast)
    (let [[f a b] ast]
      (case f
        :set/of           (set (rest ast))
        :set/add          (conj a b)
        :set/remove       (disj a b)
        :set/union        (set/union a b)
        :set/intersection (set/intersection a b)
        :set/difference   (set/difference a b)))
    (case ast
      :set/empty #{}
      ast)))

(defn eval-node-bifurcan
  "Evaluates an AST node using Bifurcan data structures."
  [ast]
  (if (vector? ast)
    (let [[f a b] ast]
      (case f
        :set/of           (Set/from (rest ast))
        :set/add          (.add a b)
        :set/remove       (.remove a b)
        :set/union        (.union a b)
        :set/intersection (.intersection a b)
        :set/difference   (.difference a b)))
    (case ast
      :set/empty Set/EMPTY
      ast)))

(defn eval-trace
  "Evaluates an AST using the given function for evaluating a node. Returns a
  trace: a vector of each intermediate results from evaluating the AST. Each
  trace element is a map:

      {:ast      [:union ...]
       :bifurcan #<Set ...>
       :clj      #{...}}

  The AST is the AST node we evaluated to produce this result. The bifurcan
  result and its Clojure representation follow. We expect that if Bifurcan is
  truly immutable, at the end of the evaluation (datafy bifurcan) = clj. The
  last element in the trace is the result of our top-level AST eval."
  [eval-node ast]
  (if (vector? ast)
    ; Evaluate each argument
    (let [[f & args] ast
          traces (mapv (partial eval-trace eval-node) args)
          ; What did each of those arguments evaluate to?
          evaluated-args (mapv (comp :bifurcan peek) traces)
          ; Evaluate this node
          evaluated (eval-node (into [f] evaluated-args))]
      ; And construct our flattened trace
      (-> (mapcat identity traces)
           vec
           (conj {:ast ast
                  :bifurcan evaluated
                  :clj (datafy evaluated)})))
    ; Bottom nodes are evaluated directly
    (let [evaluated (eval-node ast)]
      [{:ast ast
        :bifurcan evaluated
        :clj (datafy evaluated)}])))

(defn eval-check-immutable
  "Evaluates an AST using the given function for evaluating a node. Ensures
  that at every stage, AST nodes are left unchanged from their original
  values. Returns the evaluated Bifurcan structure."
  ([eval-node ast]
   (let [trace (eval-trace eval-node ast)]
     ; Check the trace elements are still stable.
     (doseq [{:keys [ast bifurcan clj]} trace]
       (is (= clj (datafy bifurcan))
           (when (instance? ICollection bifurcan)
             (str
               "AST:            " (pr-str ast)
               "\nWas:          " (pr-str clj)
               "\nNow:          " (pr-str (datafy bifurcan))
               "\nBifurcan:     " bifurcan
               "\nSize:         " (.size bifurcan)
               "\niterator-seq: " (pr-str (iterator-seq (.iterator bifurcan)))
               "\nseq:          " (pr-str (seq bifurcan))
               "\nelements:     " (.elements bifurcan)
               "\nnths:         " (mapv #(try
                                           (.nth bifurcan %)
                                           (catch IndexOutOfBoundsException e
                                             :out-of-bounds))
                                        (range 0 (inc (max (count clj)
                                                      (.size bifurcan)))))

               ))))
     (:bifurcan (peek trace)))))

(defn eval-compare
  "Evaluates an AST using both Clojure and Bifurcan evaluators, testing that
  the two yield equivalent results."
  [ast]
  (let [clj      (eval-check-immutable eval-node-clj      ast)
        bifurcan (eval-check-immutable eval-node-bifurcan ast)]
    (is (= clj (datafy bifurcan)))
    clj))

(deftest ^:focus set-test
  (checking "sets are immutable" iterations
            [ast set-gen]
            (let [res (eval-compare ast)]
            ;(prn ast)
            ;(prn (eval-compare ast))
            )))
