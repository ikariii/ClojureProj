(ns language.core
  (:require [instaparse.core :as insta])
  (:import (clojure.asm Opcodes Type ClassWriter)
           (clojure.asm.commons Method GeneratorAdapter)))

(def lang1-parser
  (insta/parser
    "prog = (spaces? expr spaces? <';'> spaces?)*
    <expr> = assig | add-sub
    assig = varname spaces? <'='> spaces? expr
    <add-sub> = mult-div | add | sub
    add = add-sub spaces? <'+'> spaces? mult-div
    sub = add-sub spaces? <'-'> spaces? mult-div
    <mult-div> = factor | mult |div | mod
    mult = mult-div spaces? <'*'> spaces? factor
    div = mult-div spaces? <'/'> spaces? factor
    mod = mult-div spaces? <'mod'> spaces? factor
    <factor> = number | <'('> spaces? expr spaces? <')'> | varget |assig |expo
    <spaces> = <#'\\s+'>
    number = #'-?[0-9]+'
    expo = spaces? expr '^' expr spaces?
    varget = varname | argument
    varname = #'[a-zA-Z]\\w*'
    argument= <'%'>#'[0-9]+'"))
  
(print (lang1-parser "a=%0;a + %1 mod 3;5^2;"))

(defn make-lang0-instr-interpreting [env]
  { :assig (fn[{varname :_ret :as env1} {value :_ret :as env2}]
             (assoc (merge env1 env2) varname value :_ret value))
   :add (fn[{v1 :_ret :as env1} {v2 :_ret :as env2}]
          (assoc (merge env1 env2) :_ret (+ v1 v2)))
   :sub (fn[{v1 :_ret :as env1} {v2 :_ret :as env2}]
          (assoc (merge env1 env2) :_ret (- v1 v2)))
   :mult (fn[{v1 :_ret :as env1} {v2 :_ret :as env2}]
           (assoc (merge env1 env2) :_ret (* v1 v2)))
   :div (fn[{v1 :_ret :as env1} {v2 :_ret :as env2}]
          (assoc (merge env1 env2) :_ret (quot v1 v2)))
   :mod (fn[{v1 :_ret :as env1} {v2 :_ret :as env2}]
          (assoc (merge env1 env2) :_ret (mod v1 v2)))
   :number #(assoc env :_ret (Integer/parseInt %))
   :varname #(assoc env :_ret (keyword %))
   :varget (fn [{varname :_ret :as env1}]
             (assoc env1 :_ret (varname env1)))})
(defn args-to-env[args]
  (into {} (map-indexed #(vector (keyword (str "%" %1)) %2) args)))
(defn make-interpreting [make-instr-interpreting init-env]
  {:prog (fn [& instrs] (:_ret (reduce
                                       (fn[env instr]
                                         (instaparse.core/transform (make-instr-interpreting env) instr))
                                       init-env
                                       instrs)))})

(defn dynamic-eval-args [make-interpreter]
  (fn[ast]
    (fn[& args]
      (instaparse.core/transform (make-interpreting make-interpreter
                                          (assoc (args-to-env args)
                                                 :_ret 0))
                       ast))))

(defn make-lang1-instr-interpreting [env]
  (assoc (make-lang0-instr-interpreting env)
         :argument #(assoc env :_ret (keyword (str "%" %)))))

(def lang1-interpret (dynamic-eval-args make-lang1-instr-interpreting))

(def lang1-interpret-test (->> "a=%0;(a + %1) mod 3; " lang1-parser lang1-interpret))
(lang1-interpret-test 9 1)





(defn compiled [n-args class-name bytecode-generator]
    (let [cw (ClassWriter. (+ ClassWriter/COMPUTE_FRAMES ClassWriter/COMPUTE_MAXS ))
          init (Method/getMethod "void <init>()")
          meth-name "run"
          meth-sig (str "(" (apply str (repeat n-args "I")) ")I")]
      (.visit cw Opcodes/V1_6 Opcodes/ACC_PUBLIC (.replace class-name \. \/) nil "java/lang/Object" nil)
      (doto (GeneratorAdapter. Opcodes/ACC_PUBLIC init nil nil cw)
        (.visitCode)
        (.loadThis)
        (.invokeConstructor (Type/getType Object) init)
        (.returnValue)
        (.endMethod))
      (doto (.visitMethod cw (+ Opcodes/ACC_PUBLIC Opcodes/ACC_STATIC) meth-name meth-sig nil nil )
        (.visitCode)
        (bytecode-generator)
        (.visitMaxs 0 0 )
        (.visitEnd))
      (.visitEnd cw)
      (let [b (.toByteArray cw)
            cl (clojure.lang.DynamicClassLoader.)]
        (.defineClass cl class-name b nil))
      (fn [& args] (clojure.lang.Reflector/invokeStaticMethod class-name meth-name (into-array args))))
    )

(def const-compiling
  {:prog (fn[& instrs](conj (reduce into [[:loadi 0]] instrs)[:reti]))
   :number #(vector [:loadi (Long/parseLong %)])})
(defn assoc-binary-op [m [op instr]]
  (let[binary-op-compiling (fn[op]
                             (fn[instrs-v0 instrs-v1]
         (conj (into instrs-v0 instrs-v1) [op])))]
    (assoc m op (binary-op-compiling instr))))
(def addsub-compiling
  (reduce assoc-binary-op const-compiling [[:add :addi][:sub :subi]]))

(def addmult-compiling
  (reduce assoc-binary-op addsub-compiling [[:mult :multi][:div :divi][:mod :modi]]))

(def lang0-compiling
  (assoc addmult-compiling
         :varget #(vector [:load %])
         :assig (fn[var instrs](conj instrs [:store var]))))

(defmulti generate-instr (fn [mv [instr & args]] instr))

(defn dispatching-bytecode-generating-eval [n-args class-name compiling]
  (fn[ast]
    (let[instrs (instaparse.core/transform compiling ast)
         generate-prog (fn[mv] (reduce generate-instr mv instrs))]
      (compiled n-args class-name generate-prog))))

(defmethod generate-instr :loadi [mv [instr & args]]
  (doto mv
    (.visitLdcInsn (int (first args)))))

(defmethod generate-instr :reti [mv [instr & args]]
  (doto mv
    (.visitInsn Opcodes/IRETURN)))
(defmethod generate-instr :multi [mv [instr & args]]
  (doto mv
    (.visitInsn Opcodes/IMUL)))

(defmethod generate-instr :divi [mv [instr & args]]
  (doto mv
    (.visitInsn Opcodes/IDIV)))
(defmethod generate-instr :modi [mv [instr & args]]
  (doto mv
    (.visitInsn Opcodes/IMUL)))
(defmethod generate-instr :addi [mv [instr & args]]
  (doto mv
    (.visitInsn Opcodes/IADD)))

(defmethod generate-instr :subi [mv [instr & args]]
  (doto mv
    (.visitInsn Opcodes/ISUB)))

(use 'clojure.set)
;; helper function that replaces all the values in map m with the given value v
(defn replace-vals [m v]
  (into {} (map vector (keys m) (repeat v ))))

(defn nb-args[ast]
  (inc (instaparse.core/transform (assoc (replace-vals
                           lang0-compiling (fn[& args]
                                             (apply max (conj (filter number? args)
                                                              -1))))
                          :argument #(Integer/parseInt %))
                   ast)))

(defn args->varnum[ast]
  (instaparse.core/transform {:argument #(Integer/parseInt %)} ast))

(defn to-numeric-vars[nb-args ast]
  (let[varnames
       (instaparse.core/transform
        (assoc (replace-vals
                lang0-compiling
                (fn[& instrs] (apply clojure.set/union (filter set? instrs))))
               :varname (fn[varname]#{varname}))
        ast)
       name->num (into {} (map vector varnames (iterate inc nb-args)))]
    (instaparse.core/transform {:varname #(get name->num %)} ast)))

(defmethod generate-instr :load [mv [instr & args]]
  (doto mv
    (.visitVarInsn Opcodes/ILOAD (int (first args)))))

(defmethod generate-instr :store [mv [instr & args]]
  (doto mv
    (.visitInsn Opcodes/DUP)
    (.visitVarInsn Opcodes/ISTORE (int (first args)))))


(defn lang1-compiler-chain[class-name ast]
  (let[n-args (nb-args ast)
       compiler (dispatching-bytecode-generating-eval n-args class-name lang0-compiling)]
    (->> ast args->varnum (to-numeric-vars n-args) compiler)))

(def lang1-compiler-test (->> "a=%0;b=%1;a mod b;" lang1-parser (lang1-compiler-chain "Lang1Compiler")))
(lang1-compiler-test 5 3)