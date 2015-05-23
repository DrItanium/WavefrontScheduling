;------------------------------------------------------------------------------
;Copyright (c) 2012-2015, Joshua Scoggins 
;All rights reserved.
;
;Redistribution and use in source and binary forms, with or without
;modification, are permitted provided that the following conditions are met:
;    * Redistributions of source code must retain the above copyright
;      notice, this list of conditions and the following disclaimer.
;    * Redistributions in binary form must reproduce the above copyright
;      notice, this list of conditions and the following disclaimer in the
;      documentation and/or other materials provided with the distribution.
;
;THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
;ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
;WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
;DISCLAIMED. IN NO EVENT SHALL Joshua Scoggins BE LIABLE FOR ANY
;DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
;(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
;LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
;ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
;(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
;SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
;------------------------------------------------------------------------------
; lib.clp - Contains set operations (such as superset and equality) and other 
;           operations
;------------------------------------------------------------------------------
(defgeneric apply$ 
            "Applies a given function to each element of a multifield")
(defgeneric pointer-from-name
            "Extracts the corresponding llvm pointer from the target name")
(defgeneric slot-insert-first$
            "Inserts a set of elements to the front a multislot in a given class")
(defgeneric empty$
            "Checks to see if a given multifield is empty or not")
(defgeneric bool
            "A simple function to convert a given piece of input to TRUE or FALSE")
;------------------------------------------------------------------------------
(deffunction superset 
             (?a ?b)
             (and (>= (length$ ?a) 
                      (length$ ?b))
                  (subsetp ?b ?a) 
                  (not (subsetp ?a ?b))))
;------------------------------------------------------------------------------
(deffunction equal$ 
             (?a ?b)
             (and (= (length$ ?a) (length$ ?b))
                  (subsetp ?b ?a) 
                  (subsetp ?a ?b)))
;------------------------------------------------------------------------------
(deffunction has-common-element 
             (?a ?b)
             (progn$ (?c ?a)
                     (if (member$ ?c ?b) then 
                       (return TRUE)))
             (return FALSE))
;------------------------------------------------------------------------------
(deffunction disjoint (?a ?b)
             (not (has-common-element ?a ?b)))
;------------------------------------------------------------------------------
(defmethod apply$
  ((?fn SYMBOL)
   (?elements MULTIFIELD))
  (bind ?output (create$))
  (progn$ (?e ?elements)
          (bind ?output (create$ ?output
                                 (funcall ?fn ?e))))
  (return ?output))
;------------------------------------------------------------------------------
(defmethod apply$
  ((?fn SYMBOL)
   $?elements)
  (apply$ ?fn ?elements))
;------------------------------------------------------------------------------
(defmethod pointer-from-name
  ((?name SYMBOL))
  (send (symbol-to-instance-name ?name) get-pointer))

(defmethod pointer-from-name
  ((?name INSTANCE))
  (send ?name get-pointer))
;------------------------------------------------------------------------------
(deffunction symbol-to-pointer-list
             "Converts a given list of symbols that represent InteropObjects and pulls the
             pointer value out of it. This function assumes order is important"
             (?list)
             (apply$ pointer-from-name
                     ?list))
;------------------------------------------------------------------------------
(defmethod batch*
  "batch multiple files"
  ((?elements MULTIFIELD (> (length$ ?elements) 1)))
  (progn$ (?a ?elements)
          (batch* ?a)))
;------------------------------------------------------------------------------
(defmethod batch*
  "batch multiple files"
  (($?elements (> (length$ ?elements) 1)))
  (batch* ?elements))
(defmethod slot-insert-first$
  ((?obj INSTANCE)
   (?slot SYMBOL)
   (?elements MULTIFIELD))
  (slot-insert$ ?obj 
                ?slot 
                1 (expand$ ?elements)))
(defmethod slot-insert-first$
  ((?obj INSTANCE)
   (?slot SYMBOL)
   $?elements)
  (slot-insert-first$ ?obj 
                      ?slot 
                      ?elements))
(defmethod empty$
  ((?list MULTIFIELD))
  (= (length$ ?list) 0))

(defmethod slot-delete-element$
  ((?object INSTANCE)
   (?slot-name SYMBOL)
   ?target)
  (bind ?result (member$ ?target 
                         (send ?object 
                               (sym-cat get- ?slot-name))))
  (and ?result
       (slot-delete$ ?object
                     ?slot-name
                     (expand$ (if (multifieldp ?result) then
                                ?result
                                else
                                ; define the range syntax since it was a single 
                                ; element
                                (create$ ?result
                                         ?result))))))

(defmethod slot-delete-element$
  ((?object INSTANCE)
   (?slot-name SYMBOL)
   $?target)
  (slot-delete-element$ ?object
                        ?slot-name
                        ?target))

(defmethod bool
 "If it isn't FALSE then it is TRUE"
  ((?v (neq ?v FALSE)))
  TRUE)

(defmethod bool
  "If we get FALSE in then just pass it through"
  ((?v SYMBOL (eq ?v FALSE)))
  FALSE)

