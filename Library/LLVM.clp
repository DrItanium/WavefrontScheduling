;Copyright (c) 2012, Joshua Scoggins 
;All rights reserved.
;
;Redistribution and use in source and binary forms, with or without
;modification, are permitted provided that the following conditions are met:
;    * Redistributions of source code must retain the above copyright
;      notice, this list of conditions and the following disclaimer.
;    * Redistributions in binary form must reproduce the above copyright
;      notice, this list of conditions and the following disclaimer in the
;      documentation and/or other materials provided with the distribution.
;    * Neither the name of Joshua Scoggins nor the
;      names of its contributors may be used to endorse or promote products
;      derived from this software without specific prior written permission.
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
(deffunction instruction-to-fact (?STR ?PARENT ?index ?pointer)
 "Takes the string representation of the instruction in question and loads it
 into the appropriate element"
 (assert (instruction ?STR parent ?PARENT index ?index pointer ?pointer)))

(deffunction basicblock-to-fact (?Name ?Parent ?pointer)
 "Takes in the makeup a basic block and asserts a fact to construct a basic
 block from through the use of rules"
 (assert (basicblock ?Name parent ?Parent pointer ?pointer)))

(deffunction region-to-fact (?Name ?Parent ?pointer)
 "Converts a region into a fact to be converted into a clips representation"
 (assert (region ?Name parent ?Parent pointer ?pointer)))

(deffunction loop-to-fact (?Name ?Parent ?pointer)
 "Converts a loop into a fact to be convertedf into a clips representation"
 (assert (loop ?Name parent ?Parent pointer ?pointer)))
 
(deffunction function-to-fact (?Name ?pointer)
 "takes the name of a function and turns it into a fact to be converted"
 (assert (function ?Name pointer ?pointer)))


(deffunction imply-successor (?Succ ?Target)
 "Tells clips that the first argument is a successor of the second"
 (assert (successor ?Succ of ?Target)))

(deffunction imply-predecessor (?Pred ?Target)
 "Tells clips that the first argument is a predecessor of the second"
 (assert (predecessor ?Pred of ?Target)))
