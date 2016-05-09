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
; config.clp - Contains the "switches" used to enable different aspects of
; debugging
;------------------------------------------------------------------------------
;If you want to do things that occur at start up then make
; the changes here :). Uncomment the line below to enable debug mode :D

(deffacts debug-stats 
 (Debug)
 (Profile)
 ;(Rules)
 ;(Blocks)
 ;(Children)
 ;(Separator)
 ;(Paths)
 ;(Loop)
 ;(Facts)
 ;(RunStatistics)
 ;(Memory)
 )
(defrule GetInitialMemoryConsumption
 (Debug)
 (Memory)
 =>
 (printout t "Initial Memory Consumption " (/ (mem-used) 131072) " MB" crlf))

(defrule GetRunStatistics
 (Debug)
 (RunStatistics)
 =>
 (watch statistics))
(defrule WatchRules
 (Debug)
 (Rules)
 =>
 (watch rules))

(defrule ProfileConstructs 
 (Debug)
 (Profile)
 =>
 (profile-reset)
 (profile constructs)
 (set-profile-percent-threshold 1))
