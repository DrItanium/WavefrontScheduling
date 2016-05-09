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
; Defines the series that the expert system will execute through on invocation
; It works through a fact definition structure
;------------------------------------------------------------------------------
(defrule first-rule-has-loops
         (declare (salience 10000))
         (initial-fact)
         (exists (object (is-a Loop)))
         =>
         (assert (Stage BuildFlatList
                        ExpandFlatList
                        ClaimOwnership
                        Arbitrate
                        ResolveClaims
                        DeterminantConstruction
                        DeterminantPopulation
                        DeterminantResolution
                        DeterminantIndirectResolution
                        Fixup 
                        FixupUpdate
                        FixupRename
                        CleanUp-Merger
                        ModificationPropagation
                        FrequencyAnalysis
                        Analysis 
                        Analysis-Update
                        ExtendedMemoryAnalysis
                        ExtendedMemoryAnalysis-Merge
                        ExtendedMemoryAnalysis-Inject
                        ExtendedMemoryAnalysis-MakeSet
                        Path
                        PathUpdate
                        WavefrontInit
                        WavefrontSchedule
                        WavefrontFinal
                        Final)))
;------------------------------------------------------------------------------
(defrule first-rule-no-loops 
         (declare (salience 10000))
         (initial-fact)
         (not (exists (object (is-a Loop))))
         =>
         (assert (Stage ModificationPropagation
                        FrequencyAnalysis
                        Analysis 
                        Analysis-Update
                        ExtendedMemoryAnalysis
                        ExtendedMemoryAnalysis-Merge
                        ExtendedMemoryAnalysis-Inject
                        ExtendedMemoryAnalysis-MakeSet
                        Path
                        PathUpdate
                        WavefrontInit
                        WavefrontSchedule
                        WavefrontFinal
                        Final)))
;------------------------------------------------------------------------------
(defrule change-stage
         (declare (salience -10000))
         ?fct <- (Stage ? $?rest)
         =>
         (retract ?fct)
         (assert (Stage $?rest)))
;------------------------------------------------------------------------------
; Rules that merge loops and regions together
;------------------------------------------------------------------------------
(defrule ConstructFlatListForRegion
         "Creates a flat representation of the contents of the given region"
         (Stage BuildFlatList $?)
         (object (is-a Region) 
                 (name ?id) 
                 (Contents $?z))
         (not (exists (object (is-a FlatList) 
                              (Parent ?id))))
         =>
         (make-instance of FlatList 
                        (Parent ?id)) 
         (assert (Populate FlatList of ?id with $?z)))
;------------------------------------------------------------------------------
(defrule PopulateFlatList-BasicBlock
         (Stage BuildFlatList $?)
         ?f <- (Populate FlatList of ?id with ?first $?rest)
         ?o <- (object (is-a FlatList) 
                       (Parent ?id))
         (object (is-a BasicBlock) 
                 (name ?first))
         =>
         (slot-insert$ ?o Contents 1 ?first)
         (retract ?f)
         (assert (Populate FlatList of ?id with $?rest)))
;------------------------------------------------------------------------------
(defrule PopulateFlatList-Region
         (Stage BuildFlatList $?)
         ?f <- (Populate FlatList of ?id with ?first $?rest)
         ?o <- (object (is-a FlatList) (Parent ?id))
         (object (is-a Region) (name ?first))
         (object (is-a FlatList) (Parent ?first) (name ?name))
         =>
         ;Add the reference to FlatList for the time being until we have
         ;finished constructing an entire flat list
         (slot-insert$ ?o Contents 1 ?name)
         (retract ?f)
         (assert (Populate FlatList of ?id with $?rest)))
;------------------------------------------------------------------------------
(defrule RetractFlatListConstruction
         (Stage BuildFlatList $?)
         ?f <- (Populate FlatList of ? with)
         =>
         (retract ?f))
;------------------------------------------------------------------------------
(defrule ExpandFlatListEntry
         "Takes a flat list and expands one of the elements of the contents if 
         it turns out that element is another flat list"
         (Stage ExpandFlatList $?)
         ?id <- (object (is-a FlatList) 
                        (Contents $?a ?b $?c))
         (object (is-a FlatList) 
                 (name ?b) 
                 (Contents $?j))
         =>
         (send ?id put-Contents ?a ?j ?c))
;------------------------------------------------------------------------------
(defrule ClaimOwnership
         "Asserts that a region owns another through a subset check. The first 
         flat list is checked to see if it is a _proper_ subset of the second"
         (Stage ClaimOwnership $?)
         (object (is-a FlatList) 
                 (name ?i0) 
                 (Contents $?c0)
                 (Parent ?p0))
         (object (is-a FlatList) 
                 (name ?i1&~?i0) 
                 (Contents $?c1)
                 (Parent ?p1))
         (test (and (> (length$ ?c1)
                       (length$ ?c0))
                    (subsetp ?c0 ?c1)))
         =>
         (assert (claim ?p1 owns ?p0)))
;------------------------------------------------------------------------------
(defrule ClaimOwnershipOfBlocks
         "This rule is used to assert ownership claims on basic blocks"
         (Stage ClaimOwnership $?)
         (object (is-a FlatList) 
                 (name ?p) 
                 (Contents $? ?b $?)
                 (Parent ?p0))
         (object (is-a BasicBlock) 
                 (name ?b))
         =>
         (assert (claim ?p0 owns ?b)))
;------------------------------------------------------------------------------
(defrule ClaimEquivalence
         "Asserts that two regions are equivalent if one flat list contains the
         same elements as a second one."
         (Stage ClaimOwnership $?)
         ?f0 <- (object (is-a FlatList) 
                        (name ?i0) 
                        (Contents $?c0)
                        (Parent ?p0))
         ?f1 <- (object (is-a FlatList) 
                        (name ?i1&~?i0) 
                        (Contents $?c1)
                        (Parent ?p1))
         (test (and (= (length$ ?c1)
                       (length$ ?c0))
                    (subsetp ?c0 
                             ?c1)))
         =>
         (assert (claim ?p1 equivalent ?p0)))
;------------------------------------------------------------------------------
(defrule MergeClaimsOfEquivalence
         "It is possible for two facts of equivalence to actually be the same 
         fact"
         (declare (salience -1))
         (Stage ClaimOwnership $?)
         ?f0 <- (claim ?a equivalent ?b)
         ?f1 <- (claim ?b equivalent ?a)
         =>
         (retract ?f1 ?f0)
         (assert (claim ?a equivalent ?b)))
;------------------------------------------------------------------------------
(defrule EliminateEquivalences-LoopFirst
         "If we find an equivalence then it means that a loop and a region 
         contain the same elements. Therefore the loop persists and the region 
         dies. The loop is the first entry."
         (declare (salience 1))
         (Stage Arbitrate $?)
         ?f0 <- (claim ?a equivalent ?b)
         (object (is-a Loop) 
                 (name ?a))
         (object (is-a Region&~Loop) 
                 (name ?b))
         =>
         (retract ?f0)
         (assert (delete region ?b)
                 (replace ?b with ?a)))
;------------------------------------------------------------------------------
(defrule EliminateEquivalences-LoopSecond
         "If we find an equivalence then it means that a loop and a region 
         contain the same elements. Therefore the loop persists and the region
         dies. The loop is the second entry."
         (declare (salience 1))
         (Stage Arbitrate $?)
         ?f0 <- (claim ?b equivalent ?a)
         (object (is-a Loop) 
                 (name ?a))
         (object (is-a Region&~Loop) 
                 (name ?b))
         =>
         (retract ?f0)
         (assert (delete region ?b)
                 (replace ?b with ?a)))
;------------------------------------------------------------------------------
; Now that we have asserted delete and replacement claims it's necessary to
; carry those claims out. First, we need to do the replacement actions
; We need to apply these changes to the flat lists associated with these
; objects to ensure that we do the proper replacement thing. 
; What we do is we use those replacement facts to retract the ownership claims
;
; Then we go through and perform partial replacement on the flat lists 
;------------------------------------------------------------------------------
(defrule RemoveStaleClaims-DeletionTargetClaimsAnother
         "We target claims of ownership that deal with a given region that has 
         to be replaced by another due to equivalence"
         (declare (salience 1))
         (Stage ResolveClaims $?)
         ?f0 <- (replace ?old with ?new)
         ?f1 <- (claim ?old owns ?other)
         =>
         (retract ?f0 ?f1)
         (assert (claim ?new owns ?other)
                 (replace ?old with ?new)))
;------------------------------------------------------------------------------
(defrule RemoveStaleClaims-AnotherClaimsDeletionTarget
         (declare (salience 1))
         (Stage ResolveClaims $?)
         ?f0 <- (replace ?old with ?new)
         ?f1 <- (claim ?other owns ?old)
         =>
         (retract ?f0 ?f1)
         (assert (claim ?other owns ?new)
                 (replace ?old with ?new)))
;------------------------------------------------------------------------------
(defrule RemoveStaleClaims-NoMoreConvergence
         "Retract replacement facts because there are no more claims to worry 
         about"
         (Stage ResolveClaims $?)
         ?f0 <- (replace ?old with ?new)
         =>
         (retract ?f0))
;------------------------------------------------------------------------------
(defrule DeleteTargetRegion
         "Deletes the target region slated for deletion"
         (Stage ResolveClaims $?)
         ?f0 <- (delete region ?r)
         =>
         (retract ?f0)
         (unmake-instance ?r))
;------------------------------------------------------------------------------
(defrule DeleteFlatLists 
         "Deletes all of the flat lists in a single rule fire"
         (Stage CleanUp-Merger $?)
         =>
         (progn$ (?fl (find-all-instances ((?list FlatList)) TRUE))
                 (unmake-instance ?fl)))
;------------------------------------------------------------------------------
; Rules for propagating producers (values)
;------------------------------------------------------------------------------
(defrule PropagateBlockProducers
         (Stage ModificationPropagation $?)
         (object (is-a BasicBlock) 
                 (name ?b) 
                 (Parent ?r) 
                 (Produces $?produces))
         =>
         (send ?r 
               set-Produces-and-propagate-up 
               ?produces))
;------------------------------------------------------------------------------
(defmessage-handler Region set-Produces-and-propagate-up primary
                    "Insert the provided set of elements into the Produces multislot and then send that data up to the target's parent" 
                    ($?elements)
                    (slot-direct-insert$ Produces
                                         1
                                         ?elements)
                    (if (and (instance-existp ?self:Parent)
                             (or (eq (class ?self:Parent)
                                     Region)
                                 (superclassp Region
                                              (class ?self:Parent)))) then
                      (send ?self:Parent 
                            set-Produces-and-propagate-up 
                            ?elements)))
;(defrule PropagateRegionProducers-ParentExists
;         (Stage ModificationPropagation $?)
;         ?fct <- (Give ?r from ? the following produced items $?produced)
;         ?region <- (object (is-a Region) 
;                            (name ?r) 
;                            (Parent ?p))
;         (object (is-a Region)
;                 (name ?p))
;         =>
;         (retract ?fct)
;         (assert (Give ?p from ?r the following produced items $?produced))
;         (slot-insert$ ?region Produces 1 ?produced))
;------------------------------------------------------------------------------
;(defrule PropagateRegionProducers-ParentDoesntExist
;         (Stage ModificationPropagation $?)
;         ?fct <- (Give ?r from ? the following produced items $?produced)
;         ?region <- (object (is-a Region) 
;                            (name ?r) 
;                            (Parent ?p))
;         (not (exists (object (is-a Region) 
;                              (name ?p))))
;         =>
;         (retract ?fct)
;         (slot-insert$ ?region Produces 1 ?produced))
;------------------------------------------------------------------------------
(defmessage-handler Instruction inject-producers-and-non-local-deps primary
                    (?op)
                    (slot-direct-insert$ Producers 
                                         1
                                         ?op)
                    (slot-direct-insert$ NonLocalDependencies
                                         1
                                         ?op))
(defrule IdentifyNonLocalDependencies
         (Stage ModificationPropagation $?)
         ?i0 <- (object (is-a Instruction) 
                        (Parent ?p) 
                        (name ?t0) 
                        (Operands $? ?op $?))
         (object (is-a thing) 
                 (name ?op) 
                 (Parent ~?p))
         =>
         ;since we don't copy the set of producers at the start anymore we
         ;need this operation as well
         (send ?i0 
               inject-producers-and-non-local-deps 
               ?op))
;------------------------------------------------------------------------------
; Rules for determining ownership of blocks, regions, etc
;------------------------------------------------------------------------------
;(defrule ConstructDeterminantForRegionOrBasicBlock
;         (Stage DeterminantConstruction $?)
;         (object (is-a Region|BasicBlock) 
;                 (name ?r))
;         (not (exists (object (is-a OwnershipDeterminant) 
;                              (Parent ?r))))
;         =>
;         (make-instance of OwnershipDeterminant 
;                        (Parent ?r)))
;------------------------------------------------------------------------------
;(defmessage-handler OwnershipDeterminant add-to-potential-children primary
;                    (?element)
;                    (slot-direct-insert$ PotentialChildren
;                                         1
;                                         ?element))
;(defmessage-handler OwnershipDeterminant add-to-claims primary
;                    (?element)
;                    (slot-direct-insert$ Claims
;                                         1 
;                                         ?element))
;(defrule PopulateDeterminant
;         (Stage DeterminantPopulation $?)
;         ?fct <- (claim ?a owns ?b)
;         (object (is-a OwnershipDeterminant) 
;                 (Parent ?b)
;                 (name ?obj))
;         (object (is-a OwnershipDeterminant) 
;                 (Parent ?a)
;                 (name ?obj2))
;         =>
;         (retract ?fct)
;         (send ?obj2 add-to-potential-children ?b)
;         (assert (item ?a claims ?b)))
(deftemplate ownership-claim
 (slot type
  (type SYMBOL)
  (allowed-symbols direct
   indirect))
 (slot owner
  (type INSTANCE)
  (default ?NONE))
 (slot target
  (type INSTANCE)
  (default ?NONE)))

(defrule ModifyClaim
         (Stage DeterminantPopulation $?)
         ?f <- (claim ?a owns ?b)
         =>
         (retract ?f)
         (assert (ownership-claim (owner ?a)
                                  (target ?b))))


;------------------------------------------------------------------------------
(defrule DetermineIndirectClaim
         (Stage DeterminantResolution $?)
         ?f <- (ownership-claim (owner ?high)
                                (target ?low)
                                (type direct))
         (ownership-claim (owner ?mid)
                          (target ?low)
                          (type direct))
         (ownership-claim (owner ?high)
                          (target ?mid)
                          (type direct))
         =>
         (modify ?f 
                 (type indirect)))

;------------------------------------------------------------------------------
(defrule DetermineIndirectIndirectClaim
         (Stage DeterminantIndirectResolution $?)
         ?f <- (ownership-claim (owner ?high)
                                (target ?low)
                                (type direct))
         (ownership-claim (owner ?mid)
                          (target ?low)
                          (type direct))
         (ownership-claim (owner ?high)
                          (target ?mid)
                          (type indirect))
         =>
         (modify ?f (type indirect)))

;------------------------------------------------------------------------------
(defrule DeleteNonExistentReferences
         (Stage Fixup $?)
         (object (is-a Region) 
                 (name ?region)
                 (Contents $?ind ?b $?))
         (not (exists (object (name ?b))))
         =>
         (slot-delete$ ?region
                       Contents
                       (bind ?ind0
                             (+ (length$ ?ind) 1))
                       ?ind0))
;------------------------------------------------------------------------------
(defrule UpdateWithClaim
         (Stage FixupUpdate $?)
         ?f <- (ownership-claim (type direct)
                                (owner ?p)
                                (target ?a))
         =>
         (retract ?f)
         (send ?a put-Parent ?p)
         (slot-insert$ ?p
          Contents
          1 
          ?a))
;------------------------------------------------------------------------------
;(defrule UpdateOwnerOfTargetBasicBlock
;         (Stage FixupUpdate $?)
;         (ownership-claim (type direct)
;                          (
;         (object (is-a OwnershipDeterminant) 
;                 (Parent ?p) 
;                 (Claims ?a))
;         ?obj <- (object (is-a BasicBlock) (name ?p))
;         =>
;         (modify-instance ?obj (Parent ?a)))
;;------------------------------------------------------------------------------
;(defrule AddNewChildToTargetRegion
;         (Stage FixupUpdate $?)
;         ?f <- (ownership-claim (type direct)
;                                (owner ?p)
;                                (target ?a))
;         (object (is-a Region)
;                 (name ?p)
;                 (Contents $?c&:(not (member$ ?a ?c))))
;         =>
;         (retract ?f)
;         (slot-insert$ ?region 
;                       Contents 1
;                       ?a))
;
;;------------------------------------------------------------------------------
;(defrule CleanupOwnershipDeterminants
;         "Deletes all of the OwnershipDeterminant objects in a single rule 
;         fire"
;         (Stage CleanUp-Merger $?)
;         =>
;         (progn$ (?obj (find-all-instances ((?list OwnershipDeterminant)) 
;                                           TRUE))
;                 (unmake-instance ?obj)))
;------------------------------------------------------------------------------
(defrule RemoveUnownedElements
         "Now that we have figured out and updated ownership claims it is 
         necessary to remove leftover entries in other regions"
         (Stage FixupRename $?)
         (object (is-a Region) 
                 (name ?t) 
                 (Contents $?a ?b $?c))
         (object (is-a thing) 
                 (name ?b) 
                 (Parent ~?t))
         =>
         (modify-instance ?t 
                          (Contents $?a $?c)))
;------------------------------------------------------------------------------
(defrule FAILURE-TooManyClaimsOfOwnership
         (Stage Fixup $?)
         ?f0 <- (ownership-claim (owner ?a)
                                 (target ?name)
                                 (type direct))
         ?f1 <- (ownership-claim (owner ~?a)
                                 (target ?name)
                                 (type direct))
         (test (neq ?f0 
                    ?f1))
         =>
         (bind ?output
               (create$))
         (do-for-all-facts ((?o ownership-claim))
                           (eq ?o:target 
                               ?name)
                           (bind ?output
                                 ?output
                                 ?o:owner))
         (printout t 
                   "ERROR: " ?name " has more than one claim of ownership on"
                   " it!" crlf "The claims are " ?output crlf)
         (halt))
;------------------------------------------------------------------------------
; The Analysis stage is the first stage that takes place when LLVM hands off
; control to CLIPS. It is tasked with:
; 
; 1) Identifying Parent Hierarchies for BasicBlocks, Regions, Instructions, and
; Loops
; 2) Identifying Variant and Invariant Operands for Instructions and BasicBlocks
; 3) Identifying Producers and Consumers on the Block Level
; 4) Partial Aspect Block Choking using the list of UsedInBlocks found in each
; instruction.
; 
; What's neat about this stage is that the rules can be fired in any order as
; they will evaluate correctly based on salience tweaking and the fact that the
; information is independent of one another. This means that I don't need to
; worry about breaking pre-existing rules as I add new rules to this Stage.
; 
; This stage will contain the most number of rules out of any stage
; 
; As this code is being written this list will be updated.
;------------------------------------------------------------------------------
; Frequency analysis - Determines which regions to apply wavefront scheduling to
;------------------------------------------------------------------------------
(defrule InstanceFrequencyCounter
         "Creates a frequency counter hint for basic blocks"
         (declare (salience 2))
         (Stage FrequencyAnalysis $?)
         (object (is-a Region) 
                 (name ?p) 
                 (CanWavefrontSchedule FALSE))
         (not (exists (object (is-a FrequencyAnalysis) 
                              (Parent ?p))))
         =>
         (make-instance of FrequencyAnalysis 
                        (Parent ?p)))
;------------------------------------------------------------------------------
(defrule IncrementFrequencyCounter-BasicBlock
         "Goes through a given Region counting the number of basic blocks found
         within the region. Valid blocks are blocks that contain more than one 
         instruction as we don't want to count JS nodes as they don't usually 
         contain code."
         (declare (salience 1))
         (Stage FrequencyAnalysis $?)
         (object (is-a Region) 
                 (name ?p) 
                 (Contents $? ?t $?) 
                 (CanWavefrontSchedule FALSE))
         (object (is-a BasicBlock) 
                 (name ?t) 
                 (Parent ?p) 
                 (Contents $?insts))
         (test (> (length$ $?insts) 1))
         ?fa <- (object (is-a FrequencyAnalysis) 
                        (Parent ?p))
         =>
         (send ?fa .IncrementFrequency))
;------------------------------------------------------------------------------
(defrule ImplyEnoughBlocks
         "There are enough blocks within the target region to make it a 
         candidate for wavefront scheduling. Make a hint that says this."
         ;(declare (salience 200))
         (Stage FrequencyAnalysis $?)
         ?fa <- (object (is-a FrequencyAnalysis) 
                        (Parent ?p) 
                        (Frequency ?z&:(< 1 ?z 100)))
         ?region <- (object (is-a Region)
                            (name ?p))
         =>
         (unmake-instance ?fa)
         (modify-instance ?region (CanWavefrontSchedule TRUE)))
;------------------------------------------------------------------------------
; Block dependency creation - Rules pertaining to the creation of data 
; dependencies between different instructions inside of a basic block
;------------------------------------------------------------------------------
(defrule MarkLocalDependency-Call
         (declare (salience 1))
         (Stage Analysis $?)
         (object (is-a CallInstruction) (Parent ?p) (name ?t0) 
                 (ArgumentOperands $? ?o $?))
         (object (is-a Instruction) (name ?o) (Parent ?p))
         =>
         (assert (Instruction ?o produces ?t0)
                 (Instruction ?t0 consumes ?o)))
;------------------------------------------------------------------------------
(defrule MarkLocalDependency 
         (Stage Analysis $?)
         ?i0 <- (object (is-a Instruction&~CallInstruction) (Parent ?p) (name ?t0) 
                        (Operands $? ?o $?))
         (object (is-a Instruction) (name ?o) (Parent ?p))
         =>
         (assert (Instruction ?o produces ?t0)
                 (Instruction ?t0 consumes ?o)))
;------------------------------------------------------------------------------
(defrule MarkInstructionsThatHappenBeforeCall-WritesToMemory
         (Stage Analysis $?)
         (object (is-a BasicBlock) (name ?v) (Contents $?before ?n0 $?))
         (object (is-a CallInstruction) (name ?n0) (Parent ?v) 
                 (MayWriteToMemory TRUE))
         =>
         (progn$ (?n1 ?before)
                 (assert (Instruction ?n0 consumes ?n1)
                         (Instruction ?n1 produces ?n0))))
;------------------------------------------------------------------------------
(defrule MarkInstructionsThatHappenBeforeCall-HasSideEffects
         (Stage Analysis $?)
         (object (is-a BasicBlock) (name ?p) (Contents $?a ?n0 $?))
         (object (is-a CallInstruction) (name ?n0) (Parent ?p)
                 (MayHaveSideEffects TRUE))
         =>
         (progn$ (?n1 ?a)
                 (assert (Instruction ?n0 consumes ?n1)
                         (Instruction ?n1 produces ?n0))))
;------------------------------------------------------------------------------
(defrule MarkCallInstructionDependency-ModifiesMemory
         "Creates a series of dependencies for all instructions following a 
         call instruction if it turns out that the call could modify memory."
         (Stage Analysis $?)
         (object (is-a BasicBlock) (name ?p) (Contents $? ?name $?rest))
         (object (is-a CallInstruction) (name ?name) (Parent ?p)
                 (MayWriteToMemory TRUE))
         =>
         (assert (Element ?p has a CallBarrier))
         (progn$ (?following ?rest)
                 (assert (Instruction ?following has a CallDependency)
                         ;(Instruction ?following consumes ?name)
                         (Instruction ?name produces ?following))))
;------------------------------------------------------------------------------
(defrule MarkCallInstructionDependency-InlineAsm
         "Creates a series of dependencies for all instructions following a 
         call instruction if it turns out that the call is inline asm."
         (Stage Analysis $?)
         (object (is-a BasicBlock) (name ?p) (Contents $? ?name $?rest))
         (object (is-a CallInstruction) (name ?name) (Parent ?p) 
                 (IsInlineAsm TRUE))
         =>
         (assert (Element ?p has a CallBarrier))
         (progn$ (?following ?rest)
                 (assert (Instruction ?following has a CallDependency)
                         ;(Instruction ?following consumes ?name)
                         (Instruction ?name produces ?following))))
;------------------------------------------------------------------------------
(defrule MarkCallInstructionDependency-SideEffects
         "Creates a series of dependencies for all instructions following a 
         call instruction if it turns out that the call has side effects."
         (Stage Analysis $?)
         (object (is-a CallInstruction) (name ?name) (Parent ?p)
                 (MayHaveSideEffects TRUE)) 
         (object (is-a BasicBlock) (name ?p) (Contents $? ?name $?rest))
         =>
         (assert (Element ?p has a CallBarrier))
         (progn$ (?following ?rest)
                 (assert (Instruction ?following has a CallDependency)
                         ;(Instruction ?following consumes ?name)
                         (Instruction ?name produces ?following))))
;------------------------------------------------------------------------------
(defrule FlagCallBarrierForDiplomat-HasParent
         ;(declare (salience -10))
         (Stage Analysis-Update $?)
         ?fct <- (Element ?z has a CallBarrier)
         ?d <- (object (is-a Diplomat) (name ?z) (Parent ?p) 
                       (HasCallBarrier FALSE))
         (exists (object (is-a Diplomat) (name ?p)))
         =>
         (retract ?fct)
         (assert (Element ?p has a CallBarrier))
         (modify-instance ?d (HasCallBarrier TRUE)))
;------------------------------------------------------------------------------
(defrule PropagateCallBarrierForDiplomat-HasParent
         ;(declare (salience -10))
         (Stage Analysis-Update $?)
         ?fct <- (Element ?z has a CallBarrier)
         ?d <- (object (is-a Diplomat) (name ?z) (Parent ?p) 
                       (HasCallBarrier TRUE))
         (exists (object (is-a Diplomat) (name ?p)))
         =>
         (retract ?fct)
         (assert (Element ?p has a CallBarrier)))
;------------------------------------------------------------------------------
(defrule FlagCallBarrierForDiplomat-NoParent
         ;(declare (salience -10))
         (Stage Analysis-Update $?)
         ?fct <- (Element ?z has a CallBarrier)
         ?d <- (object (is-a Diplomat) (name ?z) (Parent ?p) 
                       (HasCallBarrier FALSE))
         (not (exists (object (is-a Diplomat) (name ?p))))
         =>
         (retract ?fct)
         (modify-instance ?d (HasCallBarrier TRUE)))
;------------------------------------------------------------------------------
(defrule PropagateCallBarrierForDiplomat-NoParent
         ;(declare (salience -10))
         (Stage Analysis-Update $?)
         ?fct <- (Element ?z has a CallBarrier)
         ?d <- (object (is-a Diplomat) (name ?z) (Parent ?p) 
                       (HasCallBarrier TRUE))
         (not (exists (object (is-a Diplomat) (name ?p))))
         =>
         (retract ?fct))
;------------------------------------------------------------------------------
(defrule MarkHasACallDependency-Set
         (Stage Analysis-Update $?)
         ?fct <- (Instruction ?target has a CallDependency)
         ?inst <- (object (is-a Instruction) (name ?target) 
                          (HasCallDependency FALSE))
         =>
         (retract ?fct)
         (modify-instance ?inst (HasCallDependency TRUE)))
;------------------------------------------------------------------------------
(defrule MarkHasACallDependency-Ignore
         (Stage Analysis-Update $?)
         ?fct <- (Instruction ?target has a CallDependency)
         ?inst <- (object (is-a Instruction) (name ?target) 
                          (HasCallDependency TRUE))
         =>
         (retract ?fct))
;------------------------------------------------------------------------------
(defrule StoreToLoadDependency
         (Stage ExtendedMemoryAnalysis $?)
         (object (is-a StoreInstruction) (Parent ?p) (name ?t0)
                 (TimeIndex ?ti0) (MemoryTarget ?sym0))
         (object (is-a LoadInstruction) (Parent ?p) (name ?t1) 
                 (TimeIndex ?ti1&:(< ?ti0 ?ti1)) (MemoryTarget ?sym1))
         (test (or (eq ?sym0 ?sym1) (eq ?sym0 UNKNOWN)))
         =>
         (assert (Instruction ?t1 consumes ?t0)
                 (Instruction ?t0 produces ?t1)))
;------------------------------------------------------------------------------
(defrule StoreToStoreDependency
         (Stage ExtendedMemoryAnalysis $?)
         (object (is-a StoreInstruction) (Parent ?p) (name ?t0)
                 (TimeIndex ?ti0) (MemoryTarget ?sym0))
         (object (is-a StoreInstruction) (Parent ?p) (name ?t1) 
                 (TimeIndex ?ti1&:(< ?ti0 ?ti1)) (MemoryTarget ?sym1))
         (test (or (eq ?sym0 ?sym1) (eq ?sym0 UNKNOWN)))
         =>
         (assert (Instruction ?t1 consumes ?t0)
                 (Instruction ?t0 produces ?t1)))
;------------------------------------------------------------------------------
(defrule LoadToStoreDependency
         (Stage ExtendedMemoryAnalysis $?)
         (object (is-a LoadInstruction) (Parent ?p) (name ?t0)
                 (TimeIndex ?ti0) (MemoryTarget ?sym0)) 
         (object (is-a StoreInstruction) (Parent ?p) (name ?t1) 
                 (TimeIndex ?ti1&:(< ?ti0 ?ti1)) (MemoryTarget ?sym1))
         (test (or (eq ?sym0 ?sym1) (eq ?sym0 UNKNOWN)))
         =>
         (assert (Instruction ?t1 consumes ?t0)
                 (Instruction ?t0 produces ?t1)))
;------------------------------------------------------------------------------
; Memory barrier creation - Rules pertaining to the creation of
; memory barriers to prevent loads and stores from being moved above a specific
; point within the program during the act of scheduling.
;------------------------------------------------------------------------------
; Barriers consist of reads and writes that can't be verified as to their exact
; source. 
;------------------------------------------------------------------------------
; TODO: Put in a field for load and store instructions that describes what
; is being referenced. By default this slot is UNKNOWN.
;------------------------------------------------------------------------------
(defrule AssertLoadBarrierEvaluation
         "Creates a fact that tells the system to analyze the given load 
         instruction to see if it is necessary to create a memory barrier for 
         the given instruction"
         (declare (salience 5))
         (Stage Analysis $?)
         (object (is-a LoadInstruction) (name ?t0) (Operands ?target $?))
         =>
         (assert (Analyze ?target for load ?t0)))
;------------------------------------------------------------------------------
(defrule AssertStoreBarrierEvaluation
         "Creates a fact that tells the system to analyze the given store 
         instruction to see if it is necessary to create a memory barrier for 
         the given instruction"
         (declare (salience 5))
         (Stage Analysis $?)
         (object (is-a StoreInstruction) (name ?t0) 
                 (DestinationRegisters ?target))
         =>
         (assert (Analyze ?target for store ?t0)))
;------------------------------------------------------------------------------
(defrule IdentifyGetElementPointerLoadBarrier
         "Creates a load memory barrier hint if it turns out that the load 
         instruction refers to a getelementptr instruction but that 
         getelementptr doesn't refer to a alloca instruction or constant."
         (declare (salience 4))
         (Stage Analysis $?)
         ?fct <- (Analyze ?target for load ?t0)
         ?i0 <- (object (is-a LoadInstruction) (name ?t0) (Parent ?p))
         (object (is-a GetElementPointerInstruction) (name ?target) 
                 (Operands ?a $?))
         (object (is-a ~AllocaInstruction&~Constant) (name ?a))
         (object (is-a BasicBlock) (name ?p) (Parent ?r))
         =>
         (retract ?fct)
         (modify-instance ?i0 (MemoryTarget UNKNOWN))
         (assert (element ?p reads from UNKNOWN)
                 (Element ?p has a MemoryBarrier)
                 (Element ?r has a MemoryBarrier)))
;------------------------------------------------------------------------------
(defrule PopulateBasicBlockWithReadFrom-Alloca
         "Does a check to see if the load instruction refers directly to an
         AllocaInstruction or Constant. If it does then mark it as though the 
         block reads from it"
         (declare (salience 4))
         (Stage Analysis $?)
         ?fct <- (Analyze ?target for load ?t0)
         ?i0 <- (object (is-a LoadInstruction) (name ?t0) (Parent ?p))
         (object (is-a AllocaInstruction) (name ?target))
         =>
         (retract ?fct)
         (modify-instance ?i0 (MemoryTarget ?target))
         (assert (element ?p reads from ?target)))
;------------------------------------------------------------------------------
(defrule PopulateBasicBlockWithReadFrom-Constant
         "Does a check to see if the load instruction refers directly to an
         AllocaInstruction or Constant. If it does then mark it as though the 
         block reads from it"
         (declare (salience 4))
         (Stage Analysis $?)
         ?fct <- (Analyze ?target for load ?t0)
         ?i0 <- (object (is-a LoadInstruction) (name ?t0) (Parent ?p))
         (object (is-a Constant) (name ?target))
         =>
         (retract ?fct)
         (modify-instance ?i0 (MemoryTarget ?target))
         (assert (element ?p reads from ?target)))
;------------------------------------------------------------------------------
(defrule PopulateBasicBlockWithReadFrom-GetElementPointer-Alloca
         "Does a check to see if a given LoadInstruction referring to a
         GetElementPointerInstruction refers to an AllocaInstruction or 
         Constant. If it does then mark it in the ReadsFrom multifield"
         (declare (salience 4))
         (Stage Analysis $?)
         ?fct <- (Analyze ?target for load ?t0)
         ?i0 <- (object (is-a LoadInstruction) (name ?t0) (Parent ?p))
         (object (is-a GetElementPointerInstruction) (name ?target) 
                 (Operands ?a $?))
         (object (is-a AllocaInstruction) (name ?a))
         =>
         (retract ?fct)
         (modify-instance ?i0 (MemoryTarget ?a))
         (assert (element ?p reads from ?a)))
;------------------------------------------------------------------------------
(defrule PopulateBasicBlockWithReadFrom-GetElementPointer-Constant
         "Does a check to see if a given LoadInstruction referring to a
         GetElementPointerInstruction refers to an AllocaInstruction or 
         Constant. If it does then mark it in the ReadsFrom multifield"
         (declare (salience 4))
         (Stage Analysis $?)
         ?fct <- (Analyze ?target for load ?t0)
         ?i0 <- (object (is-a LoadInstruction) (name ?t0) (Parent ?p))
         (object (is-a GetElementPointerInstruction) (name ?target) 
                 (Operands ?a $?))
         (object (is-a Constant) (name ?a))
         =>
         (retract ?fct)
         (modify-instance ?i0 (MemoryTarget ?a))
         (assert (element ?p reads from ?a)))
;------------------------------------------------------------------------------
(defrule IdentifyGeneralLoadBarrier
         "Creates a load memory barrier hint if it turns out that the load 
         instruction in question refers to a register that isn't an 
         AllocaInstruction, GetElementPointerInstruction, or Constant."
         (declare (salience 3))
         (Stage Analysis $?)
         ?fct <- (Analyze ?target for load ?t0)
         ?i0 <- (object (is-a LoadInstruction) (name ?t0) (Parent ?p))
         (object (is-a BasicBlock) (name ?p) (Parent ?r))
         =>
         (retract ?fct)
         (modify-instance ?i0 (MemoryTarget UNKNOWN))
         (assert (element ?p reads from UNKNOWN)
                 (Element ?p has a MemoryBarrier)
                 (Element ?r has a MemoryBarrier)))
;------------------------------------------------------------------------------
(defrule IdentifyGetElementPointerStoreBarrier
         "Creates a store memory barrier hint if it turns out that the store 
         instruction refers to a getelementptr instruction but that 
         getelementptr doesn't refer to a alloca instruction or constant."
         (declare (salience 4))
         (Stage Analysis $?)
         ?fct <- (Analyze ?target for store ?t0)
         ?i0 <- (object (is-a StoreInstruction) (Parent ?p) (name ?t0))
         (object (is-a GetElementPointerInstruction) (name ?target) 
                 (Operands ?a $?))
         (object (is-a ~AllocaInstruction&~Constant) (name ?a))
         (object (is-a BasicBlock) (name ?p) (Parent ?r))
         =>
         (modify-instance ?i0 (MemoryTarget UNKNOWN))
         (retract ?fct)
         (assert (element ?p writes to UNKNOWN)
                 (Element ?p has a MemoryBarrier)
                 (Element ?r has a MemoryBarrier)))
;------------------------------------------------------------------------------
(defrule PopulateBasicBlockWithWriteTo-Alloca
         "Does a check to see if the load instruction refers directly to an
         AllocaInstruction or Constant. If it does then mark it as though the 
         block writes to it"
         (declare (salience 4))
         (Stage Analysis $?)
         ?fct <- (Analyze ?target for store ?t0)
         ?i0 <- (object (is-a StoreInstruction) (name ?t0) (Parent ?p))
         (object (is-a AllocaInstruction) (name ?target))
         =>
         (retract ?fct)
         (modify-instance ?i0 (MemoryTarget ?target))
         (assert (element ?p writes to ?target)))
;------------------------------------------------------------------------------
(defrule PopulateBasicBlockWithWriteTo-Constant
         "Does a check to see if the store instruction refers directly to an
         AllocaInstruction or Constant. If it does then mark it as though the 
         block writes to it"
         (declare (salience 4))
         (Stage Analysis $?)
         ?fct <- (Analyze ?target for store ?t0)
         ?i0 <- (object (is-a StoreInstruction) (name ?t0) (Parent ?p))
         (object (is-a Constant) (name ?target))
         =>
         (retract ?fct)
         (modify-instance ?i0 (MemoryTarget ?target))
         (assert (element ?p writes to ?target)))
;------------------------------------------------------------------------------
(defrule PopulateBasicBlockWithWriteTo-Single-Alloca
         "Does a check to see if the store instruction refers directly to an
         AllocaInstruction or Constant. If it does then mark it as though the 
         block writes to it"
         (declare (salience 4))
         (Stage Analysis $?)
         ?fct <- (Analyze ?target for store ?t0)
         ?i0 <- (object (is-a StoreInstruction) (name ?t0) (Parent ?p))
         (object (is-a AllocaInstruction) (name ?target))
         =>
         (retract ?fct)
         (modify-instance ?i0 (MemoryTarget ?target))
         (assert (element ?p writes to ?target)))
;------------------------------------------------------------------------------
(defrule PopulateBasicBlockWithWriteTo-Single-Constant
         "Does a check to see if the store instruction refers directly to an
         AllocaInstruction or Constant. If it does then mark it as though the 
         block writes to it"
         (declare (salience 4))
         (Stage Analysis $?)
         ?fct <- (Analyze ?target for store ?t0)
         ?i0 <- (object (is-a StoreInstruction) (name ?t0) (Parent ?p))
         (object (is-a Constant) (name ?target))
         =>
         (retract ?fct)
         (modify-instance ?i0 (MemoryTarget ?target))
         (assert (element ?p writes to ?target)))
;------------------------------------------------------------------------------
(defrule PopulateBasicBlockWithWriteTo-GetElementPointer-Alloca
         "Does a check to see if a given StoreInstruction referring to a
         GetElementPointerInstruction refers to an AllocaInstruction or 
         Constant. If it does then mark it in the WritesTo multifield"
         (declare (salience 4))
         (Stage Analysis $?)
         ?fct <- (Analyze ?target for store ?t0)
         ?i0 <- (object (is-a StoreInstruction) (name ?t0) (Parent ?p))
         (object (is-a GetElementPointerInstruction) (name ?target) 
                 (Operands ?a $?))
         (object (is-a AllocaInstruction) (name ?a))
         =>
         (retract ?fct)
         (modify-instance ?i0 (MemoryTarget ?a))
         (assert (element ?p writes to ?a)))
;------------------------------------------------------------------------------
(defrule PopulateBasicBlockWithWriteTo-GetElementPointer-Constant
         "Does a check to see if a given StoreInstruction referring to a
         GetElementPointerInstruction refers to an AllocaInstruction or 
         Constant. If it does then mark it in the WritesTo multifield"
         (declare (salience 4))
         (Stage Analysis $?)
         ?fct <- (Analyze ?target for store ?t0)
         ?i0 <- (object (is-a StoreInstruction) (name ?t0) (Parent ?p))
         (object (is-a GetElementPointerInstruction) (name ?target) 
                 (Operands ?a $?))
         (object (is-a Constant) (name ?a))
         =>
         (retract ?fct)
         (modify-instance ?i0 (MemoryTarget ?a))
         (assert (element ?p writes to ?a)))
;------------------------------------------------------------------------------
(defrule IdentifyGeneralStoreBarrier
         "Creates a store memory barrier hint if it turns out that the load 
         instruction in question refers to a register that isn't an 
         AllocaInstruction, GetElementPointerInstruction, or Constant."
         (declare (salience 3))
         (Stage Analysis $?)
         ?fct <- (Analyze ?target for store ?t0)
         ?i0 <- (object (is-a StoreInstruction) (name ?t0) (Parent ?p))
         (object (is-a BasicBlock) (name ?p) (Parent ?r))
         =>
         (retract ?fct)
         (modify-instance ?i0 (MemoryTarget UNKNOWN))
         (assert (element ?p writes to UNKNOWN)
                 (Element ?p has a MemoryBarrier)
                 (Element ?r has a MemoryBarrier)))
;------------------------------------------------------------------------------
(defrule MergeReadsFrom
         (Stage Analysis $?)
         ?f0 <- (element ?p reads from $?t0)
         ?f1 <- (element ?p reads from $?t1)
         (test (neq ?f0 ?f1))
         =>
         (retract ?f0 ?f1)
         (assert (element ?p reads from $?t0 $?t1)))
;------------------------------------------------------------------------------
(defrule MergeWritesTo
         (Stage Analysis $?)
         ?f0 <- (element ?p writes to $?t0)
         ?f1 <- (element ?p writes to $?t1)
         (test (neq ?f0 ?f1))
         =>
         (retract ?f0 ?f1)
         (assert (element ?p writes to $?t0 $?t1)))
;------------------------------------------------------------------------------
(defrule InsertIntoDiplomatReadsFrom-ParentDoesntExist
         (declare (salience -9))
         (Stage Analysis $?)
         ?fct <- (element ?p reads from $?t)
         ?bb <- (object (is-a Diplomat) (name ?p) (Parent ?q))
         (not (exists (object (is-a Diplomat) (name ?q))))
         =>
         (retract ?fct)
         (slot-insert$ ?bb ReadsFrom 1 ?t))
;------------------------------------------------------------------------------
(defrule InsertIntoDiplomatReadsFrom-ParentExists
         (declare (salience -9))
         (Stage Analysis $?)
         ?fct <- (element ?p reads from $?t)
         ?bb <- (object (is-a Diplomat) 
                        (name ?p)
                        (Parent ?q))
         (object (is-a Diplomat)
                 (name ?q))
         =>
         (retract ?fct)
         (assert (element ?q reads from ?t))
         (slot-insert$ ?bb ReadsFrom 1 ?t))
;------------------------------------------------------------------------------
(defrule InsertIntoDiplomatWritesTo-ParentDoesntExist
         (declare (salience -9))
         (Stage Analysis $?)
         ?fct <- (element ?p writes to $?t)
         ?bb <- (object (is-a Diplomat) (name ?p) (Parent ?q))
         (not (exists (object (is-a Diplomat) (name ?q))))
         =>
         (retract ?fct)
         (slot-insert$ ?bb WritesTo 1 ?t))
;------------------------------------------------------------------------------
(defrule InsertIntoDiplomatWritesTo-ParentExists
         (declare (salience -9))
         (Stage Analysis $?)
         ?fct <- (element ?p writes to $?t)
         ?bb <- (object (is-a Diplomat) (name ?p) (Parent ?q))
         (exists (object (is-a Diplomat) (name ?q)))
         =>
         (retract ?fct)
         (assert (element ?q writes to ?t))
         (slot-insert$ ?bb WritesTo 1 ?t))
;------------------------------------------------------------------------------
(defrule UpdateDiplomatHasMemoryBarrier
         (declare (salience -10))
         (Stage Analysis $?)
         ?fct <- (Element ?b has a MemoryBarrier)
         ?obj <- (object (is-a Diplomat) (name ?b) (HasMemoryBarrier FALSE)
                         (Parent ?p))
         (exists (object (is-a Diplomat) (name ?p)))
         =>
         (retract ?fct)
         (assert (Element ?p has a MemoryBarrier))
         (modify-instance ?obj (HasMemoryBarrier TRUE)))
;------------------------------------------------------------------------------
(defrule RetractDiplomatHasMemoryBarrier
         (declare (salience -10))
         (Stage Analysis $?)
         ?fct <- (Element ?b has a MemoryBarrier)
         ?obj <- (object (is-a Diplomat) (name ?b) (HasMemoryBarrier TRUE)
                         (Parent ?p))
         (exists (object (is-a Diplomat) (name ?p)))
         =>
         (retract ?fct)
         (assert (Element ?p has a MemoryBarrier)))
;------------------------------------------------------------------------------
(defrule UpdateDiplomatHasMemoryBarrier-ParentDoesntExist
         (declare (salience -10))
         (Stage Analysis $?)
         ?fct <- (Element ?b has a MemoryBarrier)
         ?obj <- (object (is-a Diplomat) (name ?b) (HasMemoryBarrier FALSE)
                         (Parent ?p))
         (not (exists (object (is-a Diplomat) (name ?p))))
         =>
         (retract ?fct)
         (modify-instance ?obj (HasMemoryBarrier TRUE)))
;------------------------------------------------------------------------------
(defrule RetractDiplomatHasMemoryBarrier-ParentDoesntExist
         (declare (salience -10))
         (Stage Analysis $?)
         ?fct <- (Element ?b has a MemoryBarrier)
         ?obj <- (object (is-a Diplomat) (name ?b) (HasMemoryBarrier TRUE)
                         (Parent ?p))
         (not (exists (object (is-a Diplomat) (name ?p))))
         =>
         (retract ?fct))
;------------------------------------------------------------------------------
; All of the merge rules used in the analysis stages. Performs analysis to
; identify producers and consumers for all instructions in the provided set of
; scheduling material (regions, functions, etc).
;------------------------------------------------------------------------------
(defrule MergeConsumers
         (Stage ExtendedMemoryAnalysis-Merge $?)
         ?f0 <- (Instruction ?a consumes ?id)
         ?f1 <- (Instruction ?b&~?a consumes ?id)
         =>
         (retract ?f0 ?f1)
         (assert (Instruction ?id consumed ?a ?b)))
;------------------------------------------------------------------------------
(defrule MergeProducers
         (Stage ExtendedMemoryAnalysis-Merge $?)
         ?f0 <- (Instruction ?a produces ?id)
         ?f1 <- (Instruction ?b&~?a produces ?id)
         =>
         (retract ?f0 ?f1)
         (assert (Instruction ?id produced ?a ?b)))
;------------------------------------------------------------------------------
(defrule MergeConsumers-Multi
         (Stage ExtendedMemoryAnalysis-Merge $?)
         ?f0 <- (Instruction ?id consumed $?a)
         ?f1 <- (Instruction ?id consumed $?b)
         (test (neq ?f0 ?f1))
         =>
         (retract ?f0 ?f1)
         (assert (Instruction ?id consumed $?a $?b)))
;------------------------------------------------------------------------------
(defrule MergeProducers-Multi
         (Stage ExtendedMemoryAnalysis-Merge $?)
         ?f0 <- (Instruction ?id produced $?a)
         ?f1 <- (Instruction ?id produced $?b)
         (test (neq ?f0 ?f1))
         =>
         (retract ?f0 ?f1)
         (assert (Instruction ?id produced $?a $?b)))
;------------------------------------------------------------------------------
(defrule MergeConsumers-Only
         (declare (salience -2))
         (Stage ExtendedMemoryAnalysis-Merge $?)
         ?f0 <- (Instruction ?a consumes ?b)
         =>
         (retract ?f0)
         (assert (Instruction ?b consumed ?a)))
;------------------------------------------------------------------------------
(defrule MergeProducers-Only
         (declare (salience -2))
         (Stage ExtendedMemoryAnalysis-Merge $?)
         ?f0 <- (Instruction ?a produces ?b)
         =>
         (retract ?f0)
         (assert (Instruction ?b produced ?a)))
;------------------------------------------------------------------------------
(defrule InjectConsumers-Producers-And-LocalDependencies
         "Performs the actions of InjectConsumers and
         InjectProducersAndLocalDependencies in a single rule fire."
         (declare (salience 1))
         (Stage ExtendedMemoryAnalysis-Inject $?)
         ?f0 <- (Instruction ?id consumed $?t0)
         ?f1 <- (Instruction ?id produced $?t1)
         ?inst <- (object (is-a Instruction) (name ?id) (Consumers $?c) 
                          (Producers $?p) (LocalDependencies $?ld))
         =>
         (retract ?f0 ?f1)
         (bind ?cs $?c)
         (bind ?ps $?p)
         (bind ?lds $?ld)
         (object-pattern-match-delay
           (progn$ (?target ?t0)
                   (if (not (member$ ?target ?cs)) then
                     (bind ?cs (insert$ ?cs 1 ?target))))
           (progn$ (?target ?t1)
                   (if (not (member$ ?target ?lds)) then
                     (bind ?lds (insert$ ?lds 1 ?target)))
                   (if (not (member$ ?target ?ps)) then
                     (bind ?ps (insert$ ?ps 1 ?target))))
           (modify-instance ?inst (Consumers ?cs) (Producers ?ps) 
                            (LocalDependencies ?lds))))
;------------------------------------------------------------------------------
(defrule InjectConsumers
         "Adds a given consumer to the target instruction"
         (Stage ExtendedMemoryAnalysis-Inject $?)
         ?fct <- (Instruction ?id consumed $?targets)
         ?inst <- (object (is-a Instruction) (name ?id) (Consumers $?cs))
         =>
         (retract ?fct)
         (bind ?cons $?cs)
         (object-pattern-match-delay
           (progn$ (?target ?targets)
                   (if (not (member$ ?target ?cons)) then
                     (bind ?cons (insert$ ?cons 1 ?target))))
           (modify-instance ?inst (Consumers ?cons))))
;------------------------------------------------------------------------------
(defrule InjectProducersAndLocalDependencies
         "Adds a given producer to the target instruction."
         (Stage ExtendedMemoryAnalysis-Inject $?)
         ?fct <- (Instruction ?id produced $?targets)
         ?inst <- (object (is-a Instruction) (name ?id) (Producers $?ps)
                          (LocalDependencies $?ld))
         =>
         (retract ?fct)
         (bind ?prods $?ps)
         (bind ?lds $?ld)
         (object-pattern-match-delay
           (progn$ (?target ?targets)
                   (if (not (member$ ?target ?lds)) then
                     (bind ?lds (insert$ ?lds 1 ?target)))
                   (if (not (member$ ?target ?prods)) then
                     (bind ?prods (insert$ ?prods 1 ?target))))
           (modify-instance ?inst (Producers ?prods) (LocalDependencies ?lds))))
;------------------------------------------------------------------------------
(defrule SetifyInstructionProducers
         (Stage ExtendedMemoryAnalysis-MakeSet $?)
         ?inst <- (object (is-a Instruction) (Producers $?a ?b $?c ?b $?d))
         =>
         (modify-instance ?inst (Producers $?a ?b $?c $?d)))
;------------------------------------------------------------------------------
(defrule SetifyInstructionConsumers
         (Stage ExtendedMemoryAnalysis-MakeSet $?)
         ?inst <- (object (is-a Instruction) (Consumers $?a ?b $?c ?b $?d))
         =>
         (modify-instance ?inst (Consumers $?a ?b $?c $?d)))
;------------------------------------------------------------------------------
(defrule SetifyLocalDependencies
         (Stage ExtendedMemoryAnalysis-MakeSet $?)
         ?inst <- (object (is-a Instruction) 
                          (LocalDependencies $?a ?b $?c ?b $?d))
         =>
         (modify-instance ?inst (LocalDependencies $?a ?b $?c $?d)))
;------------------------------------------------------------------------------
(defrule SetifyNonLocalDependencies
         (Stage ExtendedMemoryAnalysis-MakeSet $?)
         ?inst <- (object (is-a Instruction) 
                          (NonLocalDependencies $?a ?b $?c ?b $?d))
         =>
         (modify-instance ?inst (NonLocalDependencies $?a ?b $?c $?d)))
;------------------------------------------------------------------------------
; Rules devoted to starting the construction of ; a given path through a given 
; region.
;------------------------------------------------------------------------------
(defrule StartPathConstruction-NestedEntrance
         (declare (salience 3))
         (Stage Path $?)
         ?r0 <- (object (is-a Region) (CanWavefrontSchedule TRUE) 
                        (Entrances $? ?a $?) (name ?n) (Contents $? ?z $?))
         (object (is-a Region) (name ?z) (Parent ?n) (Entrances $? ?a $?))
         (object (is-a BasicBlock) (name ?a) (Parent ~?n))
         =>
         (make-instance of Path (Parent ?n) (Contents ?z)))
;------------------------------------------------------------------------------
(defrule StartPathConstruction-BasicBlock
         (declare (salience 3))
         (Stage Path $?)
         ?r0 <- (object (is-a Region) (CanWavefrontSchedule TRUE) 
                        (Entrances $? ?a $?) (name ?n))
         (object (is-a BasicBlock) (name ?a) (Parent ?n))
         =>
         (make-instance of Path (Parent ?n) (Contents ?a)))
;------------------------------------------------------------------------------
; Contains rules that add paths that a given block is a part of 
; (path update rules)
;------------------------------------------------------------------------------
(defrule FAIL-UNFINISHED-PATHS 
         (Stage PathUpdate $?)
         (test (> (length$ 
                    (find-all-instances ((?path Path))
                                        (neq TRUE ?path:Closed))) 0))
         =>
         (printout t "ERROR: Not all paths were closed!" crlf)
         (bind ?instances (find-all-instances ((?path Path))
                                              (neq TRUE ?path:Closed))) 
         (foreach ?inst ?instances
                  (send ?inst print))
         (facts)
         (halt))

(defrule AddPathToDiplomat
         "Adds the given path name to the target diplomat"
         (declare (salience 1))
         (Stage Path $?)
         (object (is-a Path) (Closed TRUE) (name ?i) (Contents $? ?b $?))
         ?d <- (object (is-a Diplomat) (name ?b))
         (test (not (member$ ?i (send ?d get-Paths))))
         =>
         (slot-insert$ ?d Paths 1 ?i))

(defrule TraversePathForElementInjection
         (Stage PathUpdate $?)
         (object (is-a Path) (Closed TRUE) (name ?p) (Contents $? ?a ?b $?))
         ?o0 <- (object (is-a Diplomat) (name ?a))
         ?o1 <- (object (is-a Diplomat) (name ?b))
         =>
         (if (not (member$ ?a (send ?o1 get-PreviousPathElements))) then
           (slot-insert$ ?o1 PreviousPathElements 1 ?a))
         (if (not (member$ ?b (send ?o0 get-NextPathElements))) then
           (slot-insert$ ?o0 NextPathElements 1 ?b)))
;------------------------------------------------------------------------------
; Debug rules (display output)
;------------------------------------------------------------------------------
(defrule PrintoutPaths
         (declare (salience -100))
         (Stage Path $?)
         (Debug)
         (Paths)
         (object (is-a Hint) (Type Path) 
                 (Closed TRUE) 
                 (name ?name) 
                 (Contents $?c)
                 (ExitBlock ?eb))
         =>
         (printout t "Path: " ?name " with contents " ?c " with exit block " ?eb crlf))
;------------------------------------------------------------------------------
; PathBuilding - Rules that build up the paths through the given region 
;------------------------------------------------------------------------------
(defrule AddToPath-Copy
         "Makes a copy of the current path object and concatenates the symbol 
         in question to the end of the list. This rule is fired when the 
         reference count of the given path object is greater than one."
         (declare (salience 1))
         (Stage Path $?)
         ?fct <- (Add ?next to ?id)
         ?hint <- (object (is-a Path) (Closed FALSE) (name ?id) (Parent ?p) 
                          (ReferenceCount ?rc&:(> ?rc 1)))
         =>
         (send ?hint .DecrementReferenceCount)
         (retract ?fct)
         (make-instance of Path 
                        (Parent ?p) 
                        (Contents (send ?hint get-Contents) ?next)))
;------------------------------------------------------------------------------
(defrule AddToPath-Concat
         "Concatenates the next element of the path directly to the original 
         path object. This rule fires when the reference count of the path is 
         equal to one"
         (declare (salience 1))
         (Stage Path $?)
         ?fct <- (Add ?next to ?id)
         ?hint <- (object (is-a Path) (Closed FALSE) (name ?id) 
                          (ReferenceCount 1))
         =>
         (retract ?fct)
         (modify-instance ?hint 
                          (ReferenceCount 0) 
                          (Contents (send ?hint get-Contents) ?next)))
;------------------------------------------------------------------------------
(defrule ClosePath-Update
         "Closes a path via an in-place update"
         (declare (salience 1))
         (Stage Path $?)
         ?fct <- (Close ?id with ?bb)
         ?hint <- (object (is-a Path) (Closed FALSE) (name ?id) 
                          (ReferenceCount 1))
         =>
         (retract ?fct)
         (modify-instance ?hint 
                          (ReferenceCount 0) 
                          (Closed TRUE) 
                          (ExitBlock ?bb)))
;------------------------------------------------------------------------------
(defrule ClosePath-Copy
         "Closes a path by making a copy of the target path"
         (declare (salience 1))
         (Stage Path $?)
         ?fct <- (Close ?id with ?bb)
         ?hint <- (object (is-a Path) (Closed FALSE) (name ?id) (Parent ?p)
                          (ReferenceCount ?rc&:(> ?rc 1)))
         =>
         (send ?hint .DecrementReferenceCount)
         (retract ?fct)
         (make-instance of Path 
                        (Closed TRUE) 
                        (ExitBlock ?bb) 
                        (Contents (send ?hint get-Contents))))
;------------------------------------------------------------------------------
; PathTraversal - Rules that handle the act of traversing the region during 
; path construction 
;------------------------------------------------------------------------------
(defrule PathConstruction-BasicBlockToBasicBlock
         (declare (salience 2))
         (Stage Path $?)
         ?path <- (object (is-a Path) (Parent ?p) (name ?id) 
                          (Contents $?before ?curr) 
                          (Closed FALSE))
         (object (is-a BasicBlock) (name ?curr) (Parent ?p) 
                 (Successors $? ?next $?))
         (object (is-a BasicBlock) (name ?next) (Parent ?p))
         (test (not (member$ ?next (create$ $?before ?curr))))
         =>
         (send ?path .IncrementReferenceCount)
         (assert (Add ?next to ?id)))
;------------------------------------------------------------------------------
(defrule PathConstruction-RegionToBasicBlock
         (declare (salience 2))
         (Stage Path $?)
         ?path <- (object (is-a Path) (Closed FALSE) (Parent ?p) (name ?id)
                          (Contents $?before ?curr))
         (object (is-a Region) (name ?curr) (Parent ?p) (Exits $? ?next $?))
         (object (is-a BasicBlock) (name ?next) (Parent ?p))
         (test (not (member$ ?next (create$ $?before ?curr))))
         =>
         (send ?path .IncrementReferenceCount)
         (assert (Add ?next to ?id)))
;------------------------------------------------------------------------------
(defrule PathConstruction-BasicBlockToRegion
         (declare (salience 2))
         (Stage Path $?)
         ?path <- (object (is-a Path) (Closed FALSE) (Parent ?p) (name ?id) 
                          (Contents $?before ?curr))
         (object (is-a BasicBlock) (name ?curr) (Parent ?p) 
                 (Successors $? ?s $?))
         (object (is-a Region) (Entrances $? ?s $?) (name ?next) (Parent ?p))
         (test (not (member$ ?next (create$ $?before ?curr))))
         =>
         (send ?path .IncrementReferenceCount)
         (assert (Add ?next to ?id)))
;------------------------------------------------------------------------------
(defrule PathConstruction-RegionToRegion
         (declare (salience 2))
         (Stage Path $?)
         ?path <- (object (is-a Path) (Closed FALSE) (Parent ?p) (name ?id) 
                          (Contents $?before ?curr))
         (object (is-a Region) (name ?curr) (Parent ?p) (Exits $? ?e $?))
         (object (is-a Region) (name ?next) (Parent ?p) (Entrances $? ?e $?)) 
         (test (not (member$ ?next (create$ $?before ?curr))))
         ; even if the entrance is part of a nested region...we really don't 
         ; care it will still be accurate thanks to the way llvm does things
         =>
         (send ?path .IncrementReferenceCount)
         (assert (Add ?next to ?id)))
;------------------------------------------------------------------------------
(defrule PathConstruction-RegionNoExit
         "We are at a region that doesn't have an exit...Not sure if LLVM 
         allows this but let's handle it."
         (declare (salience 2))
         (Stage Path $?)
         ?path <- (object (is-a Path) (Parent ?p) (name ?i) (Closed FALSE) 
                          (Contents $? ?a))
         (object (is-a Region) (name ?a) (Parent ?p) (Exits))
         =>
         (send ?path .IncrementReferenceCount)
         (assert (Close ?i with nil)))
;------------------------------------------------------------------------------
(defrule PathConstruction-BlockNoExit
         "We are at a basic block that has no successors...usually the end of a
         function"
         (declare (salience 2))
         (Stage Path $?)
         ?path <- (object (is-a Path) (Parent ?p) (name ?i) (Closed FALSE) 
                          (Contents $? ?a))
         (object (is-a BasicBlock) (name ?a) (Parent ?p) (Successors))
         =>
         (send ?path .IncrementReferenceCount)
         (assert (Close ?i with nil)))
;------------------------------------------------------------------------------
(defrule PathConstruction-BasicBlockToBasicBlock-Cycle
         (declare (salience 2))
         (Stage Path $?)
         ?path <- (object (is-a Path) (Parent ?p) (name ?id) 
                          (Contents $?before ?curr) (Closed FALSE))
         (object (is-a BasicBlock) (name ?curr) (Parent ?p) 
                 (Successors $? ?next $?))
         (object (is-a BasicBlock) (name ?next) (Parent ?p))
         (test (member$ ?next (create$ $?before ?curr)))
         =>
         (send ?path .IncrementReferenceCount)
         (assert (Close ?id with ?next)))
;------------------------------------------------------------------------------
(defrule PathConstruction-RegionToBasicBlock-Cycle
         (declare (salience 2))
         (Stage Path $?)
         ?path <- (object (is-a Path) (Closed FALSE) (Parent ?p) (name ?id)
                          (Contents $?before ?curr))
         (object (is-a Region) (name ?curr) (Parent ?p) (Exits $? ?next $?))
         (object (is-a BasicBlock) (name ?next) (Parent ?p))
         (test (member$ ?next (create$ $?before ?curr)))
         =>
         (send ?path .IncrementReferenceCount)
         (assert (Close ?id with ?next)))
;------------------------------------------------------------------------------
(defrule PathConstruction-BasicBlockToRegion-Cycle
         (declare (salience 2))
         (Stage Path $?)
         ?path <- (object (is-a Path) (Closed FALSE) (Parent ?p) (name ?id) 
                          (Contents $?before ?curr))
         (object (is-a BasicBlock) (name ?curr) (Parent ?p) (Successors $? ?s $?))
         (object (is-a Region) (name ?next) (Parent ?p) (Entrances $? ?s $?))
         (test (member$ ?next (create$ $?before ?curr)))
         =>
         (send ?path .IncrementReferenceCount)
         (assert (Close ?id with ?next)))
;------------------------------------------------------------------------------
(defrule PathConstruction-RegionToRegion-Cycle
         (declare (salience 2))
         (Stage Path $?)
         ?path <- (object (is-a Path) (Closed FALSE) (Parent ?p) (name ?id) 
                          (Contents $?before ?curr))
         (object (is-a Region) (name ?curr) (Parent ?p) (Exits $? ?e $?))
         (object (is-a Region) (name ?next) (Parent ?p) (Entrances $? ?e $?)) 
         (test (member$ ?next (create$ $?before ?curr)))
         =>
         (send ?path .IncrementReferenceCount)
         (assert (Close ?next with ?id)))
;------------------------------------------------------------------------------
(defrule PathConstruction-BasicBlockToExit
         "Marks the current path as finished because we've reached an exit to 
         the current region"
         (declare (salience 2))
         (Stage Path $?)
         ?path <- (object (is-a Path) (Parent ?p) (name ?id) (Contents $? ?curr) 
                          (Closed FALSE))
         (object (is-a BasicBlock) (name ?curr) (Parent ?p) (Successors $? ?e $?))
         (object (is-a Region) (name ?p) (Exits $? ?e $?))
         ;since the current block has an exit for this region we mark it
         =>
         (send ?path .IncrementReferenceCount)
         (assert (Close ?id with ?e)))
;------------------------------------------------------------------------------
(defrule PathConstruction-RegionToExit
         (declare (salience 2))
         (Stage Path $?)
         ?path <- (object (is-a Path) (Closed FALSE) (Parent ?p) (name ?id) 
                          (Contents $? ?c))
         (object (is-a Region) (name ?c) (Parent ?p) (Exits $? ?e $?))
         (object (is-a Region) (name ?p) (Exits $? ?e $?))
         ; both the inner and outer regions have the same exit...thus the
         ; curent nested region is a terminator for one path
         =>
         (send ?path .IncrementReferenceCount)
         (assert (Close ?id with ?e)))
;------------------------------------------------------------------------------
; Wavefront Scheduling initialization rules
;------------------------------------------------------------------------------
(defrule InitializeWavefrontSchedulingFacts
         (declare (salience 1001))
         (Stage WavefrontSchedule $?)
         =>
         (assert (Substage Init 
                           Identify 
                           PhiIdentify
                           PhiNode 
                           PhiNodeUpdate
                           Pathing 
                           Strip 
                           Inject 
                           Acquire 
                           Slice 
                           AnalyzeInit 
                           GenerateAnalyze0
                           GenerateAnalyze
                           Analyze 
                           SliceAnalyze
                           MergeInit 
                           Merge 
                           MergeUpdate 
                           ReopenBlocks
                           Ponder
                           Rename 
                           DependencyAnalysis 
                           ;ScheduleObjectCreation 
                           ;ScheduleObjectUsage
                           ;ResetScheduling
                           ;InitLLVMUpdate
                           ;LLVMUpdate 
                           AdvanceInit
                           AdvanceIdentify
                           Advance
                           AdvanceEnd
                           Update)))
;------------------------------------------------------------------------------
(defrule NextWavefrontSchedulingSubstage
         (declare (salience -1000))
         (Stage WavefrontSchedule $?)
         ?fct <- (Substage ? $?rest)
         =>
         (retract ?fct)
         (assert (Substage $?rest)))
;------------------------------------------------------------------------------
(defrule RetractSubstageCompletely
         (declare (salience -1001))
         (Stage WavefrontSchedule $?)
         ?fct <- (Substage)
         =>
         (retract ?fct))
;------------------------------------------------------------------------------
(defrule InitializeWavefrontSchedulingForARegion-SelectBlockDirectly
         (declare (salience 2))
         (Stage WavefrontInit $?)
         (object (is-a Region) (CanWavefrontSchedule TRUE) (name ?r) 
                 (Entrances $? ?e $?))
         (object (is-a BasicBlock) (name ?e) (Parent ?r))
         =>
         (assert (Add ?e to wavefront for ?r)))
;------------------------------------------------------------------------------
(defrule InitializeWavefrontSchedulingForARegion-AssertRegionInstead
         (declare (salience 2))
         (Stage WavefrontInit $?)
         (object (is-a Region) (CanWavefrontSchedule TRUE) (name ?r) 
                 (Entrances $? ?e $?))
         (object (is-a BasicBlock) (name ?e) (Parent ~?r))
         (object (is-a Region) (Parent ?r) (Entrances $? ?e $?) (name ?q))
         =>
         (assert (Add ?q to wavefront for ?r)))
;------------------------------------------------------------------------------
(defrule MergeWavefrontCreationContents-Convert-SingleSingle
         (declare (salience 1))
         (Stage WavefrontInit $?)
         ?f0 <- (Add ?v0 to wavefront for ?r)
         ?f1 <- (Add ?v1 to wavefront for ?r)
         (test (neq ?f0 ?f1))
         =>
         (retract ?f0 ?f1)
         (assert (Create wavefront for ?r containing ?v0 ?v1)))
;------------------------------------------------------------------------------
(defrule MergeWavefrontCreationContents-Convert-MultiSingle
         (declare (salience 1))
         (Stage WavefrontInit $?)
         ?f0 <- (Add ?v0 to wavefront for ?r)
         ?f1 <- (Create wavefront for ?r containing $?g0)

         =>
         (retract ?f0 ?f1)
         (assert (Create wavefront for ?r containing $?g0 ?v0)))
;------------------------------------------------------------------------------
(defrule MergeWavefrontCreationContents-Convert-MultiMulti
         (declare (salience 1))
         (Stage WavefrontInit $?)
         ?f0 <- (Create wavefront for ?r containing $?g0)
         ?f1 <- (Create wavefront for ?r containing $?g1)
         (test (neq ?f0 ?f1))
         =>
         (retract ?f0 ?f1)
         (assert (Create wavefront for ?r containing $?g0 $?g1)))
;------------------------------------------------------------------------------
(defrule ConvertWavefrontCreationFact
         (declare (salience 1))
         (Stage WavefrontInit $?)
         ?f0 <- (Add ?v0 to wavefront for ?r)
         =>
         (retract ?f0)
         (assert (Create wavefront for ?r containing ?v0)))
;------------------------------------------------------------------------------
(defrule ConstructInitialWavefront
         (Stage WavefrontInit $?)
         ?f0 <- (Create wavefront for ?r containing $?w)
         =>
         (retract ?f0)
         (make-instance of Wavefront (Parent ?r) (Contents ?w)))
;------------------------------------------------------------------------------
(defrule ConstructPathAggregateForBlock 
         (declare (salience 100))
         (Stage WavefrontSchedule $?)
         (Substage Init $?)
         (object (is-a Hint) (Type Wavefront) (Parent ?r) (Contents $? ?e $?))
         ?bb <- (object (is-a BasicBlock) (name ?e) (Contents $?c)) 
         =>
         (assert (Propagate aggregates of ?e))
         (make-instance of PathAggregate (Parent ?e) (OriginalStopIndex 
                                                       (- (length$ $?c) 1))))
;------------------------------------------------------------------------------
(defrule ConstructPathAggregateForRegion
         (declare (salience 100))
         (Stage WavefrontSchedule $?)
         (Substage Init $?)
         (object (is-a Hint) (Type Wavefront) (Parent ?r) (Contents $? ?e $?))
         ?bb <- (object (is-a Region) (name ?e)) 
         =>
         (assert (Propagate aggregates of ?e))
         (make-instance of PathAggregate (Parent ?e)))
;------------------------------------------------------------------------------
; Rules to select valid basic blocks for wavefront scheduling within a given 
; region
;------------------------------------------------------------------------------
(defrule AssertIdentifySpansInitial
         (declare (salience 100))
         (Stage WavefrontSchedule $?)
         (Substage Identify $?)
         (object (is-a Hint) (Type Wavefront) (Parent ?r) (Contents $? ?e $?))
         ;select only BasicBlocks
         (object (is-a BasicBlock) (name ?e))
         =>
         (assert (Picked ?e for ?r)))
;------------------------------------------------------------------------------
(defrule IdentifySpanSkips-SplitBlock
         (declare (salience 50))
         (Stage WavefrontSchedule $?)
         (Substage Identify $?)
         ?fct <- (Picked ?e for ?r)
         ?bb <- (object (is-a BasicBlock) (name ?e))
         (test (send ?bb .IsSplitBlock))
         =>
         (retract ?fct)
         (assert (Schedule ?e for ?r)))
;------------------------------------------------------------------------------
(defrule IdentifySpans
         (declare (salience 50))
         (Stage WavefrontSchedule $?)
         (Substage Identify $?)
         ?fct <- (Picked ?e for ?r)
         ?bb <- (object (is-a BasicBlock) (name ?e) (Paths $?paths))
         (test (not (send ?bb .IsSplitBlock)))
         =>
         (retract ?fct)
         (modify-instance ?bb (IsOpen TRUE))
         (assert (Build paths for ?e from $?paths)))
;------------------------------------------------------------------------------
(defrule BuildUpPaths
         (declare (salience 25))
         (Stage WavefrontSchedule $?)
         (Substage Identify $?)
         ?fct <- (Build paths for ?e from ?path $?paths)
         =>
         (retract ?fct)
         (assert (Build paths for ?e from $?paths)
                 (Check path ?path for block ?e)))
;------------------------------------------------------------------------------
(defrule RetractPathBuildUp
         (Stage WavefrontSchedule $?)
         (Substage Identify $?)
         ?fct <- (Build paths for ? from)
         =>
         (retract ?fct))
;------------------------------------------------------------------------------
(defrule GetFactsBeforePathing
         (declare (salience 10000))
         (Debug)
         (Facts)
         (Stage WavefrontSchedule $?)
         (Substage Pathing $?)
         =>
         (printout t "BEFORE: Wavefront Pathing " crlf crlf)
         (facts)
         (printout t crlf crlf))
;------------------------------------------------------------------------------
(defrule DispatchDivideBlock
         (declare (salience 200))
         (Stage WavefrontSchedule $?)
         (Substage Pathing $?)
         ?fct <- (Check path ?p for block ?e)
         (object (is-a Path) (name ?p) (Contents $? ?e $?rest))
         (object (is-a BasicBlock) (name ?e))
         =>
         (retract ?fct)
         (assert (Scan path ?p for block ?e with contents $?rest)))
;------------------------------------------------------------------------------
(defrule AnalyzePathElements
         (Stage WavefrontSchedule $?)
         (Substage Pathing $?)
         ?fct <- (Scan path ?p for block ?e with contents ?curr $?rest)
         ?bb <- (object (is-a BasicBlock) (name ?curr))
         =>
         (retract ?fct)
         (if (= 0 (length$ (send ?bb get-Successors))) then
           (assert (CompletelyInvalid blocks for ?e are ?curr))
           (return))
         (if (send ?bb .IsSplitBlock) then
           (assert (CompletelyInvalid blocks for ?e are $?rest)
                   (PotentiallyValid blocks for ?e are ?curr))
           (return))
         (if (send ?bb get-HasCallBarrier) then
           (assert (CompletelyInvalid blocks for ?e are $?rest)
                   (PotentiallyValid blocks for ?e are ?curr))
           (return))
         (if (send ?bb get-HasMemoryBarrier) then
           (assert (Element ?curr has a MemoryBarrier for ?e)))
         (assert (PotentiallyValid blocks for ?e are ?curr)
                 (Scan path ?p for block ?e with contents $?rest)))
;------------------------------------------------------------------------------
(defrule AnalyzePathElements-Region
         (Stage WavefrontSchedule $?)
         (Substage Pathing $?)
         ?fct <- (Scan path ?p for block ?e with contents ?curr $?rest)
         ?bb <- (object (is-a Region) (name ?curr))
         =>
         (retract ?fct)
         (if (send ?bb get-HasCallBarrier) then
           (assert (CompletelyInvalid blocks for ?e are $?rest)
                   (PotentiallyValid blocks for ?e are ?curr))
           (return))
         (if (send ?bb get-HasMemoryBarrier) then
           (assert (Element ?curr has a MemoryBarrier for ?e)))
         (assert (PotentiallyValid blocks for ?e are ?curr)
                 (Scan path ?p for block ?e with contents $?rest)))
;------------------------------------------------------------------------------
(defrule RetractCompletedFact
         (Stage WavefrontSchedule $?)
         (Substage Strip $?)
         ?fct <- (Scan path ? for block ? with contents)
         =>
         (retract ?fct))
;------------------------------------------------------------------------------
(defrule PrintoutCompletedFacts 
         (declare (salience -999))
         (Debug)
         (Facts)
         (Stage WavefrontSchedule $?)
         (Substage Pathing $?)
         =>
         (printout t "AFTER: Wavefront Pathing" crlf crlf)
         (facts)
         (printout t crlf crlf))
;------------------------------------------------------------------------------
(defrule FAIL-PATHS-EXIST
         (declare (salience -2500))
         (Stage WavefrontSchedule $?)
         (Substage Strip $?)
         (Check path ?p for block ?e)
         =>
         (printout t "ERROR: DIDN'T RETRACT COMPLETED FACT: (Check path " ?p 
                   " for block " ?e ")" crlf)
         (facts)
         (halt))
;------------------------------------------------------------------------------
; Bulk fo the wavefront scheduling rules
;
;
;
; The idea for wavefront scheduling is that we pull a region, construct
; schedules for all of the blocks within the region, identify blocks that can
; relinquish control over instructions and move them up and out of the given
; block and into blocks on the wavefront.
;------------------------------------------------------------------------------
(defrule MergePotentiallyValidBlocks
         (declare (salience 2))
         (Stage WavefrontSchedule $?)
         (Substage Strip $?)
         ?pv0 <- (PotentiallyValid blocks for ?e are $?t)
         ?pv1 <- (PotentiallyValid blocks for ?e are $?q)
         (test (and (neq ?pv0 ?pv1) (subsetp ?t ?q)))
         =>
         (retract ?pv0 ?pv1)
         ;make sure that we get matches again!
         (assert (PotentiallyValid blocks for ?e are $?q)))
;------------------------------------------------------------------------------
(defrule MergeMemoryPotentiallyValidBlocks
         (Stage WavefrontSchedule $?)
         (Substage Strip $?)
         ?pv0 <- (MemoryPotentiallyValid blocks for ?e are $?t)
         ?pv1 <- (MemoryPotentiallyValid blocks for ?e are $?q)
         (test (and (neq ?pv0 ?pv1) (subsetp ?t ?q)))
         =>
         (retract ?pv0 ?pv1)
         ;make sure that we get matches again!
         (assert (MemoryPotentiallyValid blocks for ?e are $?q)))
;------------------------------------------------------------------------------
(defrule MergeCompletelyInvalid
         (declare (salience 1))
         (Stage WavefrontSchedule $?)
         (Substage Strip $?)
         ?pv0 <- (CompletelyInvalid blocks for ?e are $?t)
         ?pv1 <- (CompletelyInvalid blocks for ?e are $?q)
         (test (and (neq ?pv0 ?pv1) (subsetp ?t ?q)))
         =>
         (retract ?pv0 ?pv1)
         (assert (CompletelyInvalid blocks for ?e are $?q)))
;------------------------------------------------------------------------------
(defrule RetractPotentiallyValidBlocksThatAreCompletelyEnclosed
         (Stage WavefrontSchedule $?)
         (Substage Strip $?)
         (CompletelyInvalid blocks for ?e are $?t)
         ?pv1 <- (PotentiallyValid blocks for ?e are $?q)
         (test (subsetp ?q ?t))
         =>
         (retract ?pv1))
;------------------------------------------------------------------------------
(defrule StripoutIndividualElementsFromPotentiallyValid
         (declare (salience -1))
         (Stage WavefrontSchedule $?)
         (Substage Strip $?)
         ?f0 <- (PotentiallyValid blocks for ?e are $?before ?car $?rest)
         (CompletelyInvalid blocks for ?e are $? ?car $?)
         =>
         (retract ?f0)
         (assert (PotentiallyValid blocks for ?e are $?before $?rest)))
;------------------------------------------------------------------------------
(defrule RetractEmptyPotentiallyValid
         (declare (salience -100))
         (Stage WavefrontSchedule $?)
         (Substage Strip $?)
         ?f0 <- (PotentiallyValid blocks for ? are)
         =>
         (retract ?f0))
;------------------------------------------------------------------------------
(defrule InjectPotentiallyValidBlocks-Complete
         (Stage WavefrontSchedule $?)
         (Substage Inject $?)
         ?fct <- (PotentiallyValid blocks for ?e are $?blocks)
         ?pa <- (object (is-a PathAggregate) (Parent ?e) 
                        (PotentiallyValid $?pv))
         =>
         (retract ?fct)
         (bind ?pvs $?pv)
         (bind ?newIndex (+ (length$ ?pv) 1))
         (progn$ (?block ?blocks)
                 (if (not (member$ ?block ?pvs)) then 
                   (bind ?pvs (insert$ ?pvs ?newIndex ?block))
                   (bind ?newIndex (+ ?newIndex 1))))
         (modify-instance ?pa (PotentiallyValid ?pvs)))
;------------------------------------------------------------------------------
(defrule InjectCompletelyInvalidBlocks-Complete
         (Stage WavefrontSchedule $?)
         (Substage Inject $?)
         ?fct <- (CompletelyInvalid blocks for ?e are $?blocks)
         ?pa <- (object (is-a PathAggregate) (Parent ?e) 
                        (CompletelyInvalid $?ci))
         =>
         (retract ?fct)
         (bind ?cis $?ci)
         (bind ?newIndex (+ 1 (length$ ?ci)))
         (progn$ (?block ?blocks)
                 (if (not (member$ ?block ?cis)) then 
                   (bind ?cis (insert$ ?cis ?newIndex ?block))
                   (bind ?newIndex (+ 1 ?newIndex))))
         (modify-instance ?pa (CompletelyInvalid ?cis)))
;------------------------------------------------------------------------------
(defrule InterleavedInjectCompletelyInvalid-AndPotentiallyInvalidBlocks
         (declare (salience 1))
         (Stage WavefrontSchedule $?)
         (Substage Inject $?)
         ?f0 <- (CompletelyInvalid blocks for ?e are $?b0)
         ?f1 <- (PotentiallyValid blocks for ?e are $?b1)
         ?pa <- (object (is-a PathAggregate) (Parent ?e)
                        (CompletelyInvalid $?ci)
                        (PotentiallyValid $?pv))
         =>
         (retract ?f0 ?f1)
         (bind ?cis $?ci)
         (bind ?pvs $?pv)
         (bind ?i0 (+ 1 (length$ ?ci)))
         (bind ?i1 (+ 1 (length$ ?pv)))
         (progn$ (?b ?b0)
                 (if (not (member$ ?b ?cis)) then
                   (bind ?cis (insert$ ?cis ?i0 ?b))
                   (bind ?i0 (+ ?i0 1))))
         (progn$ (?b ?b1)
                 (if (not (member$ ?b ?pvs)) then
                   (bind ?pvs (insert$ ?pvs ?i1 ?b))
                   (bind ?i1 (+ ?i1 1))))
         (modify-instance ?pa (CompletelyInvalid ?cis) 
                          (PotentiallyValid ?pvs)))
;------------------------------------------------------------------------------
(defrule InjectMemoryBarrierBlocks 
         (Stage WavefrontSchedule $?)
         (Substage Inject $?)
         ;get the Mrs. Hitler birth certificate
         ?fct <- (Element ?t has a MemoryBarrier for ?e)
         ?pa <- (object (is-a PathAggregate) (Parent ?e))
         =>
         (retract ?fct)
         (if (not (member$ ?t (send ?pa get-MemoryBarriers))) then
           (slot-insert$ ?pa MemoryBarriers 1 ?t)))
;------------------------------------------------------------------------------
(defrule InjectCallBarrierBlocks 
         (Stage WavefrontSchedule $?)
         (Substage Inject $?)
         ;get the Mrs. Hitler birth certificate
         ?fct <- (Element ?t has a CallBarrier for ?e)
         ?pa <- (object (is-a PathAggregate) (Parent ?e))
         =>
         (retract ?fct)
         (if (not (member$ ?t (send ?pa get-CallBarriers))) then
           (slot-insert$ ?pa CallBarriers 1 ?t)))
;------------------------------------------------------------------------------
; now that we have a path aggregate we need to get the list of instruction
; CPV's that represent valid movable instructions for the given block on the
; wavefront. 
;------------------------------------------------------------------------------
(defrule SelectValidCPVs 
         (Stage WavefrontSchedule $?)
         (Substage Acquire $?)
         (object (is-a Wavefront) (Parent ?r) (Contents $? ?e $?))
         (object (is-a BasicBlock) (name ?e) (IsOpen TRUE))
         ?pa <- (object (is-a PathAggregate) (name ?ag) (Parent ?e)
                        (PotentiallyValid $?pv))
         =>
         (assert (For ?e find CPVs for $?pv)))
;------------------------------------------------------------------------------
(defrule FindValidCPVsForBlock
         (Stage WavefrontSchedule $?)
         (Substage Acquire $?)
         ?fct <- (For ?e find CPVs for ?pv $?pvs)
         (object (is-a BasicBlock) (name ?pv) (Contents $?instructions))
         =>
         (retract ?fct)
         (assert (For ?e find CPVs for $?pvs)
                 (Get CPVs out of ?pv for ?e using $?instructions)))
;------------------------------------------------------------------------------
(defrule SkipRegionsForFindingValidCPVsForBlock
         (Stage WavefrontSchedule $?)
         (Substage Acquire $?)
         ?fct <- (For ?e find CPVs for ?pv $?pvs)
         (object (is-a Region) (name ?pv)) 
         =>
         (retract ?fct)
         (assert (For ?e find CPVs for $?pvs)))
;------------------------------------------------------------------------------
(defrule RetractValidCPVsForBlock
         (Stage WavefrontSchedule $?)
         (Substage Acquire $?)
         ?fct <- (For ? find CPVs for)
         =>
         (retract ?fct))
;------------------------------------------------------------------------------
(defrule IgnorePHIInstructions
         (declare (salience 1))
         (Stage WavefrontSchedule $?)
         (Substage Acquire $?)
         ?fct <- (Get CPVs out of ?pv for ?e using ?inst $?insts)
         (object (is-a PhiNode) (name ?inst))
         =>
         (retract ?fct)
         (assert (Get CPVs out of ?pv for ?e using $?insts)))
;------------------------------------------------------------------------------
(defrule IgnoreCallInstructions
         (declare (salience 1))
         (Stage WavefrontSchedule $?)
         (Substage Acquire $?)
         ?fct <- (Get CPVs out of ?pv for ?e using ?inst $?insts)
         (object (is-a CallInstruction) (name ?inst))
         =>
         (retract ?fct)
         (assert (Get CPVs out of ?pv for ?e using $?insts)))
;------------------------------------------------------------------------------
(defrule IgnoreTerminatorInstructions
         (declare (salience 1))
         (Stage WavefrontSchedule $?)
         (Substage Acquire $?)
         ?fct <- (Get CPVs out of ?pv for ?e using ?inst $?insts)
         (object (is-a TerminatorInstruction) (name ?inst))
         =>
         (retract ?fct)
         (assert (Get CPVs out of ?pv for ?e using $?insts)))
;------------------------------------------------------------------------------
(defrule DisableInstructionsDependentOnDestinationPhis
         (declare (salience 2))
         (Stage WavefrontSchedule $?)
         (Substage Acquire $?)
         ?fct <- (Get CPVs out of ?pv for ?e using ?inst $?insts)
         ;make sure that the parent block is the same
         (object (is-a Instruction) (name ?inst) (Parent ?p) 
                 (DestinationRegisters $? ?reg $?))
         (object (is-a PhiNode) (name ?reg) (Parent ?p))
         =>
         (retract ?fct)
         (assert (Get CPVs out of ?pv for ?e using $?insts)))
;------------------------------------------------------------------------------
(defrule DisableInstructionsDependentOnLocalPhis
         (declare (salience 2))
         (Stage WavefrontSchedule $?)
         (Substage Acquire $?)
         ?fct <- (Get CPVs out of ?pv for ?e using ?inst $?insts)
         ;make sure that the parent block is the same 
         (object (is-a Instruction) (name ?inst) (LocalDependencies $? ?reg $?))
         (object (is-a PhiNode) (name ?reg))
         =>
         (retract ?fct)
         (assert (Get CPVs out of ?pv for ?e using $?insts)))
;------------------------------------------------------------------------------
(defrule TagValidCPVs
         (Stage WavefrontSchedule $?)
         (Substage Acquire $?)
         ?fct <- (Get CPVs out of ?pv for ?e using ?inst $?insts)
         ?i <- (object (is-a Instruction) (name ?inst) (IsTerminator FALSE) 
                       (HasCallDependency FALSE))
         =>
         (retract ?fct)
         (assert (Get CPVs out of ?pv for ?e using $?insts)
                 (Marked ?inst as valid for block ?e)))
;------------------------------------------------------------------------------
(defrule RetractDrainedGetCPVFacts
         (Stage WavefrontSchedule $?)
         (Substage Acquire $?)
         ?fct <- (Get CPVs out of ?pv for ?e using)
         =>
         (retract ?fct))
;------------------------------------------------------------------------------
(defmessage-handler PathAggregate add-instructions-if-not-member primary
                    ($?elements)
                    (progn$ (?a ?elements)
                            (if (not (member$ ?a ?self:InstructionList)) then
                              (slot-direct-insert$ InstructionList
                                                   1
                                                   ?a))))
(defmessage-handler PathAggregate add-scheduled-instructions-if-not-member primary
                    ($?elements)
                    (progn$ (?a ?elements)
                            (if (not (member$ ?a ?self:ScheduledInstructions)) then
                              (slot-direct-insert$ ScheduledInstructions
                                                   1
                                                   ?a))))

(defrule ReloadCPVIntoNewAggregate
         "Put the CPV that has already been created into the target path 
         aggregate"
         (Stage WavefrontSchedule $?)
         (Substage Acquire $?)
         ?fct <- (Marked ?inst as valid for block ?e)
         (object (is-a CompensationPathVector) 
                 (Parent ?inst) 
                 (name ?cpvID))
         (object (is-a PathAggregate) 
                 (name ?ag) 
                 (Parent ?e)
                 (ImpossibleCompensationPathVectors $?icpv&:(not (member$ ?cpvID 
                                                                          ?icpv))))
         (object (is-a Instruction) 
                 (name ?inst) 
                 (NonLocalDependencies $?nlds)
                 (DestinationRegisters ?reg))
         =>
         (retract ?fct)
         (send ?ag
               add-instructions-if-not-member 
               ?inst
               ?reg)
         (send ?ag
               add-scheduled-instructions-if-not-member
               $?nlds)
         (slot-insert$ ?ag
                       CompensationPathVectors 
                       1 
                       ?cpvID))
;------------------------------------------------------------------------------
(defrule CPVIsImpossible
         (Stage WavefrontSchedule $?)
         (Substage Acquire $?)
         ?fct <- (Marked ?inst as valid for block ?e)
         (object (is-a CompensationPathVector) 
                 (Parent ?inst) 
                 (name ?cpvID))
         (object (is-a PathAggregate) 
                 (Parent ?e)
                 (name ?ag)
                 (ImpossibleCompensationPathVectors $?icpv&:(not (member$ ?cpvID
                                                                          ?icpv))))
         (object (is-a Instruction) 
                 (name ?inst) 
                 (NonLocalDependencies $?nlds))
         =>
         (retract ?fct)
         ;add the non-local dependencies
         (send ?ag
               add-scheduled-instructions-if-not-member
               $?nlds))

;------------------------------------------------------------------------------
(defrule MakeCPV 
         (Stage WavefrontSchedule $?)
         (Substage Acquire $?)
         ?fct <- (Marked ?inst as valid for block ?e)
         (not (exists (object (is-a CompensationPathVector) 
                              (Parent ?inst))))
         (object (is-a PathAggregate) 
                 (Parent ?e)
                 (name ?ag))
         (object (is-a Instruction) 
                 (name ?inst) 
                 (Parent ?pv) 
                 (DestinationRegisters ?reg) 
                 (NonLocalDependencies $?nlds))
         (object (is-a BasicBlock) 
                 (name ?pv) 
                 (Paths $?paths))
         =>
         ; We need to disable the stores from moving when their dependencies
         ; 
         ; YOU DON'T EVEN WANT TO KNOW WHAT I'M GOING TO DO TO YOU
         (retract ?fct)
         (bind ?name 
               (gensym*))
         (slot-insert$ ?ag
                       CompensationPathVectors 
                       1
                       (bind ?name
                             (make-instance of CompensationPathVector
                                            (Parent ?inst)
                                            (Paths $?paths)
                                            (OriginalBlock ?pv))))
         (send ?ag 
               add-instructions-if-not-member
               ?inst
               ?reg)
         (send ?ag 
               add-scheduled-instructions-if-not-member
               ?nlds))
;------------------------------------------------------------------------------
; Now we go through and attempt to schedule the instruction represented by 
; each CPV into the block on the wavefront. I call this stage merge. I had some
; far raunchier names but this is my thesis. Some of the potential names were
; OneeChanTheresNoWayThatCanFit, ImAMexiCan, Copulation, and many more.
; 
; I guess the biggest question would be why? And my answer would be why not?
; These terms just popped into my head.
;------------------------------------------------------------------------------
(defrule SetifyInstructionList
         (Stage WavefrontSchedule $?)
         (Substage Slice $?)
         ?pa <- (object (is-a PathAggregate) (InstructionList $?a ?b $?c ?b $?d))
         =>
         (modify-instance ?pa (InstructionList $?a ?b $?c $?d)))
;------------------------------------------------------------------------------
(defrule GenerateInitialSliceFactsForElementsOnTheWavefront 
         (Stage WavefrontSchedule $?)
         (Substage Slice $?)
         (object (is-a Wavefront) (Parent ?r) (Contents $? ?e $?))
         (object (is-a BasicBlock) (name ?e) (IsOpen TRUE))
         (object (is-a PathAggregate) (Parent ?e) 
                 (CompensationPathVectors $?cpv))
         (test (> (length$ ?cpv) 0))
         =>
         (assert (Generate slices for block ?e in ?r using $?cpv)))
;------------------------------------------------------------------------------
(defrule GenerateFactForSlicesFromCPV
         (Stage WavefrontSchedule $?)
         (Substage Slice $?)
         ?fct <- (Generate slices for block ?e in ?r using ?cpv $?cpvs)
         (object (is-a CompensationPathVector) (name ?cpv) (Parent ?i)
                 (Paths $?paths))
         (object (is-a Instruction) (name ?i) (Parent ?b))
         =>
         (retract ?fct)
         (assert (Generate slices for block ?e in ?r using $?cpvs)
                 (Generate slices for block ?e in ?r with cpv ?cpv with stop 
                           block ?b using paths $?paths)))
;------------------------------------------------------------------------------
(defrule RetractEmptySlicesCreationFact
         (Stage WavefrontSchedule $?)
         (Substage Slice $?)
         ?fct <- (Generate slices for block ? in ? using)
         =>
         (retract ?fct))
;------------------------------------------------------------------------------
(defrule QueryCanCreateSliceForPath
         (Stage WavefrontSchedule $?)
         (Substage Slice $?)
         ?fct <- (Generate slices for block ?e in ?r with cpv ?cpv with stop 
                           block ?b using paths ?path $?paths)
         (object (is-a Path) (name ?path) (Contents $? ?e $?))
         ;(test (member$ ?e ?z))
         =>
         (retract ?fct)
         (assert (Generate slice for block ?e in ?r with cpv ?cpv with stop 
                           block ?b using path ?path)
                 (Generate slices for block ?e in ?r with cpv ?cpv with stop 
                           block ?b using paths $?paths)))
;------------------------------------------------------------------------------
(defrule QueryCantCreateSliceForPath
         (Stage WavefrontSchedule $?)
         (Substage Slice $?)
         ?fct <- (Generate slices for block ?e in ?r with cpv ?cpv with stop 
                           block ?b using paths ?path $?paths)
         (object (is-a Path) (name ?path) (Contents $?z))
         (test (not (member$ ?e ?z)))
         =>
         (retract ?fct)
         (assert (Generate slices for block ?e in ?r with cpv ?cpv with stop 
                           block ?b using paths $?paths)))
;------------------------------------------------------------------------------
(defrule TryConstructNewSlice
         (Stage WavefrontSchedule $?)
         (Substage Slice $?)
         ?fct <- (Generate slice for block ?e in ?r with cpv ?cpv with stop 
                           block ?b using path ?path)
         (not (exists (object (is-a Slice) (Parent ?b) (TargetPath ?path) 
                              (TargetBlock ?e))))
         (object (is-a Path) (name ?path) (Contents $? ?e $?slice ?b $?))
         =>
         (retract ?fct)
         (make-instance (gensym*) of Slice (Parent ?b) (TargetPath ?path)
                        (TargetBlock ?e) (Contents $?slice)))
;------------------------------------------------------------------------------
(defrule SliceAlreadyExists
         (Stage WavefrontSchedule $?)
         (Substage Slice $?)
         ?fct <- (Generate slice for block ?e in ?r with cpv ?cpv with stop 
                           block ?b using path ?path)
         (exists (object (is-a Slice) (Parent ?b) (TargetPath ?path) 
                         (TargetBlock ?e)))
         =>
         (retract ?fct))
;------------------------------------------------------------------------------
(defrule RemoveSliceAnalysisFact
         (Stage WavefrontSchedule $?)
         (Substage Slice $?)
         ?fct <- (Generate slices for block ? in ? with cpv ? with stop block ? 
                           using paths)
         =>
         (retract ?fct))
;------------------------------------------------------------------------------
;only construct slices as we see fit as we can just reference them again.
;------------------------------------------------------------------------------
; Now that we have slices constructed it's time to run through the
; analyze-merge cycle. First up, analyze. In this phase we need to see if it
; is possible to schedule into the block. Actually, I can see that we already
; did the hard work as any regions that would have prevented code from moving
; up would have already prevented the block from being selected. Thus we should
; just check to see if we have a local dependency
;------------------------------------------------------------------------------
(defrule InitialCPVSetupForPathAggregate
         "Load all of the compensation path vectors for the given path 
         aggregate into the aggregates TargetCompensationPathVectors 
         multifield"
         (Stage WavefrontSchedule $?)
         (Substage AnalyzeInit $?)
         (object (is-a Wavefront) (Contents $? ?blkID $?))
         ?agObj <- (object (is-a PathAggregate) (Parent ?blkID) 
                           (CompensationPathVectors $?cpvIDs))
         (test (> (length$ ?cpvIDs) 0))
         =>
         (modify-instance ?agObj (TargetCompensationPathVectors $?cpvIDs)))
;------------------------------------------------------------------------------
(defrule SetifyTargetCompensationPathVectors
         (Stage WavefrontSchedule $?)
         (Substage AnalyzeInit $?)
         ?pa <- (object (is-a PathAggregate) 
                        (TargetCompensationPathVectors $?a ?b $?c ?b $?d))
         =>
         (modify-instance ?pa (TargetCompensationPathVectors $?a ?b $?c $?d)))
;------------------------------------------------------------------------------
(defrule SelectCPVForAnalysis
         (Stage WavefrontSchedule $?)
         (Substage GenerateAnalyze0 $?)
         (object (is-a Wavefront) (Parent ?r) (Contents $? ?e $?))
         ?bb <- (object (is-a BasicBlock) (name ?e) (IsOpen TRUE))
         ;(not (exists (Schedule ?e for ?r)))
         ?agObj <- (object (is-a PathAggregate) (Parent ?e) 
                           (TargetCompensationPathVectors $?cpvs))
         (test (> (length$ ?cpvs) 0))
         =>
         ;clear out the cpvs
         (modify-instance ?agObj (TargetCompensationPathVectors))
         (bind ?result (create$))
         (progn$ (?cpv $?cpvs)
                 (bind ?det FALSE)
                 (progn$ (?p (send (symbol-to-instance-name ?cpv) get-Paths))
                         (if ?det then 
                           (break)
                           else 
                           (bind ?o2 (symbol-to-instance-name ?p))
                           (bind ?det 
                                 (or ?det 
                                     (member$ ?e 
                                              (send ?o2 get-Contents))))))
                 (if ?det then 
                   (bind ?result (create$ ?result ?cpv))))
         (assert (Analyze block ?e for ?r using cpvs $?result)))
;------------------------------------------------------------------------------
(defrule SegmentCPVsApart
         (Stage WavefrontSchedule $?)
         (Substage GenerateAnalyze $?)
         ?fct <- (Analyze block ?e for ?r using cpvs ?cpv $?cpvs)
         (object (is-a BasicBlock) (name ?e))
         (object (is-a CompensationPathVector) (name ?cpv) (Parent ?i))
         =>
         ;(printout t "Analyze instruction " ?i " { associated cpv " ?cpv 
         ; " } for " ?e crlf)
         (retract ?fct)
         (assert (Analyze block ?e for ?r using cpvs $?cpvs)
                 (Analyze instruction ?i { associated cpv ?cpv } for ?e)))
;------------------------------------------------------------------------------
(defrule RetractCPVSegmentationFact
         (Stage WavefrontSchedule $?)
         (Substage GenerateAnalyze $?)
         ?fct <- (Analyze block ? for ? using cpvs)
         =>
         (retract ?fct))
;------------------------------------------------------------------------------
(defrule TargetInstructionDoesNotHaveACorrespondingCPV
         "Sometimes it turns out that sometimes store instructions will add 
         certain instructions to the instruction list even though they don't 
         have a valid CPV.  This rule removes those elements from the path 
         aggregate"
         (Stage WavefrontSchedule $?)
         (Substage GenerateAnalyze $?)
         ?pa <- (object (is-a PathAggregate) (Parent ?e) 
                        (InstructionList $?b ?a $?c))
         (not (exists (object (is-a CompensationPathVector) (Parent ?a))))
         =>
         ;(printout t "NOTE: Removed " ?a " from the path aggregate of " ?e 
         ;            " because a CPV wasn't tied to the instruction" crlf)
         (modify-instance ?pa (InstructionList $?b $?c)))
;------------------------------------------------------------------------------
(defrule TargetInstructionIsNotRegisteredWithTheTargetPathAggregate
         "Sometimes it turns out that sometimes store instructions will add 
         certain instructions to the instruction list even though they don't 
         have a valid CPV registered with the path aggregate. This rule removes 
         those elements from the path aggregate"
         (Stage WavefrontSchedule $?)
         (Substage GenerateAnalyze $?)
         ?pa <- (object (is-a PathAggregate) (Parent ?e) 
                        (InstructionList $?b ?a $?c)
                        (CompensationPathVectors $?cpvs))
         (object (is-a CompensationPathVector) (Parent ?a) (name ?id))
         (test (not (member$ ?id $?cpvs)))
         =>
         ;(printout t "NOTE: Removed " ?a " from the path aggregate of " ?e 
         ;" because the corresponding CPV wasn't registered with the path"
         ;" aggregate" crlf)
         (modify-instance ?pa (InstructionList $?b $?c)))
;------------------------------------------------------------------------------
(defrule TargetCPVIsImpossibleToScheduleIntoTargetBlock
         (Stage WavefrontSchedule $?)
         (Substage Analyze $?)
         ?fct <- (Analyze instruction ?i { associated cpv ?cpv } for ?e)
         ?agObj <- (object (is-a PathAggregate) (Parent ?e) 
                           (InstructionList $?il)
                           (ScheduledInstructions $?sched))
         (object (is-a Instruction) (name ?i) (LocalDependencies $?ld)
                 (NonLocalDependencies $?nld))
         (test (not (and (subsetp ?ld ?il)
                         (subsetp ?nld ?sched))))
         =>
         ;(printout t ?i " is impossible to schedule into " ?e crlf)
         ;(printout t "Local Dependencies = " ?ld crlf)
         ;(printout t "Non Local Dependencies = " ?nld crlf)
         ;(printout t "Instruction List = " ?il crlf)
         ;(printout t "Schedule = " ?sched crlf)
         (retract ?fct)
         (bind ?ind (member$ ?i ?il))
         (if ?ind then
           (slot-delete$ ?agObj InstructionList ?ind ?ind))
         (assert (Cant schedule ?cpv for ?e ever)))
;------------------------------------------------------------------------------

(defrule TargetCPVCantBeScheduledIntoTargetBlockYet
         (Stage WavefrontSchedule $?)
         (Substage Analyze $?)
         ?fct <- (Analyze instruction ?i { associated cpv ?cpv } for ?e)
         ?paObj <- (object (is-a PathAggregate) (Parent ?e) 
                           (InstructionList $?il)
                           (ScheduledInstructions $?sched)
                           (CompensationPathVectors $?cpvs))
         (object (is-a Instruction) (name ?i) (LocalDependencies $?ld) 
                 (NonLocalDependencies $?nld) (Parent ?parent))
         (test (and (not (subsetp ?ld ?sched))
                    (subsetp ?ld ?il)
                    (subsetp ?nld ?sched)))
         =>
         ;(printout t "Can't schedule " ?i " into " ?e " right now!" crlf)
         ;(printout t "Non Local Dependencies = " ?nld crlf)
         ;(printout t "Local Dependencies = " ?ld crlf)
         ;(printout t "Scheduled = " ?sched crlf)
         ;(printout t "Instruction List = " ?il crlf)
         ;(printout t "From = " ?parent crlf)
         ;(printout t "CPVS = " ?cpvs crlf)
         ;(facts)
         (retract ?fct)
         (assert (Cant schedule ?cpv for ?e now)))
;------------------------------------------------------------------------------
(defrule TargetCPVNeedsToBeSliceAnalyzed
         (Stage WavefrontSchedule $?)
         (Substage Analyze $?)
         ?fct <- (Analyze instruction ?i { associated cpv ?cpv } for ?e)
         (object (is-a PathAggregate) (Parent ?e) 
                 (ScheduledInstructions $?sched))
         (object (is-a Instruction) (name ?i) (Parent ?b) 
                 (LocalDependencies $?ld))
         (test (subsetp ?ld ?sched))
         (object (is-a CompensationPathVector) (name ?cpv) (Paths $?paths))
         =>
         (retract ?fct)
         (bind ?validPaths (create$))
         (foreach ?z ?paths
                  (bind ?obj (instance-name (symbol-to-instance-name ?z)))
                  (if (member$ ?e (send ?obj get-Contents)) then
                    (bind ?validPaths (create$ ?validPaths ?z))))
         (if (> (length$ ?validPaths) 0) then
           (assert (Pull slices for range ?e to ?b for instruction ?i { 
                         associated cpv ?cpv } using paths $?validPaths))))
;------------------------------------------------------------------------------
(defrule CreateSliceSegments
         (Stage WavefrontSchedule $?)
         (Substage Analyze $?)
         ?fct <- (Pull slices for range ?e to ?b for instruction ?i {
                       associated cpv ?cpv } using paths ?path $?paths)
         (object (is-a Slice) (Parent ?b) (TargetBlock ?e) (TargetPath ?path)
                 (name ?s))
         =>
         (retract ?fct)
         (assert (Pull slices for range ?e to ?b for instruction ?i {
                       associated cpv ?cpv } using paths $?paths)
                 (Analyze slice ?s for ?e and cpv ?cpv)))
;------------------------------------------------------------------------------
(defrule RetractSliceSegmenterFact
         (Stage WavefrontSchedule $?)
         (Substage Analyze $?)
         ?fct <- (Pull slices for range ? to ? for instruction ? {
                       associated cpv ? } using paths)
         =>
         (retract ?fct))
;------------------------------------------------------------------------------
(defrule FAILURE-MISSING-SLICE 
         (Stage WavefrontSchedule $?)
         (Substage Analyze $?)
         ?fct <- (Pull slices for range ?e to ?b for instruction ?i {
                       associated cpv ?cpv } using paths ?path $?paths)
         (not (exists (object (is-a Slice) (Parent ?b) (TargetBlock ?e)
                              (TargetPath ?path))))
         =>
         (facts)
         (printout t "ERROR: Couldn't find an associated slice for " crlf
                   "TargetBlock = " ?e crlf
                   "Parent = " ?b crlf
                   "TargetPath = " ?path crlf
                   "TargetPath contents = " (send (symbol-to-instance-name
                                                    ?path) get-Contents) crlf
                   "Rest of paths are = " $?paths crlf)
         (halt))

;------------------------------------------------------------------------------
(defrule MergeSliceAnalysisFacts-SingleSingle
         (Stage WavefrontSchedule $?)
         (Substage Analyze $?)
         ?f0 <- (Analyze slice ?s0 for ?e and cpv ?cpv)
         ?f1 <- (Analyze slice ?s1&~?s0 for ?e and cpv ?cpv)
         ;(test (neq ?f0 ?f1))
         =>
         (retract ?f0 ?f1)
         (assert (Analyze in ?e using cpv ?cpv and slices ?s0 ?s1)))
;------------------------------------------------------------------------------
(defrule ConvertSingleSliceRule
         (declare (salience -3))
         (Stage WavefrontSchedule $?)
         (Substage Analyze $?)
         ?f0 <- (Analyze slice ?s0 for ?e and cpv ?cpv)
         =>
         (retract ?f0)
         (assert (Analyze in ?e using cpv ?cpv and slices ?s0)))
;------------------------------------------------------------------------------
(defrule MergeSliceAnalysisFacts-MultiMulti
         (Stage WavefrontSchedule $?)
         (Substage Analyze $?)
         ?f0 <- (Analyze in ?e using cpv ?cpv and slices $?q)
         ?f1 <- (Analyze in ?e using cpv ?cpv and slices $?z)
         (test (neq ?f0 ?f1)) 
         =>
         (retract ?f0 ?f1)
         (assert (Analyze in ?e using cpv ?cpv and slices $?z $?q)))
;------------------------------------------------------------------------------
(defrule SetifyAnalyzeSlicesFact
         (declare (salience -1))
         (Stage WavefrontSchedule $?)
         (Substage Analyze $?)
         ?fct <- (Analyze in ?e using cpv ?cpv and slices $?a ?b $?c ?b $?d)
         =>
         (retract ?fct)
         (assert (Analyze in ?e using cpv ?cpv and slices $?a ?b $?c $?d)))
;------------------------------------------------------------------------------
(defrule ERROR-ANALYSIS-FAILURE
         (declare (salience -900))
         (Stage WavefrontSchedule $?)
         (Substage Analyze $?)
         (Analyze instruction ?i for ?blkID)
         ?inst <- (object (is-a Instruction) (name ?i))
         (object (is-a PathAggregate) (Parent ?blkID) 
                 (ScheduledInstructions $?si))
         ?cpv <- (object (is-a CompensationPathVector) (Parent ?i))
         =>
         (printout t "ERROR: ANALYZE INSTRUCTION " ?i " WASN'T MATCHED!!!" crlf
                   "SCHEDULED INSTRUCTIONS: " $?si crlf)
         (send ?inst print)
         (printout t crlf)
         (send ?cpv print)
         (halt))
;------------------------------------------------------------------------------
; now that we have a list of slices to look at it's time to check and see if
; the given cpv can be moved up based on the slice. If it can't then assert 
; a fact that says as much
;------------------------------------------------------------------------------
(defrule RetractSliceAnalysis
         "Retract all slice analysis if it turns out there is a failure fact"
         (Stage WavefrontSchedule $?)
         (Substage SliceAnalyze $?)
         ?fct <- (Analyze in ?e using cpv ?cpv and slices $?)
         (exists (Cant schedule ?cpv for ?e ?))
         =>
         (retract ?fct))
;------------------------------------------------------------------------------
(defrule AnalyzeSliceContentsForFailure-ProducerLowerThanTargetBlock
         "Does a check to make sure that non local dependencies prevent an 
         instruction from being moved upward into the target block"
         (Stage WavefrontSchedule $?)
         (Substage SliceAnalyze $?)
         ?fct <- (Analyze in ?e using cpv ?cpv and slices ?s $?ss)
         (object (is-a Slice) (name ?s) (TargetBlock ?e) (Parent ?b)
                 (Contents $? ?element $?))
         (object (name ?element) (Produces $? ?nld $?))
         (object (is-a CompensationPathVector) (name ?cpv) (Parent ?i))
         (object (is-a Instruction) (name ?i) (DestinationRegisters ?dr)
                 (NonLocalDependencies $? ?nld $?))
         ?agObj <- (object (is-a PathAggregate) (Parent ?e))
         =>
         ; (printout t "Failed Instruction " ?i " because producer is lower "
         ;             "than block " ?e " on the wavefront" crlf)
         (retract ?fct)
         (bind ?ind (member ?i (send ?agObj get-InstructionList)))
         (if (neq FALSE ?ind) then
           (slot-delete$ ?agObj InstructionList ?ind ?ind))
         (assert (Cant schedule ?cpv for ?e ever)))
;------------------------------------------------------------------------------
(defrule AnalyzeSliceContentsForFailure-CallBarrier
         (Stage WavefrontSchedule $?)
         (Substage SliceAnalyze $?)
         ?fct <- (Analyze in ?e using cpv ?cpv and slices ?s $?ss)
         (object (is-a Slice) (name ?s) (TargetBlock ?e) (Parent ?b)
                 (Contents $? ?element $?))
         (object (name ?element) (HasCallBarrier TRUE))
         (object (is-a CompensationPathVector) (name ?cpv) (Parent ?i))
         (object (is-a Instruction) (name ?i) (DestinationRegisters ?dr))
         ?agObj <- (object (is-a PathAggregate) (Parent ?e))
         =>
         (retract ?fct)
         ;(printout t "Removed " ?i " from being scheduled - "
         ;            "Call Barrier" crlf)
         (bind ?ind (member$ ?i (send ?agObj get-InstructionList)))
         (if (neq FALSE ?ind) then 
           (slot-delete$ ?agObj InstructionList ?ind ?ind))
         (assert (Cant schedule ?cpv for ?e ever)))
;------------------------------------------------------------------------------
(defrule SliceTargetHasMemoryBarrier
         "The given slice has an element that contains a memory barrier. 
         A memory barrier is only created when analysis has failed to ascertain
         what is being read from or written to in memory."
         (Stage WavefrontSchedule $?)
         (Substage SliceAnalyze $?)
         ?fct <- (Analyze in ?e using cpv ?cpv and slices ?s $?ss)
         (object (is-a Slice) (name ?s) (TargetBlock ?e) 
                 (Parent ?b) (Contents $? ?element $?))
         (object (is-a CompensationPathVector) (name ?cpv) (Parent ?i))
         (object (is-a LoadInstruction|StoreInstruction) (name ?i)
                 (DestinationRegisters ?dr))
         (object (name ?element) (HasMemoryBarrier TRUE))
         ?agObj <- (object (is-a PathAggregate) (Parent ?e))
         =>
         (retract ?fct)
         ;(printout t "Removed " ?i " from being scheduled into " ?e 
         ;            " - MemoryBarrier" crlf)
         (bind ?ind (member$ ?i (send ?agObj get-InstructionList)))
         (if (neq FALSE ?ind) then 
           (slot-delete$ ?agObj InstructionList ?ind ?ind))
         (assert (Cant schedule ?cpv for ?e ever)))
;------------------------------------------------------------------------------
(defrule SliceTargetDoesntHaveMemoryBarrier-ModifiesSameMemory
         "The given slice has an element that contains a entry in the WritesTo 
         list that is the same thing as the given load or store instruction"
         (Stage WavefrontSchedule $?)
         (Substage SliceAnalyze $?)
         ?fct <- (Analyze in ?e using cpv ?cpv and slices ?s $?ss)
         (object (is-a Slice) (name ?s) (TargetBlock ?e) 
                 (Parent ?b) (Contents $? ?element $?))
         (object (is-a CompensationPathVector) (name ?cpv) (Parent ?i))
         ?instruction <- (object (is-a LoadInstruction|StoreInstruction) 
                                 (name ?i)
                                 (MemoryTarget ?mt) 
                                 (DestinationRegisters ?dr))
         (object (name ?element) (HasMemoryBarrier FALSE) (HasCallBarrier FALSE)
                 (WritesTo $? ?mt $?))
         ?agObj <- (object (is-a PathAggregate) (Parent ?e))
         =>
         (retract ?fct)
         (bind ?ind (member$ ?i (send ?agObj get-InstructionList)))
         (if (neq FALSE ?ind) then 
           (slot-delete$ ?agObj InstructionList ?ind ?ind))
         ;(printout t "Removed " ?i " from being scheduled into " 
         ;					 ?e " because " ?element " - ModifiesSameMemory" crlf)
         (assert (Cant schedule ?cpv for ?e ever)))
;------------------------------------------------------------------------------
(defrule SliceTargetDoesntHaveMemoryBarrier-HasUnknownReference
         "Does now allow loads or stores to be moved above the given element
         regardless of if a memory barrier exists or not. This is because there
         is an unknown loader element"
         (Stage WavefrontSchedule $?)
         (Substage Analyze $?)
         ?fct <- (Analyze in ?e using cpv ?cpv and slices ?s $?ss)
         (object (is-a Slice) (name ?s) (TargetBlock ?e) 
                 (Parent ?cpv) (Contents $? ?element $?))
         (object (is-a CompensationPathVector) (name ?cpv) (Parent ?i))
         (object (is-a LoadInstruction|StoreInstruction) (name ?i) 
                 (Parent ?q) (DestinationRegisters ?dr))
         (object (name ?element) (WritesTo $? UNKNOWN $?))
         ?agObj <- (object (is-a PathAggregate) (Parent ?e))
         =>
         (retract ?fct)
         ;(printout t "Removed " ?i " from being scheduled from block " ?q 
         ;					 " unknown reference" crlf)
         (bind ?ind (member$ ?i (send ?agObj get-InstructionList)))
         (if (neq FALSE ?ind) then 
           (slot-delete$ ?agObj InstructionList ?ind ?ind))
         (assert (Cant schedule ?cpv for ?e ever)))
;------------------------------------------------------------------------------
(defrule CanScheduleIntoBlockOnSlice
         (declare (salience -2))
         (Stage WavefrontSchedule $?)
         (Substage SliceAnalyze $?)
         ?fct <- (Analyze in ?e using cpv ?cpv and slices ?s $?ss)
         =>
         (retract ?fct)
         (assert (Analyze in ?e using cpv ?cpv and slices $?ss)))
;------------------------------------------------------------------------------
(defrule CanScheduleInstructionThisIteration
         (declare (salience -3))
         (Stage WavefrontSchedule $?)
         (Substage SliceAnalyze $?)
         ?fct <- (Analyze in ?e using cpv ?cpv and slices)
         =>
         (retract ?fct)
         (assert (Can schedule ?cpv for ?e)))
;------------------------------------------------------------------------------
(defrule AddCPVToSuccessList
         (Stage WavefrontSchedule $?)
         (Substage MergeInit $?)
         ?fct <- (Can schedule ?cpvID for ?blkID)
         ?agObj <- (object (is-a PathAggregate) (Parent ?blkID))
         =>
         (retract ?fct)
         (slot-insert$ ?agObj MovableCompensationPathVectors 1 ?cpvID))
;------------------------------------------------------------------------------
(defrule FailCPVForNow
         (Stage WavefrontSchedule $?)
         (Substage MergeInit $?)
         ?fct <- (Cant schedule ?cpvID for ?blkID now)
         ?agObj <- (object (is-a PathAggregate) (Parent ?blkID))
         =>
         (retract ?fct)
         (slot-insert$ ?agObj StalledCompensationPathVectors 1 ?cpvID))
;------------------------------------------------------------------------------
(defrule RemoveCPVFromService
         (Stage WavefrontSchedule $?)
         (Substage MergeInit $?)
         ?fct <- (Cant schedule ?cpvID for ?blkID ever)
         ?agObj <- (object (is-a PathAggregate) (Parent ?blkID))
         ?cpvObj <- (object (is-a CompensationPathVector) (name ?cpvID) 
                            (Parent ?i))
         =>
         (retract ?fct)
         (slot-insert$ ?cpvObj Failures 1 ?blkID)
         (slot-insert$ ?agObj ImpossibleCompensationPathVectors 1 ?cpvID))
;------------------------------------------------------------------------------
(defrule PonderMovementIteration
         (declare (salience 100))
         (Stage WavefrontSchedule $?)
         (Substage Ponder $?)
         (object (is-a Wavefront) (name ?r) (Contents $? ?e $?))
         ?ag <- (object (is-a PathAggregate) (Parent ?e) (name ?pa)
                        (StalledCompensationPathVectors $?scpv))
         (test (> (length$ $?scpv) 0))
         =>
         (assert (Another Movement Required))
         (modify-instance ?ag (StalledCompensationPathVectors)
                          (TargetCompensationPathVectors $?scpv)))
;------------------------------------------------------------------------------
(defrule AnotherMovementIsRequired
         (Stage WavefrontSchedule $?)
         ?ponder <- (Substage Ponder $?rest)
         ?f <- (Another Movement Required)
         =>
         ;this returns a tuple
         (retract ?ponder ?f)
         (assert (Substage GenerateAnalyze0 
                           GenerateAnalyze 
                           Analyze 
                           SliceAnalyze 
                           MergeInit 
                           Merge 
                           MergeUpdate
                           ReopenBlocks 
                           Ponder 
                           $?rest)))
;------------------------------------------------------------------------------
(defrule FinishSchedulingIntoBlock
         (declare (salience -1))
         (Stage WavefrontSchedule $?)
         (Substage Ponder $?rest)
         =>
         (progn$ (?instance (find-all-instances ((?wave Wavefront)) TRUE))
                 (progn$ (?child (send ?instance get-Contents))
                         (modify-instance 
                           (symbol-to-instance-name ?child)
                           (IsOpen FALSE)))))
;------------------------------------------------------------------------------
; LLVM Schedule Construction rules - these rules interface with LLVM
;------------------------------------------------------------------------------
(defrule ConstructScheduleObjectForBlock-HasPhis
         (declare (salience 10))
         (Stage WavefrontSchedule $?)
         (Substage ScheduleObjectCreation $?)
         ?fct <- (Schedule ?e for ?r)
         (object (is-a TerminatorInstruction) (Parent ?e) (name ?last))
         (object (is-a BasicBlock) (name ?e) (Parent ?r)
                 (Contents $? ?lastPhi ?firstNonPhi $?instructions ?last $?))
         (object (is-a PhiNode) (name ?lastPhi))
         (object (is-a Instruction&~PhiNode&~TerminatorInstruction) 
                 (name ?firstNonPhi))
         =>
         ;strange that ?last is being incorporated into $?q
         (retract ?fct)
         (assert (Update style for ?e is ?lastPhi))
         (make-instance of Schedule (Parent ?e) 
                        (Contents ?firstNonPhi ?instructions)))
;------------------------------------------------------------------------------
(defrule ConstructScheduleObjectForBlock-DoesntHavePhis
         (declare (salience 10))
         (Stage WavefrontSchedule $?)
         (Substage ScheduleObjectCreation $?)
         ?fct <- (Schedule ?e for ?r)
         (object (is-a BasicBlock) (name ?e) (Parent ?r)
                 (Contents ?firstNonPhi $?instructions ?last $?))
         (object (is-a Instruction&~PhiNode&~TerminatorInstruction) 
                 (name ?firstNonPhi))
         (object (is-a TerminatorInstruction) (Parent ?e) (name ?last))
         =>
         (retract ?fct)
         (assert (Update style for ?e is))
         (make-instance of Schedule (Parent ?e) 
                        (Contents ?firstNonPhi ?instructions)))
;------------------------------------------------------------------------------
(defrule ConstructScheduleObjectForBlock-TerminatorOnly
         (declare (salience 10))
         (Stage WavefrontSchedule $?)
         (Substage ScheduleObjectCreation $?)
         ?fct <- (Schedule ?e for ?r)
         (object (is-a BasicBlock) (name ?e) (Parent ?r)
                 (Contents ?last))
         (object (is-a TerminatorInstruction) (Parent ?e) (name ?last))
         =>
         ;mark the block as closed
         (retract ?fct))
;------------------------------------------------------------------------------
(defrule ConstructScheduleObjectForBlock-TerminatorAndPhisOnly
         (declare (salience 10))
         (Stage WavefrontSchedule $?)
         (Substage ScheduleObjectCreation $?)
         ?fct <- (Schedule ?e for ?r)
         (object (is-a BasicBlock) (name ?e) (Parent ?r)
                 (Contents $? ?lastPhi ?last $?))
         (object (is-a TerminatorInstruction) (Parent ?e) (name ?last))
         (object (is-a PhiNode) (name ?lastPhi))
         =>
         ;mark the block as closed
         (retract ?fct))
;------------------------------------------------------------------------------
(defrule Failout-Strange-ScheduleFact
         (declare (salience 10))
         (Stage WavefrontSchedule $?)
         (Substage ScheduleObjectCreation $?)
         ?fct <- (Schedule ?e for ?r)
         (object (is-a thing&~BasicBlock) 
                 (name ?e))
         (object (is-a thing&~Region) 
                 (name ?r))
         =>
         (printout t "ERROR: Asserted a really wierd schedule fact: " crlf
                   "What should be a block is a " (class ?e) " named " ?e crlf
                   "What should be a region is a " (class ?r) " named " ?r crlf)
         (halt))
;------------------------------------------------------------------------------
(defrule PreschedulePhiNodes
         "Adds all phi nodes into the list of scheduled instructions.
         We can always assume they are ready to go too!"
         (Stage WavefrontSchedule $?)
         (Substage ScheduleObjectCreation $?)
         (object (is-a Schedule) 
                 (name ?n) 
                 (Parent ?p) 
                 (Scheduled $?s))
         (object (is-a BasicBlock) 
                 (name ?p) 
                 (Contents $? ?c $?))
         (object (is-a PhiNode) 
                 (name ?c))
         (test (not (member$ ?c ?s)))
         =>
         (slot-insert$ ?n
                       Scheduled
                       1
                       ?c))
;         (modify-instance ?n
;                          (Scheduled $?s ?c)))
;------------------------------------------------------------------------------
(defrule PrescheduleNonLocals
         "Marks all non local instructions as already scheduled. With the way 
         that the dependency analysis goes only instructions that are actually 
         valid will be scheduled first."
         (Stage WavefrontSchedule $?)
         (Substage ScheduleObjectCreation $?)
         ?schedObj <- (object (is-a Schedule) (name ?n) (Parent ?p) 
                              (Contents $? ?c $?) (Scheduled $?s))
         ?inst <- (object (is-a Instruction) (name ?c) (Parent ?p)
                          (NonLocalDependencies $? ?d $?))
         (test (not (member$ ?d ?s)))
         =>
         (modify-instance ?schedObj (Scheduled $?s ?d)))
;------------------------------------------------------------------------------
(defrule AssertPerformScheduling
         (declare (salience -1))
         (Stage WavefrontSchedule $?)
         (Substage ScheduleObjectCreation $?)
         (object (is-a Schedule) (name ?q) (Parent ?b))
         =>
         (assert (Perform Schedule ?q for ?b)))
;------------------------------------------------------------------------------
(defrule PrintoutSchedules
         (declare (salience -10))
         (Stage WavefrontSchedule $?)
         (Substage ScheduleObjectCreation $?)
         (Debug)
         (Schedule)
         ?schedule <- (object (is-a Schedule) (name ?q))
         =>
         (send ?schedule print))
;------------------------------------------------------------------------------
(defrule FAIL-SCHEDULE-FACT-STILL-EXISTS
         (declare (salience -200))
         (Stage WavefrontSchedule $?)
         (Substage ScheduleObjectCreation $?)
         (Schedule ?e for ?r)
         =>
         (printout t "ERROR: (Schedule " ?e " for " ?r ") still exists!" crlf)
         (printout t "EXITING PROGRAM!" crlf)
         (facts)

         (halt))
;------------------------------------------------------------------------------
(defrule CanScheduleInstructionNow
         (declare (salience 344))
         (Stage WavefrontSchedule $?)
         (Substage ScheduleObjectUsage $?)
         (Perform Schedule ?n for ?b)
         ?sched <- (object (is-a Schedule) (name ?n) (Contents ?curr $?rest) 
                           (Scheduled $?s) (Success $?succ))
         (object (is-a Instruction) (name ?curr) 
                 (LocalDependencies $?p&:(subsetp $?p $?s)))
         =>
         (modify-instance ?sched (Contents $?rest) (Success $?succ ?curr)))
;------------------------------------------------------------------------------
(defrule MustStallInstructionForSchedule
         (declare (salience 343))
         (Stage WavefrontSchedule $?)
         (Substage ScheduleObjectUsage $?)
         (Perform Schedule ?n for ?b)
         ?sched <- (object (is-a Schedule) (name ?n) (Contents ?curr $?rest) 
                           (Scheduled $?s) (Failure $?fails))
         (object (is-a Instruction) (name ?curr) 
                 (LocalDependencies $?p&:(not (subsetp $?p $?s))))
         =>
         (modify-instance ?sched (Contents $?rest) (Failure $?fails ?curr)))
;------------------------------------------------------------------------------
(defrule EndInstructionScheduleAttempt
         (Stage WavefrontSchedule $?)
         (Substage ResetScheduling $?)
         ?fct <- (Perform Schedule ?n for ?b)
         ?sched <- (object (is-a Schedule) (name ?n)
                           (Contents))
         =>
         (retract ?fct))
;------------------------------------------------------------------------------
(defrule PutSuccessfulInstructionIntoInstructionStream
         (declare (salience 270))
         (Stage WavefrontSchedule $?)
         (Substage ResetScheduling $?)
         ?sched <- (object (is-a Schedule) (name ?n) (Parent ?p)
                           (Success ?targ $?rest) (Scheduled $?s)
                           (InstructionStream $?is))
         (object (is-a Instruction) (name ?targ))
         =>
         (object-pattern-match-delay
           (modify-instance ?sched (Success $?rest) (Scheduled $?s ?targ)
                            (InstructionStream $?is ?targ))))
;------------------------------------------------------------------------------
(defrule PutSuccessfulStoreInstructionIntoInstructionStream
         (declare (salience 271))
         (Stage WavefrontSchedule $?)
         (Substage ResetScheduling $?)
         ?sched <- (object (is-a Schedule) (name ?n) (Parent ?p)
                           (Success ?targ $?rest) (Scheduled $?s)
                           (InstructionStream $?stream))
         (object (is-a StoreInstruction) (name ?targ) (DestinationRegisters ?reg))
         =>
         (object-pattern-match-delay 
           (modify-instance ?sched (Success $?rest) (Scheduled $?s ?targ ?reg)
                            (InstructionStream $?stream ?targ))))
;------------------------------------------------------------------------------
(defrule FinishedPopulatingInstructionGroup-AssertReset
         (declare (salience 200))
         (Stage WavefrontSchedule $?)
         (Substage ResetScheduling $?)
         (object (is-a Schedule) (name ?n) (Contents) (Success) 
                 (Failure $?elements))
         (test (> (length$ ?elements) 0))
         =>
         (assert (Reset schedule ?n)))
;------------------------------------------------------------------------------
(defrule FinishedPopulatingInstructionGroup-AssertFinished
         (declare (salience 200))
         (Stage WavefrontSchedule $?)
         (Substage ResetScheduling $?)
         (object (is-a Schedule) (name ?n)
                 (Parent ?p) (Contents) (Success) (Failure))
         =>
         (assert (Schedule ?p in llvm)))
;------------------------------------------------------------------------------
(defrule ResetTargetScheduleForAnotherGo
         (declare (salience 180))
         (Stage WavefrontSchedule $?)
         (Substage ResetScheduling $?)
         ?fct <- (Reset schedule ?n)
         ?sched <- (object (is-a Schedule) (name ?n) (Parent ?p) (Contents) 
                           (Failure $?elements))
         =>
         (object-pattern-match-delay
           (retract ?fct)
           (assert (Perform Schedule ?n for ?p)
                   (Reset scheduling process))
           (modify-instance ?sched (Contents ?elements) (Failure))))
;------------------------------------------------------------------------------
(defrule ResetSchedulingProcess
         (declare (salience -10))
         (Stage WavefrontSchedule $?)
         (Substage ResetScheduling $?)
         ?f0 <- (Substage ResetScheduling $?rest)
         ?f1 <- (Reset scheduling process)
         =>
         (retract ?f0 ?f1)
         (assert (Substage ScheduleObjectUsage ResetScheduling $?rest)))
;------------------------------------------------------------------------------
(defrule FinishLLVMEncoding-HasPhi
         (declare (salience -12))
         (Stage WavefrontSchedule $?)
         (Substage LLVMUpdate $?)
         ?f1 <- (Schedule ?p in llvm)
         ?f2 <- (Update style for ?p is ?lastPhi)
         (object (is-a Schedule) (Parent ?p) (InstructionStream $?stream))
         ?bb <- (object (is-a BasicBlock) (name ?p) 
                        (Contents $?before ?lastPhi $?instructions ?last 
                                  $?rest))
         (object (is-a TerminatorInstruction) (name ?last) (Pointer ?tPtr))
         =>
         (object-pattern-match-delay
           (modify-instance ?bb 
                            (Contents $?before ?lastPhi ?stream ?last $?rest))
           (llvm-schedule-block ?tPtr (symbol-to-pointer-list ?stream))
           (retract ?f1 ?f2)))
;------------------------------------------------------------------------------
(defrule FinishLLVMEncoding-NoPhi
         (declare (salience -12))
         (Stage WavefrontSchedule $?)
         (Substage LLVMUpdate $?)
         ?f1 <- (Schedule ?p in llvm)
         ?f2 <- (Update style for ?p is)
         ?bb <- (object (is-a BasicBlock) (name ?p))
         (object (is-a Schedule) (Parent ?p) (InstructionStream $?stream))
         (object (is-a TerminatorInstruction) (Parent ?p) (name ?last) 
                 (Pointer ?tPtr))
         =>
         (object-pattern-match-delay
           (modify-instance ?bb (Contents ?stream ?last))
           (llvm-schedule-block ?tPtr (symbol-to-pointer-list ?stream))
           (retract ?f1 ?f2)))
;------------------------------------------------------------------------------
(defrule RetractUpdateStyleHint
         (declare (salience -26))
         (Stage WavefrontSchedule $?)
         (Substage LLVMUpdate $?)
         ?fct <- (Update style for ?t is $?lasers)
         =>
         (retract ?fct))
;------------------------------------------------------------------------------
; Wavefront propagation rules (TODO: refresh self with these rules)
;------------------------------------------------------------------------------
(defrule PropagateAggregateInformation
         "Pulls instruction propagation information from all elements on paths 
         that immediately precede this element on the wavefront and merges it 
         into the path aggregate itself"
         (Stage WavefrontSchedule $?)
         (Substage Identify $?)
         (Propagate aggregates of ?e)
         ;if this element is on the wavefront then we can be certain that all 
         ;of it's predecessors are above it. That is the definition of being on
         ;the wavefront
         ?pa <- (object (is-a PathAggregate) (Parent ?e) (name ?pp))
         (object (is-a Diplomat) (name ?e) (PreviousPathElements $? ?z $?))
         (object (is-a PathAggregate) (Parent ?z) 
                 (InstructionPropagation $? ?targ ?alias ? ! $?))
         =>
         ;replace parent blocks of previous path elements with the name of the
         ;element this was acquired from
         ;(printout t "Put (" ?targ " " ?alias " " ?z "! ) into " ?pp crlf)
         (slot-insert$ ?pa InstructionPropagation 1 ?targ ?alias ?z !))
;------------------------------------------------------------------------------
(defrule RetractAggregationInformation
         (declare (salience -50))
         (Stage WavefrontSchedule $?)
         (Substage Identify $?)
         ?fct <- (Propagate aggregates of ?)
         =>
         (retract ?fct))
;------------------------------------------------------------------------------
(defrule AssertPhiNodePropagationPredicateIsBlock
         (declare (salience 1))
         (Stage WavefrontSchedule $?)
         (Substage PhiIdentify $?)
         (object (is-a Wavefront) (Parent ?r) (Contents $? ?e $?))
         ?pa <- (object (is-a PathAggregate) (Parent ?e) 
                        (InstructionPropagation ?targ ?alias ?pred ! $?rest))
         =>
         (modify-instance ?pa (InstructionPropagation $?rest))
         (assert (Propagation target ?targ with alias ?alias
                              from block ?pred for block ?e)))
;------------------------------------------------------------------------------
(defrule RemoveDuplicateElements 
         (Stage WavefrontSchedule $?)
         (Substage PhiNode $?)
         ?f0 <- (Propagation target ?t with alias ?a from block ?p0 
                             for block ?b)
         ?f1 <- (Propagation target ?t with alias ?a from block ?p1 
                             for block ?b)
         (test (and (neq ?f0 ?f1) (neq ?p0 ?p1)))
         ?pa <- (object (is-a PathAggregate) (Parent ?b))
         =>
         (retract ?f0 ?f1)
         (slot-insert$ ?pa InstructionPropagation 1 ?t ?a ?b !))
;------------------------------------------------------------------------------
(defrule MergePhiNodePropagationWithOtherPropagation
         (Stage WavefrontSchedule $?)
         (Substage PhiNode $?)
         ?f0 <- (Propagation target ?t with alias ?a0 from block ?p0 
                             for block ?b)
         ?f1 <- (Propagation target ?t with alias ?a1 from block ?p1 
                             for block ?b)
         (test (neq ?f0 ?f1))
         =>
         (retract ?f0 ?f1)
         (assert (Create phinode targeting instruction ?t for block ?b 
                         consisting of ?a0 ?p0 ?a1 ?p1 )))
;------------------------------------------------------------------------------
(defrule MergePhiNodePropagationWithCreateStatement
         (Stage WavefrontSchedule $?)
         (Substage PhiNode $?)
         ?f0 <- (Propagation target ?t with alias ?a0 from block ?p0 
                             for block ?b)
         ?f1 <- (Create phinode targeting instruction ?t for block ?b 
                        consisting of $?targets)
         =>
         (retract ?f0 ?f1)
         (assert (Create phinode targeting instruction ?t for block ?b 
                         consisting of $?targets ?a0 ?p0 )))
;------------------------------------------------------------------------------
(defrule PutUnfulfilledItemsBackIntoPropagationList
         (declare (salience -10))
         (Stage WavefrontSchedule $?)
         (Substage PhiNode $?)
         ?f0 <- (Propagation target ?t with alias ?a0 from block ?p0 for 
                             block ?b)
         ?pa <- (object (is-a PathAggregate) (Parent ?b))
         =>
         (retract ?f0)
         (slot-insert$ ?pa InstructionPropagation 1 ?t ?a0 ?b !))
;------------------------------------------------------------------------------
(defrule NamePhiNodeFromCreateStatement-NotOriginalBlock
         (declare (salience -12))
         (Stage WavefrontSchedule $?)
         (Substage PhiNode $?)
         ?fct <- (Create phinode targeting instruction ?t for block ?b
                         consisting of $?elements)
         ?agObj <- (object (is-a PathAggregate) 
                           (Parent ?b))
         ?bb <- (object (is-a BasicBlock) 
                        (name ?b) 
                        (Contents ?first $?rest)
                        (UnlinkedInstructions $?ui))
         (test (not (member$ ?t $?ui)))
         (object (is-a Instruction) 
                 (name ?first) 
                 (Pointer ?bPtr))
         (object (is-a Instruction) 
                 (name ?t) 
                 (Type ?ty))
         (object (is-a LLVMType) 
                 (name ?ty) 
                 (Pointer ?dataType))
         =>
         (retract ?fct)
         (bind ?name (sym-cat phi. (gensym*) . ?t))
         (bind ?count (/ (length$ $?elements) 2))
         (bind ?pointers (symbol-to-pointer-list ?elements))
         (make-instance ?name of PhiNode 
                        (Parent ?b)
                        (TimeIndex 0)
                        (Pointer (llvm-make-phi-node ?name ?dataType ?count 
                                                     ?bPtr ?pointers))
                        (IncomingValueCount ?count)
                        (Operands $?elements))
         ;we've scheduled the given original instruction into this block
         ; although it's just a ruse
         (slot-insert$ ?agObj ScheduledInstructions 1 ?t)
         (slot-insert$ ?agObj InstructionPropagation 1 ?t ?name ?b !)
         (slot-insert$ ?agObj ReplacementActions 1 ?t ?name !)
         (slot-insert$ ?bb Contents 1 ?name)
         (assert (Update duration for block ?b)))
;------------------------------------------------------------------------------
(defrule NamePhiNodeFromCreateStatement-OriginalBlock
         (declare (salience -12))
         (Stage WavefrontSchedule $?)
         (Substage PhiNode $?)
         ?fct <- (Create phinode targeting instruction ?t for block ?b
                         consisting of $?elements)
         ?agObj <- (object (is-a PathAggregate) 
                           (Parent ?b))
         ?bb <- (object (is-a BasicBlock) 
                        (name ?b) 
                        (Contents ?first $?rest) 
                        (UnlinkedInstructions $?ui))
         (test (not (member$ ?t ?ui)))
         (object (is-a Instruction) 
                 (name ?first) 
                 (Pointer ?bPtr))
         ?tObj <- (object (is-a Instruction) 
                          (name ?t) 
                          (Type ?ty) 
                          (Pointer ?tPtr))
         (object (is-a LLVMType) 
                 (name ?ty) 
                 (Pointer ?dataType))
         =>
         (retract ?fct)
         (bind ?name (sym-cat phi. (gensym*) . ?t))
         (bind ?count (/ (length$ $?elements) 2))
         (bind ?pointers (symbol-to-pointer-list ?elements))
         (bind ?phiPointer 
               (llvm-make-phi-node ?name ?dataType ?count ?bPtr ?pointers))
         (bind ?phiObj (make-instance ?name of PhiNode 
                                      (Parent ?b)
                                      (TimeIndex 0)
                                      (Pointer ?phiPointer)
                                      (IncomingValueCount ?count)
                                      (Operands $?elements)))
         (llvm-replace-all-uses ?tPtr ?phiPointer)
         (llvm-unlink-and-delete-instruction ?tPtr)
         (unmake-instance ?tObj)
         (slot-insert$ ?agObj ScheduledInstructions 1 ?t)
         (slot-insert$ ?bb Contents 1 ?name)
         (assert (Update duration for block ?b)))
;------------------------------------------------------------------------------
(defrule ReindexBasicBlock 
         (Stage WavefrontSchedule $?)
         (Substage PhiNodeUpdate $?)
         ?fct <- (Update duration for block ?b)
         (object (is-a BasicBlock) (name ?b) (Contents $?c))
         =>
         ;this is very much procedural but I frankly don't care
         ;anymore. 
         (bind ?index 0)
         (progn$ (?t ?c)
                 (bind ?obj (instance-address (symbol-to-instance-name ?t)))
                 (modify-instance ?obj (TimeIndex ?index))
                 (bind ?index (+ ?index 1)))
         (retract ?fct))
;------------------------------------------------------------------------------
; Rules associated with advancing the wavefront
;------------------------------------------------------------------------------
(defrule MoveContentsToDeleteNodes
         "Moves blocks out of the contents into the closed list"
         (declare (salience 2701))
         (Stage WavefrontSchedule $?)
         (Substage AdvanceInit $?)
         ?wave <- (object (is-a Wavefront) (name ?z) (Parent ?r) 
                          (Contents $?c) (Closed $?cl))
         (test (or (> (length$ ?c) 0) (> (length$ ?cl) 0)))
         =>
         (slot-insert$ ?wave DeleteNodes 1 ?c ?cl))
;------------------------------------------------------------------------------
(defrule MarkShouldStayOnWavefront
         (declare (salience 343))
         (Stage WavefrontSchedule $?)
         (Substage AdvanceIdentify $?)
         ?wave <- (object (is-a Wavefront) (name ?q) (Parent ?r) 
                          (DeleteNodes $?a ?b $?c))
         ?bb <- (object (is-a Diplomat) (name ?b) (NextPathElements ?s))
         (object (is-a Diplomat) (name ?s) (PreviousPathElements $?ppe))
         (test (not (subsetp ?ppe (send ?wave get-DeleteNodes)))) 
         ?agObj <- (object (is-a PathAggregate) (Parent ?b))
         =>
         (object-pattern-match-delay
           (if (not (member$ ?b (send ?wave get-Closed))) then
             (bind ?ind (member$ ?b (send ?wave get-Contents)))
             (slot-delete$ ?wave Contents ?ind ?ind)
             (slot-insert$ ?wave Closed 1 ?b))
           (modify-instance ?wave (DeleteNodes $?a $?c))))
;------------------------------------------------------------------------------
(defrule DeleteElementFromWavefront
         (declare (salience 180))
         (Stage WavefrontSchedule $?)
         (Substage Advance $?)
         ?wave <- (object (is-a Wavefront) (name ?id) (Parent ?r) 
                          (DeleteNodes ?a $?))
         (object (is-a Diplomat) (name ?a) (NextPathElements $?npe))
         =>
         (object-pattern-match-delay
           (bind ?ind (member$ ?a (send ?wave get-Contents)))
           (bind ?ind2 (member$ ?a (send ?wave get-Closed)))
           (slot-delete$ ?wave DeleteNodes 1 1)
           (if ?ind then (slot-delete$ ?wave Contents ?ind ?ind))
           (if ?ind2 then (slot-delete$ ?wave Closed ?ind2 ?ind2))
           (assert (Add into ?id blocks $?npe))))
;------------------------------------------------------------------------------
(defrule PutSuccessorsOntoWavefront-Match
         (declare (salience 100))
         (Stage WavefrontSchedule $?)
         (Substage AdvanceEnd $?)
         ?fct <- (Add into ?id blocks ?next $?rest)
         ?wave <- (object (is-a Wavefront) (name ?id))
         =>
         (retract ?fct)
         ;I know that this is procedural but I really want to get this done
         (assert (Add into ?id blocks $?rest))
         (if (not (member$ ?next (send ?wave get-Contents))) then
           (slot-insert$ ?wave Contents 1 ?next)))
;------------------------------------------------------------------------------
(defrule PutSuccessorsOntoWavefront-NoMoreElements
         (declare (salience 100))
         (Stage WavefrontSchedule $?)
         (Substage AdvanceEnd $?)
         ?fct <- (Add into ? blocks)
         =>
         (retract ?fct))
;------------------------------------------------------------------------------
(defrule PonderRestartOfWavefrontScheduling
         (declare (salience -512))
         (Stage WavefrontSchedule $?)
         ?fct <- (Substage Update $?)
         =>
         (bind ?instances (find-all-instances ((?wave Wavefront)) 
                                              (> (length$ ?wave:Contents) 0)))
         (if (> (length$ ?instances) 0) then
           (retract ?fct)
           (assert (Substage Init 
                             Identify 
                             PhiIdentify 
                             PhiNode 
                             PhiNodeUpdate 
                             Pathing 
                             Strip 
                             Inject 
                             Acquire 
                             Slice 
                             AnalyzeInit 
                             GenerateAnalyze0
                             GenerateAnalyze
                             Analyze 
                             SliceAnalyze 
                             MergeInit 
                             Merge 
                             MergeUpdate
                             ReopenBlocks
                             Ponder 
                             Rename 
                             DependencyAnalysis 
                             ;ScheduleObjectCreation 
                             ;ScheduleObjectUsage 
                             ;ResetScheduling 
                             ;InitLLVMUpdate
                             ;LLVMUpdate 
                             AdvanceInit 
                             AdvanceIdentify
                             Advance
                             AdvanceEnd
                             Update))))
;------------------------------------------------------------------------------
(defrule RetractUnlinkedInstructions
         (Stage WavefrontFinal $?)
         ?bb <- (object (is-a BasicBlock) (name ?b) 
                        (UnlinkedInstructions ?i $?rest))
         ?instruction <- (object (is-a Instruction) (name ?i) (Parent ?b) 
                                 (Pointer ?ptr))
         (object (is-a PathAggregate) (Parent ?b) 
                 (InstructionPropagation $? ?i ?new ?b ! $?))
         (object (is-a Instruction) (name ?new) (Pointer ?nPtr))
         =>
         ;this is a little gross but it is a very easy way to ensure that
         ;things work correctly
         (object-pattern-match-delay
           (llvm-replace-all-uses ?ptr ?nPtr)
           (modify-instance ?bb (UnlinkedInstructions $?rest))
           (llvm-unlink-and-delete-instruction ?ptr)
           (unmake-instance ?instruction)))
;------------------------------------------------------------------------------
; Update the dependencies on the wavefront
;
;
; This stage is the actual act of scheduling the blocks on the wavefront. 
; The first step is to reacquire all dependencies of the given blocks by
; running the same rules as before. The only difference is that we have to do
; it specially for the blocks on the wavefront. 
; 
; I'm thinking of just copying the rules from the analysis pass to here. It
; would be a duplication but I frankly don't care anymore. 
;------------------------------------------------------------------------------
(defrule CreateDependencyAnalysisTargets
         (declare (salience 10))
         (Stage WavefrontSchedule $?)
         (Substage DependencyAnalysis $?)
         (object (is-a Wavefront) (Parent ?r) (Contents $? ?e $?))
         (object (is-a BasicBlock) (name ?e))
         (object (is-a PathAggregate) (Parent ?e) (OriginalStopIndex ?si))
         =>
         ;only look at instructions starting at the original stop index. This
         ;prevents unncessary recomputation
         (assert (Evaluate ?e for dependencies starting at ?si)))
;------------------------------------------------------------------------------
(defrule IdentifyWAR-Wavefront
         "Identifies a WAR dependency between two instructions. It will not 
         match if it turns out the values are constant integers or constant 
         floating point values"
         (Stage WavefrontSchedule $?)
         (Substage DependencyAnalysis $?)
         (Evaluate ?p for dependencies starting at ?si)
         ?i0 <- (object (is-a Instruction) (Parent ?p) (name ?t0)
                        (Operands $? ?c $?) (TimeIndex ?ti0))
         (object (is-a thing&~ConstantInteger&~ConstantFloatingPoint) 
                 (name ?c))
         ?i1 <- (object (is-a Instruction) (Parent ?p) (name ?t1)
                        (TimeIndex ?ti1&:(and (>= ?ti1 ?si) (< ?ti0 ?ti1)))
                        (DestinationRegisters $? ?c $?))
         =>
         (assert (Instruction ?t1 consumes ?t0)
                 (Instruction ?t0 produces ?t1)))
;------------------------------------------------------------------------------
(defrule IdentifyRAW-Wavefront
         "Identifies a RAW dependency between two instructions in the same 
         block. It will not match if it turns out that the values are constant 
         integers or constant floating point values."
         (Stage WavefrontSchedule $?)
         (Substage DependencyAnalysis $?)
         (Evaluate ?p for dependencies starting at ?si)
         (object (is-a Instruction) (Parent ?p) (name ?t0)
                 (DestinationRegisters $? ?c $?) (TimeIndex ?ti0))
         (object (is-a thing&~ConstantInteger&~ConstantFloatingPoint) 
                 (name ?c))
         (object (is-a Instruction) (Parent ?p) (name ?t1)
                 (Operands $? ?c $?) 
                 (TimeIndex ?ti1&:(and (>= ?ti1 ?si) (< ?ti0 ?ti1))))
         =>
         (assert (Instruction ?t1 consumes ?t0)
                 (Instruction ?t0 produces ?t1)))
;------------------------------------------------------------------------------
(defrule IdentifyWAW-Wavefront
         "Identifies a WAW dependency between two instructions in the same 
         block. It will not match if it turns out that the values are constant 
         integers or constant floating point values."
         (Stage WavefrontSchedule $?)
         (Substage DependencyAnalysis $?)
         (Evaluate ?p for dependencies starting at ?si)
         ?i0 <- (object (is-a Instruction) (Parent ?p) (name ?t0)
                        (DestinationRegisters $? ?c $?) (TimeIndex ?ti0))
         (object (is-a thing&~ConstantInteger&~ConstantFloatingPoint) 
                 (name ?c))
         ?i1 <- (object (is-a Instruction) (Parent ?p) (name ?t1) 
                        (TimeIndex ?ti1&:(and (>= ?ti1 ?si) (< ?ti0 ?ti1))) 
                        (DestinationRegisters $? ?c $?))
         =>
         (assert (Instruction ?t1 consumes ?t0)
                 (Instruction ?t0 produces ?t1)))
;------------------------------------------------------------------------------
;these call instruction checks only work for new instructions or those that
; dont have a call dependency. As that was the only way they got into the 
; block in the first place
;------------------------------------------------------------------------------
(defrule MarkCallInstructionDependency-ModifiesMemory-Wavefront
         "Creates a series of dependencies for all instructions following a 
         call instruction if it turns out that the call could modify memory."
         (Stage WavefrontSchedule $?)
         (Substage DependencyAnalysis $?)
         (Evaluate ?p for dependencies starting at ?si)
         (object (is-a CallInstruction) (name ?name) (Parent ?p) 
                 (DoesNotAccessMemory FALSE) (OnlyReadsMemory FALSE) 
                 (MayWriteToMemory TRUE)
                 (TimeIndex ?t0))
         (object (is-a Instruction) (Parent ?p) 
                 (TimeIndex ?ti1&:(and (>= ?ti1 ?si) (< ?t0 ?ti1)))
                 (HasCallDependency FALSE) (name ?following))
         =>
         (assert (Instruction ?following has a CallDependency)
                 (Instruction ?following consumes ?name)
                 (Instruction ?name produces ?following)))
;------------------------------------------------------------------------------
(defrule MarkCallInstructionDependency-InlineAsm-Wavefront
         "Creates a series of dependencies for all instructions following a 
         call instruction if it turns out that the call is inline asm."
         (Stage WavefrontSchedule $?)
         (Substage DependencyAnalysis $?)
         (Evaluate ?p for dependencies starting at ?si)
         (object (is-a CallInstruction) (name ?name) (Parent ?p) 
                 (IsInlineAsm TRUE)
                 (TimeIndex ?t0))
         (object (is-a Instruction) (Parent ?p) 
                 (TimeIndex ?ti1&:(and (>= ?ti1 ?si) (< ?t0 ?ti1)))
                 (HasCallDependency FALSE) (name ?following))
         =>
         (assert (Instruction ?following has a CallDependency)
                 (Instruction ?following consumes ?name)
                 (Instruction ?name produces ?following)))
;------------------------------------------------------------------------------
(defrule MarkCallInstructionDependency-SideEffects-Wavefront
         "Creates a series of dependencies for all instructions following a 
         call instruction if it turns out that the call is inline asm."
         (Stage WavefrontSchedule $?)
         (Substage DependencyAnalysis $?)
         (Evaluate ?p for dependencies starting at ?si)
         (object (is-a CallInstruction) (name ?name) (Parent ?p) 
                 (MayHaveSideEffects TRUE) (MayWriteToMemory TRUE) 
                 (TimeIndex ?t0))
         (object (is-a Instruction) (Parent ?p) 
                 (TimeIndex ?ti1&:(and (>= ?ti1 ?si) (< ?t0 ?ti1)))
                 (HasCallDependency FALSE) (name ?following))
         =>
         (assert (Instruction ?following has a CallDependency)
                 (Instruction ?following consumes ?name)
                 (Instruction ?name produces ?following)))
;------------------------------------------------------------------------------
(defrule MarkNonLocalDependencies-Wavefront
         (Stage WavefrontSchedule $?)
         (Substage DependencyAnalysis $?)
         (Evaluate ?p for dependencies starting at ?si)
         ?inst <- (object (is-a Instruction) (Parent ?p) 
                          (TimeIndex ?t&:(>= ?t ?si))
                          (Operands $? ?o $?))
         (object (is-a Instruction) (name ?o) (Parent ~?p))
         =>
         (slot-insert$ ?inst NonLocalDependencies 1 ?o))
;------------------------------------------------------------------------------
(defrule Wavefront-MarkHasCallDependency
         (declare (salience -2))
         (Stage WavefrontSchedule $?)
         (Substage DependencyAnalysis $?)
         ?fct <- (Instruction ?f has a CallDependency)
         ?obj <- (object (is-a Instruction) (name ?f))
         =>
         (modify-instance ?obj (HasCallDependency TRUE))
         (retract ?fct))
;------------------------------------------------------------------------------
(defrule InjectConsumers-Wavefront
         "Adds a given consumer to the target instruction"
         (declare (salience -5))
         (Stage WavefrontSchedule $?)
         (Substage DependencyAnalysis $?)
         ?fct <- (Instruction ?target consumes ?id)
         ?inst <- (object (is-a Instruction) (name ?id))
         =>
         (retract ?fct)
         (if (not (member$ ?target (send ?inst get-Consumers))) then
           (slot-insert$ ?inst Consumers 1 ?target)))
;------------------------------------------------------------------------------
(defrule InjectProducers-Wavefront
         "Adds a given producer to the target instruction"
         (declare (salience -5))
         (Stage WavefrontSchedule $?)
         (Substage DependencyAnalysis $?)
         ?fct <- (Instruction ?target produces ?id)
         ?inst <- (object (is-a Instruction) (name ?id))
         =>
         (retract ?fct)
         (if (not (member$ ?target (send ?inst get-LocalDependencies))) then
           (slot-insert$ ?inst LocalDependencies 1 ?target))
         (if (not (member$ ?target (send ?inst get-Producers))) then 
           (slot-insert$ ?inst Producers 1 ?target)))
;------------------------------------------------------------------------------
(defrule StoreToLoadDependency-Wavefront
         (Stage WavefrontSchedule $?)
         (Substage DependencyAnalysis $?)
         (Evaluate ?p for dependencies starting at ?si)
         (object (is-a StoreInstruction) (Parent ?p) (name ?t0)
                 (TimeIndex ?ti0) (MemoryTarget ?sym0))
         (object (is-a LoadInstruction) (Parent ?p) (name ?t1) 
                 (TimeIndex ?ti1&:(and (>= ?ti1 ?si) (< ?ti0 ?ti1)))
                 (MemoryTarget ?sym1))
         ;(test (or-eq ?sym0 ?sym1 UNKNOWN))
         (test (or (eq ?sym0 ?sym1) (eq ?sym0 UNKNOWN)))
         =>
         (assert (Instruction ?t1 consumes ?t0)
                 (Instruction ?t0 produces ?t1)))
;------------------------------------------------------------------------------
(defrule StoreToStoreDependency-Wavefront
         (Stage WavefrontSchedule $?)
         (Substage DependencyAnalysis $?)
         (Evaluate ?p for dependencies starting at ?si)
         (object (is-a StoreInstruction) (Parent ?p) (name ?t0)
                 (TimeIndex ?ti0) (MemoryTarget ?sym0))
         (object (is-a StoreInstruction) (Parent ?p) (name ?t1) 
                 (TimeIndex ?ti1&:(and (>= ?ti1 ?si) (< ?ti0 ?ti1)))
                 (MemoryTarget ?sym1))
         ;(test (or-eq ?sym0 ?sym1 UNKNOWN))
         (test (or (eq ?sym0 ?sym1) (eq ?sym0 UNKNOWN)))
         =>
         (assert (Instruction ?t1 consumes ?t0)
                 (Instruction ?t0 produces ?t1)))
;------------------------------------------------------------------------------
(defrule LoadToStoreDependency-Wavefront
         (Stage WavefrontSchedule $?)
         (Substage DependencyAnalysis $?)
         (Evaluate ?p for dependencies starting at ?si)
         (object (is-a LoadInstruction) (Parent ?p) (name ?t0)
                 (TimeIndex ?ti0) (MemoryTarget ?sym0)) 
         (object (is-a StoreInstruction) (Parent ?p) (name ?t1) 
                 (TimeIndex ?ti1&:(and (>= ?ti1 ?si) (< ?ti0 ?ti1)))
                 (MemoryTarget ?sym1))
         ;(test (or-eq ?sym0 ?sym1 UNKNOWN))
         (test (or (eq ?sym0 ?sym1) (eq ?sym0 UNKNOWN)))
         =>
         (assert (Instruction ?t1 consumes ?t0)
                 (Instruction ?t0 produces ?t1)))
;------------------------------------------------------------------------------
(defrule FinishedDependencyAnalysis 
         (declare (salience -800))
         (Stage WavefrontSchedule $?)
         (Substage DependencyAnalysis $?)
         ?fct <- (Evaluate ?p for dependencies starting at ?v)
         (object (is-a BasicBlock) (name ?p) (Parent ?r))
         =>
         (assert (Schedule ?p for ?r))
         (retract ?fct))
;------------------------------------------------------------------------------
(defrule RemoveInstructionsFromProducers
         (declare (salience 768))
         (Stage WavefrontSchedule $?)
         (Substage MergeUpdate $?)
         ?fct <- (Remove evidence of ?tInst from instructions ?inst $?insts)
         ?iObj <- (object (is-a Instruction) 
                          (name ?inst) 
                          (Producers $?pb ?tInst $?pa)
                          (LocalDependencies $?ldb ?tInst $?lda))
         =>
         (retract ?fct)
         (assert (Remove evidence of ?tInst from instructions $?insts))
         (modify-instance ?iObj (Producers $?pb $?pa)
                          (LocalDependencies $?ldb $?lda))
         (slot-insert$ ?iObj NonLocalDependencies 1 ?tInst))
;------------------------------------------------------------------------------
(defrule RetractRemoveInstructionsFromProducers
         (declare (salience 768))
         (Stage WavefrontSchedule $?)
         (Substage MergeUpdate $?)
         ?fct <- (Remove evidence of ? from instructions)
         =>
         (retract ?fct))
;------------------------------------------------------------------------------
(defrule StartRecomputeBlock
         (declare (salience 100))
         (Stage WavefrontSchedule $?)
         (Substage MergeUpdate $?)
         ?fct <- (Recompute block ?b)
         ?bb <- (object (is-a BasicBlock) (name ?b) 
                        (Contents $?instructions ?last))
         (object (is-a TerminatorInstruction) (name ?last))
         =>
         (modify-instance ?bb (ReadsFrom) (WritesTo) (HasMemoryBarrier FALSE))
         (retract ?fct)
         (assert (Recompute block ?b with instructions $?instructions)))
;------------------------------------------------------------------------------
(defrule RecomputeNonMemoryInstructionForBlock
         (declare (salience 99))
         (Stage WavefrontSchedule $?)
         (Substage MergeUpdate $?)
         ?fct <- (Recompute block ?b with instructions ?inst $?rest)
         (object (is-a BasicBlock) (name ?b))
         (object (is-a Instruction&~LoadInstruction&~StoreInstruction) 
                 (name ?inst) (Parent ?b))
         =>
         (retract ?fct)
         (assert (Recompute block ?b with instructions $?rest)))
;------------------------------------------------------------------------------
(defrule RecomputeLoadInstructionForBlock
         (declare (salience 99))
         (Stage WavefrontSchedule $?)
         (Substage MergeUpdate $?)
         ?fct <- (Recompute block ?b with instructions ?inst $?rest)
         (object (is-a LoadInstruction) (name ?inst) (Parent ?b) 
                 (MemoryTarget ?mt)) 
         ?bb <- (object (is-a BasicBlock) (name ?b))
         =>
         (if (not (member$ ?mt (send ?bb get-ReadsFrom))) then
           (slot-insert$ ?bb ReadsFrom 1 ?mt))
         (retract ?fct)
         (assert (Recompute block ?b with instructions $?rest)))
;------------------------------------------------------------------------------
(defrule RecomputeStoreInstructionForBlock
         (declare (salience 99))
         (Stage WavefrontSchedule $?)
         (Substage MergeUpdate $?)
         ?fct <- (Recompute block ?b with instructions ?inst $?rest)
         (object (is-a StoreInstruction) (name ?inst) (Parent ?b) 
                 (MemoryTarget ?mt))
         ?bb <- (object (is-a BasicBlock) (name ?b))
         =>
         (if (not (member$ ?mt (send ?bb get-WritesTo))) then
           (slot-insert$ ?bb WritesTo 1 ?mt))
         (retract ?fct)
         (assert (Recompute block ?b with instructions $?rest)))
;------------------------------------------------------------------------------
(defrule FinishRecomputationForBlock
         (declare (salience 98))
         (Stage WavefrontSchedule $?)
         (Substage MergeUpdate $?)
         ?fct <- (Recompute block ?b with instructions)
         ?bb <- (object (is-a BasicBlock) (name ?b) (ReadsFrom $?rf)
                        (WritesTo $?wt))
         =>
         (retract ?fct)
         (if (or (member$ UNKNOWN ?rf)
                 (member$ UNKNOWN ?wt)) then
           (modify-instance ?bb (HasMemoryBarrier TRUE))))
;------------------------------------------------------------------------------
; Now we need to rename operands as need be within the blocks that these
; instructions have been scheduled into
;------------------------------------------------------------------------------
(defrule AssertReplacementActions
         "Iterates through the replacement actions multifield and asserts facts 
         related to the replacement of given values with another value"
         (declare (salience 100))
         (Stage WavefrontSchedule $?)
         (Substage Rename $?)
         (object (is-a PathAggregate) (Parent ?e) 
                 (ReplacementActions $? ?orig ?new ! $?))
         =>
         ; I have turned you into a cheese sandwich, what do you say to that?
         (assert (Replace uses of ?orig with ?new for block ?e)))
;------------------------------------------------------------------------------
(defrule ReplaceUses
         (declare (salience 20))
         (Stage WavefrontSchedule $?)
         (Substage Rename $?)
         ?fct <- (Replace uses of ?orig with ?new for block ?e)
         (object (is-a Instruction) (name ?orig) (Pointer ?oPtr))
         (object (is-a Instruction) (name ?new) (Pointer ?nPtr))
         (object (is-a BasicBlock) (name ?e) (Contents $? ?new $?rest))
         =>
         (retract ?fct)
         (bind ?ptrList (create$))
         (bind ?symList (create$))
         (bind ?i0 1)
         (progn$ (?var $?rest)
                 (bind ?obj (symbol-to-instance-name ?var))
                 (if (member$ ?orig (send ?obj get-Operands)) then
                   (bind ?ptrList (insert$ ?ptrList ?i0 (send ?obj get-Pointer)))
                   (bind ?symList (insert$ ?symList ?i0 ?var))
                   (bind ?i0 (+ ?i0 1))))
         (assert ({ clips ! ?orig => ?new for ?symList })
                 ({ llvm ! ?oPtr => ?nPtr for ?ptrList })))
;------------------------------------------------------------------------------
(defrule ReplaceUsesInLLVM
         (declare (salience -1))
         (Stage WavefrontSchedule $?)
         (Substage Rename $?)
         ?fct <- ({ llvm ! ?from => ?to for $?p2 })
         =>
         (if (llvm-replace-uses ?from ?to ?p2) then 
           (retract ?fct) 
           else
           (printout t
                     "Some kind of error occured when trying to replace uses. " 
                     crlf "Make sure that you've done arguments correctly. " 
                     crlf "The failing rule is ReplaceUsesInLLVM." crlf
                     "?from = " ?from crlf
                     "?to = " ?to crlf
                     "?p2 = " ?p2 crlf
                     "Now I'm exiting" crlf)
           (halt)))
;------------------------------------------------------------------------------
(defrule ReplaceUsesInCLIPS
         (declare (salience -1))
         (Stage WavefrontSchedule $?)
         (Substage Rename $?)
         ?fct <- ({ clips ! ?from => ?to for ?symbol $?rest })
         ?inst <- (object (is-a Instruction) (name ?symbol) 
                          (Operands $?operands) (LocalDependencies $?locDep)
                          (NonLocalDependencies $?nLocDep))
         =>
         (modify-instance ?inst (Operands) (LocalDependencies) 
                          (NonLocalDependencies))
         (retract ?fct)
         (assert ({ clips ! ?from => ?to for $?rest })
                 ({ clips ! ?from => ?to replacement ?symbol 
                    operands $?operands })
                 ({ env: clips translation: ?from => ?to action: replacement
                    in: ?symbol type: local-dependencies
                    contents: $?locDep })
                 ({ env: clips translation: ?from => ?to action: replacement
                    in: ?symbol type: non-local-dependencies
                    contents: $?nLocDep })))
;------------------------------------------------------------------------------
(defrule ReplaceUsesInCLIPS-End
         (declare (salience -1))
         (Stage WavefrontSchedule $?)
         (Substage Rename $?)
         ?fct <- ({ clips ! ?from => ?to for })
         =>
         (retract ?fct))
;------------------------------------------------------------------------------
(defrule ReplaceIndividualLocalDependencyEntries-NoMatch
         (declare (salience -2))
         (Stage WavefrontSchedule $?)
         (Substage Rename $?)
         ?fct <- ({
                   env: clips
                   translation: ?from => ?to 
                   action: replacement
                   in: ?symbol 
                   type: local-dependencies
                   contents: ?curr&~?from $?rest
                   })
         ?inst <- (object (is-a Instruction) (name ?symbol))
         =>
         (object-pattern-match-delay
           (slot-insert$ ?inst LocalDependencies 1 ?curr)
           (retract ?fct)
           (assert ({ env: clips translation: ?from => ?to action: replacement in:
                      ?symbol type: local-dependencies contents: $?rest }))))
;------------------------------------------------------------------------------
(defrule ReplaceIndividualLocalDependencyEntries-Match
         (declare (salience -2))
         (Stage WavefrontSchedule $?)
         (Substage Rename $?)
         ?fct <- ({
                   env: clips
                   translation: ?from => ?to 
                   action: replacement
                   in: ?symbol 
                   type: local-dependencies
                   contents: ?from $?rest
                   })
         ?inst <- (object (is-a Instruction) (name ?symbol))
         =>
         (object-pattern-match-delay
           (slot-insert$ ?inst LocalDependencies 1 ?to)
           (retract ?fct)
           (assert ({ env: clips translation: ?from => ?to action: replacement in:
                      ?symbol type: local-dependencies contents: $?rest }))))
;------------------------------------------------------------------------------
(defrule ReplaceIndividualNonLocalDependencyEntries-NoMatch
         (declare (salience -2))
         (Stage WavefrontSchedule $?)
         (Substage Rename $?)
         ?fct <- ({
                   env: clips
                   translation: ?from => ?to 
                   action: replacement
                   in: ?symbol 
                   type: non-local-dependencies
                   contents: ?curr&~?from $?rest
                   })
         ?inst <- (object (is-a Instruction) (name ?symbol))
         =>
         (object-pattern-match-delay
           (slot-insert$ ?inst NonLocalDependencies 1 ?curr)
           (retract ?fct)
           (assert ({ env: clips translation: ?from => ?to action: replacement in:
                      ?symbol type: local-dependencies contents: $?rest }))))
;------------------------------------------------------------------------------
(defrule ReplaceIndividualNonLocalDependencyEntries-Match
         (declare (salience -2))
         (Stage WavefrontSchedule $?)
         (Substage Rename $?)
         ?fct <- ({
                   env: clips
                   translation: ?from => ?to 
                   action: replacement
                   in: ?symbol 
                   type: non-local-dependencies
                   contents: ?from $?rest
                   })
         ?inst <- (object (is-a Instruction) (name ?symbol))
         =>
         (object-pattern-match-delay
           (slot-insert$ ?inst NonLocalDependencies 1 ?to)
           (retract ?fct)
           (assert ({ env: clips translation: ?from => ?to action: replacement in:
                      ?symbol type: non-local-dependencies contents: $?rest }))))
;------------------------------------------------------------------------------
(defrule ReplaceIndividualInstructionUses-NoMatch
         (declare (salience -2))
         (Stage WavefrontSchedule $?)
         (Substage Rename $?)
         ?fct <- ({ clips ! ?f => ?t replacement ?s operands ?op&~?f $?ops })
         ?inst <- (object (is-a Instruction) (name ?s))
         =>
         (slot-insert$ ?inst Operands 1 ?op)
         (retract ?fct)
         (assert ({ clips ! ?f => ?t replacement ?s operands $?ops })))
;------------------------------------------------------------------------------
(defrule ReplaceIndividualInstructionUses-Match
         (declare (salience -2))
         (Stage WavefrontSchedule $?)
         (Substage Rename $?)
         ?fct <- ({ clips ! ?f => ?t replacement ?s operands ?f $?ops })
         ?inst <- (object (is-a Instruction) (name ?s))
         =>
         (slot-insert$ ?inst Operands 1 ?t)
         (retract ?fct)
         (assert ({ clips ! ?f => ?t replacement ?s operands $?ops })))
;------------------------------------------------------------------------------
(defrule ReplaceIndividualInstructionUses-Empty
         (declare (salience -2))
         (Stage WavefrontSchedule $?)
         (Substage Rename $?)
         ?fct <- ({ clips ! ?f => ?t replacement ?s operands })
         =>
         (retract ?fct))
;------------------------------------------------------------------------------
; Rules associated with the act of actually scheduling instructions
; into blocks on the wavefront
;------------------------------------------------------------------------------
(defrule AssertScheduleCPVIntoTargetBlock 
         (Stage WavefrontSchedule $?)
         (Substage Merge $?)
         (object (is-a Wavefront) (Parent ?r) (Contents $? ?e $?))
         (object (is-a Diplomat) (name ?e) (IsOpen TRUE))
         ?agObj <- (object (is-a PathAggregate) (Parent ?e) 
                           (MovableCompensationPathVectors $?cpvs)) 
         =>
         (if (> (length$ $?cpvs) 0) then
           (modify-instance ?agObj (MovableCompensationPathVectors)))
         (progn$ (?cpv $?cpvs)
                 (assert (Determine schedule style for ?cpv into block ?e))))
;------------------------------------------------------------------------------
(defrule ScheduleStyleForCPVIsMove
         "This rule attempts to determine if the CPV should be moved into the 
         given block on the wavefront. If this is true then the fact to perform 
         this action will be asserted"
         (Stage WavefrontSchedule $?)
         (Substage Merge $?)
         ?fct <- (Determine schedule style for ?cpv into block ?e)
         (object (is-a BasicBlock) (name ?e) (Paths $?paths))
         (object (is-a CompensationPathVector) (name ?cpv)
                 (Paths $?cpvPaths))
         ;the two sets are the same
         (test (equal$ ?paths ?cpvPaths))
         =>
         (retract ?fct)
         (assert (Move ?cpv into ?e)))
;------------------------------------------------------------------------------
(defrule ScheduleStyleForCPVIsCompensate
         "This rule attempts to determine if the CPV should be copied into the 
         given block on the wavefront. If this is true then the fact to perform 
         this action will be asserted."
         (Stage WavefrontSchedule $?)
         (Substage Merge $?)
         ?fct <- (Determine schedule style for ?cpv into block ?e)
         (object (is-a BasicBlock) (name ?e) (Paths $?paths))
         (object (is-a CompensationPathVector) (name ?cpv)
                 (Paths $?cpvPaths) (Parent ?i))
         ;there are more paths in the CPV than in the block
         (test (subsetp ?paths ?cpvPaths))
         =>
         (retract ?fct)
         (assert (Clone ?cpv into ?e)))
;------------------------------------------------------------------------------
(defrule RemoveScheduleStyleForCPV
         (declare (salience 1))
         (Stage WavefrontSchedule $?)
         (Substage Merge $?)
         ?fct <- (Determine schedule style for ?cpv into block ?e)
         (object (is-a BasicBlock) (name ?e) (Paths $?paths) (Parent ?q))
         (object (is-a CompensationPathVector) (name ?cpv)
                 (Paths $?cpvPaths) (Parent ?i))
         ?agObj <- (object (is-a PathAggregate) (Parent ?e))
         (test (not (subsetp ?paths ?cpvPaths)))
         =>
         ;TODO: Put code in here to delete a given instruction from the target
         ;      instruction list as well. 
         ;
         ; Eventually, I will detect if we are in a loop. If we are then it is
         ; necessary to figure out which paths remain in the loop and those
         ; that exit. 
         ;this should prevent a potential infinite loop
         ;(printout t "Preventing " ?i " from being scheduled into " ?e crlf)
         (retract ?fct)
         (bind ?ind (member$ ?i (send ?agObj get-InstructionList)))
         (if ?ind then (slot-delete$ ?agObj InstructionList ?ind ?ind)))
;------------------------------------------------------------------------------
(defrule MoveInstructionIntoBlock
         "Moves the given object into bottom of the given block"
         (Stage WavefrontSchedule $?)
         (Substage Merge $?)
         ?fct <- (Move ?cpv into ?e)
         ?newBlock <- (object (is-a BasicBlock) 
                              (name ?e) 
                              (Contents $?blockBefore ?last)
                              (Produces $?nBProds))
         ?agObj <- (object (is-a PathAggregate) 
                           (Parent ?e)
                           (InstructionPropagation $?agIP)
                           (ScheduledInstructions $?agSI)
                           (ReplacementActions $?agRA))
         ?terminator <- (object (is-a TerminatorInstruction) 
                                (Pointer ?tPtr) 
                                (name ?last) 
                                (TimeIndex ?ti) 
                                (Parent ?e))
         ?cpvObject <- (object (is-a CompensationPathVector) 
                               (name ?cpv) 
                               (Parent ?inst)
                               (ScheduleTargets $?cpvST)
                               (Aliases $?cpvAliases))
         ?newInst <- (object (is-a Instruction) 
                             (name ?inst) 
                             (Pointer ?nPtr) 
                             (Parent ?otherBlock) 
                             (DestinationRegisters ?register) 
                             (Consumers $?niConsumers))
         ?oldBlock <- (object (is-a BasicBlock) 
                              (name ?otherBlock) 
                              (Produces $?pBefore ?inst $?pRest)
                              (Contents $?before ?inst $?rest))
         ;TODO: add another rule where we have to update the consumers list as
         ;      well
         =>
         (object-pattern-match-delay
           ;(printout t "Scheduled " ?inst " into " ?e crlf)
           (modify-instance ?terminator (TimeIndex (+ ?ti 1)))
           ;(modify-instance ?newBlock (Produces ?nBProds ?register))
           (modify-instance ?oldBlock (Contents $?before $?rest) 
                            (Produces $?pBefore $?pRest))
           ;(modify-instance ?cpvObject (Paths))
           (assert (Remove evidence of ?inst from instructions $?niConsumers)
                   ;(send ?newInst get-Consumers))
                   (Recompute block ?otherBlock))
           (retract ?fct)
           (if (eq (class ?inst)
                   StoreInstruction) then
             (modify-instance ?agObj 
                              (ScheduledInstructions $?agSI ?inst ?register)
                              (ReplacementActions $?agRA ?inst ?inst !))
             ;(slot-insert$ ?agObj ScheduledInstructions 1 ?inst ?register)
             (modify-instance ?newBlock 
                              (Produces $?nBProds ?register)
                              (Contents $?blockBefore ?inst ?last))
             (modify-instance ?cpvObject 
                              (Paths)
                              (ScheduleTargets ?cpvST ?e ?inst)
                              (Aliases $?cpvAliases ?inst ?e))
             (llvm-unlink-and-move-instruction-before ?nPtr ?tPtr)
             ;(slot-insert$ ?cpvObject ScheduleTargets 1 ?e ?inst)
             ;(slot-insert$ ?cpvObject Aliases 1 ?inst ?e)
             ;(slot-insert$ ?agObj ReplacementActions 1 ?inst ?inst !)
             else
             (bind ?newName (sym-cat movedinstruction. (gensym*) . ?inst))
             (modify-instance ?cpvObject (Paths)
                              (ScheduleTargets ?cpvST ?e ?newName)
                              (Aliases ?cpvAliases ?newName ?e))
             ;(slot-insert$ ?cpvObject ScheduleTargets 1 ?e ?newName)
             ;(slot-insert$ ?cpvObject Aliases 1 ?newName ?e)
             ;(slot-insert$ ?agObj ReplacementActions 1 ?inst ?newName !)
             (modify-instance ?newBlock 
                              (Produces $?nBProds ?register)
                              (Contents $?blockBefore ?newName ?last))
             (bind ?newPtr (llvm-clone-instruction ?nPtr ?newName))
             ;purge the list of producers and consumers
             (duplicate-instance ?inst to ?newName 
                                 (name ?newName) 
                                 (Name ?newName)
                                 (Pointer ?newPtr) 
                                 (Producers) 
                                 (Consumers)
                                 (NonLocalDependencies) 
                                 (LocalDependencies)
                                 (TimeIndex ?ti) 
                                 (Parent ?e))
             (llvm-move-instruction-before ?newPtr ?tPtr)
             (slot-insert$ ?oldBlock UnlinkedInstructions 1 ?inst)
             (modify-instance ?agObj (ReplacementActions $?agRA ?inst ?newName !)
                              (InstructionPropagation $?agIP ?inst ?newName ?e !)
                              (ScheduledInstructions $?agSI ?inst)))))
;(slot-insert$ ?agObj InstructionPropagation 1 ?inst ?newName ?e !)
;(slot-insert$ ?agObj ScheduledInstructions 1 ?inst))))
;------------------------------------------------------------------------------
(defrule CloneInstructionIntoBlock
         "Moves the given object into bottom of the given block"
         (Stage WavefrontSchedule $?)
         (Substage Merge $?)
         ?fct <- (Clone ?cpv into ?e)
         ?newBlock <- (object (is-a BasicBlock) 
                              (name ?e) 
                              (Contents $?blockBefore ?last))
         ?agObj <- (object (is-a PathAggregate) 
                           (Parent ?e))
         ?terminator <- (object (is-a TerminatorInstruction) 
                                (Pointer ?tPtr) 
                                (name ?last) 
                                (TimeIndex ?ti) 
                                (Parent ?e))
         ?cpvObject <- (object (is-a CompensationPathVector) 
                               (name ?cpv) 
                               (Parent ?inst) 
                               (Paths $?cpvPaths))
         ?newInst <- (object (is-a Instruction) 
                             (name ?inst) 
                             (Pointer ?nPtr) 
                             (Parent ?otherBlock) 
                             (DestinationRegisters ?register))
         =>
         ;we also need to update all CPVs within 
         (retract ?fct)
         (object-pattern-match-delay
           (bind ?newName 
                 (sym-cat compensation.copy.
                          (gensym*). 
                          ?inst))
           (bind ?newPtr 
                 (llvm-clone-instruction ?nPtr 
                                         ?newName))
           ;purge the list of producers and consumers
           (duplicate-instance ?inst to ?newName 
                               (name ?newName) 
                               (Name ?newName)
                               (Pointer ?newPtr) 
                               (Parent ?e)
                               (TimeIndex (+ ?ti 1)))
           (llvm-move-instruction-before ?newPtr 
                                         ?tPtr)
           ;we add the original name so that we don't have to do
           ; an insane number of updates to the CPVs that follow
           ; this object
           (if (eq (class ?inst)
                   StoreInstruction) then
             (slot-insert$ ?agObj ScheduledInstructions 1 ?inst ?register)
             else
             (slot-insert$ ?agObj InstructionPropagation 1 ?inst ?newName ?e !)
             (slot-insert$ ?agObj ScheduledInstructions 1 ?inst))
           (slot-insert$ ?newBlock Produces 1 ?register)
           (modify-instance ?newBlock (Contents $?blockBefore ?newName ?last))
           (slot-insert$ ?cpvObject ScheduleTargets 1 ?e ?newName)
           (slot-insert$ ?cpvObject Aliases 1 ?newName ?e) 
           (slot-insert$ ?agObj ReplacementActions 1 ?inst ?newName !)
           (assert (Recompute block ?otherBlock)
                   (Reopen blocks from ?cpv))
           (bind ?leftOvers (create$))
           (progn$ (?z ?cpvPaths)
                   (bind ?cPath (symbol-to-instance-name ?z))
                   (if (not (member$ ?e (send ?cPath get-Contents))) then
                     (bind ?leftOvers (insert$ ?leftOvers 1 ?z))))
           (modify-instance ?cpvObject (Paths ?leftOvers))))
;------------------------------------------------------------------------------
(defrule FAILURE-CLONE
         (declare (salience -768))
         (Stage WavefrontSchedule $?)
         (Substage Merge $?)
         (Clone ?cpv into ?e)
         (object (is-a CompensationPathVector) (name ?cpv) (Parent ?p))
         =>
         (printout t "ERROR: Didn't clone " ?p " into " ?e crlf)
         (halt))
;------------------------------------------------------------------------------
(defrule FAILURE-MOVE
         (declare (salience -768))
         (Stage WavefrontSchedule $?)
         (Substage Merge $?)
         (Move ?cpv into ?e)
         (object (is-a CompensationPathVector) (name ?cpv) (Parent ?p))
         =>
         (printout t "ERROR: Didn't move " ?p " into " ?e crlf)
         (halt))
;------------------------------------------------------------------------------
(defrule FAILURE-SCHEDULE-STYLE
         (declare (salience -768))
         (Stage WavefrontSchedule $?)
         (Substage Merge $?)
         (Determine schedule style for ?cpv into block ?e)
         ?o <- (object (is-a CompensationPathVector) (name ?cpv) (Parent ?p)
                       (Paths $?cpvPaths))
         ?pa <- (object (is-a PathAggregate) (Parent ?e))
         (object (is-a Instruction) (name ?p) (Parent ?bb))
         (object (is-a BasicBlock) (name ?e) (Parent ?r) (Paths $?paths))
         (object (is-a Wavefront) (Parent ?r) (Contents $?z) (Closed $?y))
         (object (is-a Region) (name ?r) (Entrances ?x $?))
         (object (is-a BasicBlock) (name ?x) (Paths $?allPaths))
         =>
         (printout t "ERROR: Couldn't figure out scheduling stype for " ?p 
                   " which is targeted for " ?e crlf
                   "Blocks on the wavefront = " ?z crlf
                   "Closed Blocks = " ?y crlf
                   "For reference ?cpvPaths = " ?cpvPaths crlf
                   "For reference aliases of ?cpv are = " 
                   (send ?o get-Aliases) crlf
                   "For reference ?paths = " ?paths crlf
                   "Parent of " ?p " is " ?bb crlf
                   "Printing out the path aggregate for " ?p crlf )
         (send ?pa print)
         (progn$ (?apath ?allPaths)
                 (printout t "  " ?apath " = " 
                           (send (symbol-to-instance-name ?apath) 
                                 get-Contents) 
                           crlf))
         (facts)
         (halt))
;------------------------------------------------------------------------------
; Rules for reopening blocks on the wavefront
;------------------------------------------------------------------------------
(defrule AssertReopenBlocksOnWavefront
         (Stage WavefrontSchedule $?)
         (Substage ReopenBlocks $?)
         ?fct <- (Reopen blocks from ?cpv)
         ?obj <- (object (is-a CompensationPathVector) (name ?cpv) 
                         (Failures $?failures))
         =>
         (retract ?fct)
         (modify-instance ?obj (Failures))
         (assert (From ?cpv reopen $?failures)))
;------------------------------------------------------------------------------
(defrule ReopenBlockOnWavefront
         (Stage WavefrontSchedule $?)
         (Substage ReopenBlocks $?)
         ?fct <- (From ?cpv reopen ?fail $?failures)
         ?wave <- (object (is-a Wavefront) (name ?w) (Closed $?a ?fail $?b)
                          (Contents $?cnts))
         ?bb <- (object (is-a BasicBlock) (name ?fail) (IsOpen FALSE))
         ?pa <- (object (is-a PathAggregate) (Parent ?fail)
                        (ImpossibleCompensationPathVectors $?icpv))
         =>
         (modify-instance ?bb (IsOpen TRUE))
         (modify-instance ?pa (ImpossibleCompensationPathVectors)
                          (TargetCompensationPathVectors $?icpv))
         (progn$ (?q ?icpv)
                 (slot-insert$ ?pa InstructionList 1 
                               (send (symbol-to-instance-name ?q) get-Parent)))
         (modify-instance ?wave (Contents $?cnts ?fail) (Closed ?a ?b))
         (retract ?fct)
         (assert (From ?cpv reopen $?failures)))
;------------------------------------------------------------------------------
(defrule ReaddFailureToCPV
         (Stage WavefrontSchedule $?)
         (Substage ReopenBlocks $?)
         ?fct <- (From ?cpv reopen ?fail $?failures)
         ?wave <- (object (is-a Wavefront) (name ?w) (Closed $?c))
         (test (not (member$ ?fail $?c)))
         ?obj <- (object (is-a CompensationPathVector) (name ?cpv))
         =>
         (slot-insert$ ?obj Failures 1 ?fail)
         (retract ?fct)
         (assert (From ?cpv reopen $?failures)))
;------------------------------------------------------------------------------
(defrule RetractEmptyReopenFact
         (Stage WavefrontSchedule $?)
         (Substage ReopenBlocks $?)
         ?fct <- (From ? reopen)
         =>
         (retract ?fct))
;------------------------------------------------------------------------------
; Debug stats at the end 
;------------------------------------------------------------------------------
(defrule PrintRules
         (Stage Final $?)
         (Debug)
         (Rules)
         =>
         (rules))
;------------------------------------------------------------------------------
(defrule PrintFacts
         (Stage Final $?)
         (Debug)
         (Facts)
         =>
         (facts))
;------------------------------------------------------------------------------

(defrule Separator
         (Stage Final $?)
         (Debug)
         (Separator)
         =>
         (printout t "====================================================" crlf))
;------------------------------------------------------------------------------
(defrule ProfileInfo
         (Stage Final $?)
         (Debug)
         (Profile)
         =>
         (profile-info))
;------------------------------------------------------------------------------
(defrule FinalMemoryConsumption
         (Stage Final $?)
         (Debug)
         (Memory)
         =>
         (printout t "Final Memory Consumption: " (/ (mem-used) 131072) " MB" crlf
                   "Memory Requests: " (mem-requests) crlf))
;------------------------------------------------------------------------------
; Memory related functions - ugh!
;------------------------------------------------------------------------------
(defrule CleanupMemory
         "Releases unused memory from CLIPS"
         (Stage Final $?)
         =>
         (release-mem))
