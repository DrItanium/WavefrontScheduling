
(defclass OwnershipDeterminant (is-a TaggedObject) 
 (multislot Claims)
 (multislot IndirectClaims)
 (multislot PotentialChildren)) 
 
(defrule ConstructDeterminantForRegion
 (Stage DeterminantConstruction $?)
 (object (is-a Region) (ID ?r))
 (not (exists (object (is-a OwnershipDeterminant) (Parent ?r))))
 =>
 (make-instance of OwnershipDeterminant (Parent ?r)))

(defrule PopulateDeterminant
 (Stage DeterminantPopulation $?)
 ?fct <- (claim ?a owns ?b)
 ?obj <- (object (is-a OwnershipDeterminant) (Parent ?b))
 ?obj2 <- (object (is-a OwnershipDeterminant) (Parent ?a))
 =>
 (retract ?fct)
 (slot-insert$ ?obj2 PotentialChildren 1 ?b)
 (slot-insert$ ?obj Claims 1 ?a))
;now that we have the set of claims for each region it's necessary to figure
;out which claims are indirect and direct.
(defrule DetermineIndirectClaim
 (Stage DeterminantResolution $?)
 ?t0 <- (object (is-a OwnershipDeterminant) (Parent ?b) (Claims $?z ?a $?x))
 (object (is-a OwnershipDeterminant) (Parent ~?b) 
  (PotentialChildren $? ?b $?) (Claims $? ?a $?))
 ?t1 <- (object (is-a OwnershipDeterminant) (Parent ?a) 
   (PotentialChildren $?z0 ?b $?x0))
 =>
 (slot-insert$ ?t0 IndirectClaims 1 ?a)
 (modify-instance ?t1 (PotentialChildren $?z0 $?x0))
 (modify-instance ?t0 (Claims $?z $?x)))

(defrule DetermineIndirectIndirectClaim
 (Stage DeterminantIndirectResolution $?)
 ?t0 <- (object (is-a OwnershipDeterminant) (Parent ?b) (Claims $?z ?a $?x))
 (object (is-a OwnershipDeterminant) (Parent ~?b&~?a) 
                (IndirectClaims $? ?a $?) (PotentialChildren $? ?b $?))
 ?t1 <- (object (is-a OwnershipDeterminant) (Parent ?a)
                (PotentialChildren $?z0 ?b $?x0))
 =>
 (slot-insert$ ?t0 IndirectClaims 1 ?a)
 (modify-instance ?t0 (Claims $?z $?x))
 (modify-instance ?t1 (PotentialChildren $?z0 $?x0)))
  
(defrule DeleteNonExistentReferences
 (Stage Fixup $?)
 ?region <- (object (is-a Region) (Contents $?a ?b $?c))
 (not (exists (object (ID ?b))))
 =>
 (modify-instance ?region (Contents $?a $?c)))

(defrule UpdateOwnerOfTargetRegion
 (Stage FixupUpdate $?)
 (object (is-a OwnershipDeterminant) (Parent ?p) 
  (Claims ?a))
 ?obj <- (object (is-a Region) (ID ?p))
 =>
 (modify-instance ?obj (Parent ?a)))

(defrule AddNewChildToTargetRegion
 (Stage FixupUpdate $?)
 (object (is-a OwnershipDeterminant) (Parent ?p)
  (PotentialChildren $? ?a $?))
 ?region <- (object (is-a Region) (ID ?p) (Contents $?c))
 (test (eq FALSE (member$ ?a ?c)))
 =>
 (slot-insert$ ?region Contents 1 ?a))

(defrule CleanupOwnershipDeterminants
 (Stage CleanUp-Merger $?)
 ?obj <- (object (is-a OwnershipDeterminant))
 =>
 (unmake-instance ?obj))

(defrule FAILURE-TooManyClaimsOfOwnership
 (Stage Fixup $?)
 (object (is-a OwnershipDeterminant) (Parent ?a) 
         (Claims $?z&:(> (length$ ?z) 1))
         (ID ?name))
 =>
 (printout t "ERROR: " ?name " has more than one claim of ownership on it!"
  crlf "The claims are " ?z crlf)
 (exit))

(defrule FAILURE-NoRemainingClaims
 (Stage Fixup $?)
 (object (is-a OwnershipDeterminant) (Parent ?a) (Claims)
  (PotentialChildren $?pc) (IndirectClaims $?ic))
 (object (is-a Region) (ID ?a) (IsTopLevelRegion FALSE))
 =>
 (printout t "ERROR: " ?a " has no remaining claims!" crlf 
             ?a " has " $?pc " as it's potential children." crlf
             ?a " has " $?ic " as it's indirect claims." crlf)
 (exit))
