import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobGIsArithFrobAndSign
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobG_isArithFrobAt_and_sign_eq_jacobiSym : ∀ (D : D7) (l : ℕ) [Fact l.Prime], l ∉ D.host.small → l ≠ D.host.q → l ≠ D.host.d → (∀ (Q : Ideal (𝓞 D.host.E)) [Q.IsPrime] [Q.LiesOver (Ideal.span {(l : ℤ)})], IsArithFrobAt ℤ (D.host.sigmaOf (DV.frobG D l)) Q) ∧ ((((DV.frobG D l).1.2 : ℤˣ) : ℤ) = jacobiSym (-(D.host.d : ℤ)) l) := by
  first | exact @GlobalTheory.FrobSign.frobG_isArithFrob_and_sign | exact GlobalTheory.FrobSign.frobG_isArithFrob_and_sign | (intros; apply GlobalTheory.FrobSign.frobG_isArithFrob_and_sign <;> assumption)
