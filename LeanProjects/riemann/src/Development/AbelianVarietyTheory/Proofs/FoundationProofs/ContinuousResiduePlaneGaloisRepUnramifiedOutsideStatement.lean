import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousResiduePlaneGaloisRepUnramifiedOutside
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResPlaneSmulEqZero
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_residuePlaneGaloisRep_unramifiedOutside : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (S : Finset Pl) (W : R2 Ω l) (c : Coef l) (hO : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1), Continuous W → ContAction (resRep c W hO S hN) := by
  first | exact @GlobalTheory.Ord2.resRep_contAction | exact GlobalTheory.Ord2.resRep_contAction | (intros; apply GlobalTheory.Ord2.resRep_contAction <;> assumption)
