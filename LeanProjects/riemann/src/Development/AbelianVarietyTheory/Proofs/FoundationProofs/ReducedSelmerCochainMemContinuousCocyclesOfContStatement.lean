import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReducedSelmerCochainMemContinuousCocyclesOfCont
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResPlaneSmulEqZero
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduced_selmer_cochain_mem_continuous_cocycles_of_cont : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (c : Coef l) (hO : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1), Continuous W → ∀ z ∈ divSelCoc c W S A, ∀ y : Fin 2 → Qbar l, VecE c y → (∀ s i, (l : Qbar l) * z s i - (mat W s *ᵥ y - y) i ∈ c.O) → descS S (resCoc c W z y) ∈ Z1 (resRep c W hO S hN) := by
  first | exact @GlobalTheory.Ord2.descS_resCoc_mem_z1_of_continuous | exact GlobalTheory.Ord2.descS_resCoc_mem_z1_of_continuous | (intros; apply GlobalTheory.Ord2.descS_resCoc_mem_z1_of_continuous <;> assumption)
