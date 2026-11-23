import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFactsOfNormalHolds
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_facts_of_normal_holds : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → p.Prime → IsNoetherianRing R → IsFractionRing R Ω → IsIntegrallyClosedIn R Ω → ∀ φ : Equiv.Perm Sg, D.TestFacts R p w χ φ → D.Good₁ R p χ → D.Good₂ R p χ → D.Facts R p w χ φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.lattice_facts_of_normal | exact GlobalTheory.CompanionTheory.Ar.Num.lattice_facts_of_normal | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.lattice_facts_of_normal <;> assumption)
