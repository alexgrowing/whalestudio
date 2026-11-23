import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacterLatticeKernelLocallyFree
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_lattice_kernel_locally_free : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → D.Good₂ R p χ → (∀ τ, mulLat w (stdLat R _) ≤ D.af R p (χ τ)) → ∀ τ, LocFree R (r τ) (D.kerH R p τ (χ τ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.KerFree.main | exact GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.KerFree.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.KerFree.main <;> assumption)
