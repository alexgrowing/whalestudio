import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomorphismTrivialOnKernel
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetGroupMorphismBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FracIdExistsTotPos

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monomorphism_trivial_on_kernel : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π →
    (∃ N : ℕ, RingHom.ker π ^ N = ⊥) → ∀ (A : Over (Sp R)) [GrpObj A], IsProper A.hom →
    ∀ (n : ℕ) (D : Over (Sp R)) [GrpObj D], IsSeparated D.hom → ∀ (x : Fin n → (A ⟶ D)), (∀ j, IsMonHom (x j)) →
    (∀ (T₀ : Over (Sp R₀)) (y : Over.mk (T₀.hom ≫ spMap π) ⟶ A), (∀ j, y ≫ x j = 1) → y = 1) →
    ∀ (T : Over (Sp R)) (y : T ⟶ A), (∀ j, y ≫ x j = 1) → y = 1 := by
  first | exact @GlobalTheory.KernelThickening.kernel_trivial_of_nilpotent | exact GlobalTheory.KernelThickening.kernel_trivial_of_nilpotent | (intros; apply GlobalTheory.KernelThickening.kernel_trivial_of_nilpotent <;> assumption)
