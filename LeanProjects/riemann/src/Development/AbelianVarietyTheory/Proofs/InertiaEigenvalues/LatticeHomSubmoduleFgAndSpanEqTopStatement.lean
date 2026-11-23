import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeHomSubmoduleFgAndSpanEqTop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdEApply
open GlobalTheory.UnitLemma GlobalTheory.StableLatCount Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_hom_submodule_fg_and_span_eq_top : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (E : Type) [Field E] [Algebra O E] [IsFractionRing O E] (A₁ A₂ : Type) [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂] [Algebra O A₁] [Algebra O A₂] [IsScalarTower O E A₁] [IsScalarTower O E A₂] [Module.Finite E A₁] [Module.Finite E A₂] (M₁ : Submodule O A₁) (M₂ : Submodule O A₂), IsLat O E M₁ → IsLat O E M₂ → (homLat E M₁ M₂).FG ∧ Submodule.span E (homLat E M₁ M₂ : Set (A₂ →ₗ[E] A₁)) = ⊤ := by
  first | exact @GlobalTheory.StableLatCount.homLat_fg_and_span_eq_top | exact GlobalTheory.StableLatCount.homLat_fg_and_span_eq_top | (intros; apply GlobalTheory.StableLatCount.homLat_fg_and_span_eq_top <;> assumption)
