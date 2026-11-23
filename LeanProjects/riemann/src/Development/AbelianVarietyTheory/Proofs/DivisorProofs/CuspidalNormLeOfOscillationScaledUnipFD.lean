import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemBand
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsNormRconvLeSiegel
import GroundTheory.AutomorphicForms.ReductionSiegel
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped NumberField.AdeleRing

namespace GlobalTheory.CuspTail

theorem norm_le_of_osc_scaledUnipFD : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ), 0 < r → r < a →
    ∀ φ : GA E a → ℂ, (∀ γ g, φ (ratGL E a γ * g) = φ g) → IsCuspidal φ → Continuous φ →
    ∀ M : ℕ, 0 < M → ∀ (x : GA E a) (B : ℝ),
      (∀ X ∈ GroundTheory.Automorphic.scaledUnipFD E a r M, ‖φ (unip X * x) - φ x‖ ≤ B) → ‖φ x‖ ≤ B := by
  intro E _ _ _ a r hr hra φ _ hcusp hφ M hM x B hB
  set D := GroundTheory.Automorphic.scaledUnipFD E a r M with hDdef
  set ν := GroundTheory.Automorphic.AutomorphicForm.unipMeasure E a r
  have hD : IsAddFundamentalDomain (ratN E a r) D ν :=
    GroundTheory.Automorphic.isAddFundamentalDomain_scaledUnipFD hM
  have hD1 : ν D = 1 := GroundTheory.Automorphic.unipMeasure_scaledUnipFD hM
  have hunip : (unip : (BlockIx a r → Ad E) → GA E a) =
      (GroundTheory.Automorphic.AutomorphicForm.unipGL (n := a) (r := r) (R := Ad E)) :=
    funext fun X => Units.ext rfl
  have hcont : Continuous fun X : BlockIx a r → Ad E => φ (unip X * x) := by
    refine hφ.comp (Continuous.mul ?_ continuous_const)
    rw [hunip]
    exact GroundTheory.Automorphic.AutomorphicForm.continuous_unipGL
  obtain ⟨C, hC, hDC⟩ :=
    GroundTheory.Automorphic.CuspidalSpectrum.exists_isCompact_superset_scaledUnipFD (K := E) (n := a) r hM
  have hint : IntegrableOn (fun X => φ (unip X * x)) D ν :=
    (hcont.continuousOn.integrableOn_compact hC).mono_set hDC
  have hmean : ∫ X in D, φ (unip X * x) ∂ν = 0 :=
    hcusp r hr hra ν D inferInstance hD x
  have hfin : ν D < ⊤ := by rw [hD1]; exact ENNReal.one_lt_top
  have hkey : ∫ X in D, (φ (unip X * x) - φ x) ∂ν = -φ x := by
    rw [integral_sub hint (integrableOn_const hfin.ne)]
    simp only [hmean, setIntegral_const, measureReal_def, hD1, ENNReal.toReal_one, one_smul, zero_sub]
  calc ‖φ x‖ = ‖∫ X in D, (φ (unip X * x) - φ x) ∂ν‖ := by rw [hkey, norm_neg]
    _ ≤ B * ν.real D := norm_setIntegral_le_of_norm_le_const hfin hB
    _ = B := by simp [measureReal_def, hD1]

end GlobalTheory.CuspTail
