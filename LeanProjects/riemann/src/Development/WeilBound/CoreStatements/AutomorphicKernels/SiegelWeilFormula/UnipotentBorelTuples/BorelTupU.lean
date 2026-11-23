import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnipotentBorelTuples.TranslationInvariantFunctionalHaar
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeylTheta.TWeylOf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnitaryChartEquiv.CEquivApply

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.TowU

namespace PositivityTheory.SiegelWeilFormula.TW.Twu

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

open PositivityTheory.SiegelWeilFormula.TBij.Adp PositivityTheory.SiegelWeilFormula.KTunit

local instance (priority := high) measTupU {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] :
    MeasurableSpace (κ → AF F) := borel _

local instance borelTupU {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] : BorelSpace (κ → AF F) := ⟨rfl⟩

theorem uniq : Uniq := by
  classical
  intro F E _ _ _ _ _ σ d ν hν Λ hΛ hinv
  have hψ : IsStd d.B.ψ := d.ok.good.std
  obtain ⟨τ, S0, S0', C, hop, hT⟩ := Tunit.T_chart d
  by_cases hC : C = 0
  · refine ⟨0, fun Φ hΦ => ?_⟩
    have h0 : d.T Φ = 0 := funext fun X => by rw [hT Φ hΦ X, hC, zero_mul]; rfl
    rw [(TBij.tBij F E σ d).2.2 Φ hΦ h0, map_zero, zero_mul]
  have rhoS : ∀ w, ∀ φ ∈ schA F d.κ, S0 (d.dd.rho d.B.ψ w φ) = schr d.B.ψ (c0 d τ w) (S0 φ) := by
    intro w φ hφ
    simp only [Darboux.rho]
    rw [hop.Heisenberg₂ _ _ hφ, LinearEquiv.symm_apply_apply]
  have rhoS' : ∀ w, ∀ φ ∈ schA F d.κ, S0' (schr d.B.ψ (c0 d τ w) φ) = d.dd.rho d.B.ψ w (S0' φ) := by
    intro w φ hφ
    have h1 := rhoS w (S0' φ) (hop.pres' φ hφ)
    rw [hop.right φ hφ] at h1
    have hm : d.dd.rho d.B.ψ w (S0' φ) ∈ schA F d.κ :=
      GlobalTheory.HeisSchA.schr_mem_schA d.B.ψ hψ _ _ (hop.pres' φ hφ)
    rw [← h1, hop.left _ hm]
  obtain ⟨hμ, hint⟩ := map_haar d τ ν hν
  obtain ⟨c, hc⟩ := translation_invariant_functional_haar d.B.ψ hψ d.κ (ν.map (cmap d τ)) hμ (Λ ∘ₗ S0') (hop.adm' Λ hΛ) (by
    intro a φ hφ
    have e0 := coordinates_frame d τ (cinv d τ a)
    have ea : (fun k => d.crd (cinv d τ a) (τ k)) = a := cmap_cinv d τ a
    rw [ea] at e0
    rw [← schr_zero_right, ← e0, LinearMap.comp_apply, LinearMap.comp_apply, rhoS' _ φ hφ]
    exact hinv _ _ (hop.pres' φ hφ))
  refine ⟨c / C, fun Φ hΦ => ?_⟩
  have h1 := hc (S0 Φ) (hop.pres Φ hΦ)
  rw [LinearMap.comp_apply, hop.left Φ hΦ] at h1
  rw [h1, ← hint]
  have e2 : ∫ Z, d.T Φ Z ∂ν = C * ∫ Z, S0 Φ (cmap d τ Z) ∂ν := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun Z => hT Φ hΦ Z)
  rw [e2]
  field_simp

end PositivityTheory.SiegelWeilFormula.TW.Twu

end
