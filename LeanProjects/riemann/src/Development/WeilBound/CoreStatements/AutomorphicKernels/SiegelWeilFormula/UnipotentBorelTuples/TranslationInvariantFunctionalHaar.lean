import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFourierRealisesWeylElementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterInvariantAdelicFormEqMulEvalZeroStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DarbouxCharts.TChart

noncomputable section

open scoped Matrix
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU

namespace PositivityTheory.SiegelWeilFormula.TW.Twu

variable {F : Type} [Field F] [NumberField F]

theorem schr_zero_left (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ] (y : κ → AF F) (φ : (κ → AF F) → ℂ) :
    schr ψ (0, y) φ = fun x => ψ (x ⬝ᵥ y) * φ x := by
  funext x
  simp [schr]

theorem schr_zero_right (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ] (a : κ → AF F) (φ : (κ → AF F) → ℂ) :
    schr ψ (a, 0) φ = fun x => φ (x + a) := by
  funext x
  simp [schr]

theorem translation_invariant_functional_haar (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (κ : Type) [Fintype κ] [DecidableEq κ]
    (μ : @Measure (κ → AF F) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ)
    (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (hl : l ∈ (adeleClass F).adm κ)
    (hinv : ∀ a : κ → AF F, ∀ φ ∈ schA F κ, l (fun x => φ (x + a)) = l φ) :
    ∃ c : ℂ, ∀ φ ∈ schA F κ, l φ = c * ∫ x, φ x ∂μ := by
  obtain ⟨S, S', hS, hSf⟩ := GlobalTheory.T.adelicFourier_realises_weylElement F ψ hψ κ μ hμ (fun _ => 1)
  have hl' : l ∘ₗ S' ∈ (adeleClass F).adm κ := hS.adm' l hl
  have hchar : ∀ (y : κ → AF F), ∀ φ ∈ schA F κ,
      (l ∘ₗ S') (fun x => ψ (x ⬝ᵥ y) * φ x) = (l ∘ₗ S') φ := by
    intro y φ hφ
    have hφ₁m : S' φ ∈ schA F κ := hS.pres' φ hφ
    have hφeq : S (S' φ) = φ := hS.right φ hφ
    have htr : schr ψ (-y, 0) (S' φ) ∈ schA F κ := by
      rw [schr_zero_right]
      exact GlobalTheory.SchwartzTranslate.schA_translate F (-y) hφ₁m
    have key : S (schr ψ (-y, 0) (S' φ)) = fun x => ψ (x ⬝ᵥ y) * φ x := by
      rw [hS.Heisenberg₂ _ _ hφ₁m, hφeq, ← schr_zero_left]
      congr 1
      ext i <;> simp
    rw [← key, LinearMap.comp_apply, hS.left _ htr, LinearMap.comp_apply, schr_zero_right]
    exact hinv (-y) (S' φ) hφ₁m
  obtain ⟨c, hc⟩ := GlobalTheory.T.character_invariant_adelic_form_eq_mul_eval_zero F ψ hψ κ (l ∘ₗ S') hl' hchar
  refine ⟨c, fun φ hφ => ?_⟩
  have h1 : l φ = (l ∘ₗ S') (S φ) := by
    rw [LinearMap.comp_apply, hS.left φ hφ]
  rw [h1, hc _ (hS.pres φ hφ), hSf φ hφ 0]
  simp

end PositivityTheory.SiegelWeilFormula.TW.Twu

end
