import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsEmbExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingFrameDeltaChange
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

noncomputable section

namespace GlobalTheory.LawsFieldChange

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F)

theorem goodOf_comp (σ' : c'.F →+* ℂ) :
    (goodOf c' σ').comp (incF c c' hle) = goodOf c (σ'.comp (incF c c' hle)) := by
  have h : GoodEmb c' σ' ↔ GoodEmb c (σ'.comp (incF c c' hle)) := Iff.rfl
  unfold goodOf
  by_cases hg : GoodEmb c' σ'
  · rw [if_pos hg, if_pos (h.1 hg)]
  · rw [if_neg hg, if_neg (fun h' => hg (h.2 h'))]
    rfl

variable {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

theorem modelWt_unfBC (σ' : c'.F →+* ℂ) (G : WTZ E) :
    modelWt (unfBC hle U σ') G = modelWt (U (σ'.comp (incF c c' hle))) G := by
  have hr : relab c' σ' = relab c (σ'.comp (incF c c' hle)) := funext fun τ => RingHom.ext fun x => rfl
  unfold modelWt
  rw [hr]
  rfl

theorem petAt_unfBC (σ' : c'.F →+* ℂ) (x : ℝ) {D : D7} (V : HSp D)
    (dict : GA D V → Σ k, Frame ((U (σ'.comp (incF c c' hle))).X k).Ψ r) (μ : Measure (AutQ V)) (G : WTZ E)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n) :
    petAt (unfBC hle U σ') x V dict μ G (rulBC hle f) = petAt (U (σ'.comp (incF c c' hle))) x V dict μ G f := by
  have hrd := (rulBC_cusp E H Dw l Xo c c' hle r U a n f hf).1 σ'
  unfold petAt
  rw [hrd, modelWt_unfBC hle U σ' G]
  rfl

end

theorem laws_fieldChange : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j Xo c' (unfBC hle U) (fun σ => dict (σ.comp (incF c c' hle))) ∧ ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f : cuspW Xo c U (wtZ a n), ∃ h : rulBC hle (f : Rul Xo c) ∈ cuspW Xo c' (unfBC hle U) (wtZ a n), ∀ σ : c'.F →+* ℂ, normW (unfBC hle U) (xiR D) (fun _ => D.sp.W j) (fun σ => dict (σ.comp (incF c c' hle))) (wtZ a n) σ ⟨_, h⟩ = normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) (σ.comp (incF c c' hle)) f := by
  intro D j H Dw l Xo c c' hle U dict hL
  refine ⟨?_, ?_⟩
  · exact
      { inR := hL.inR
        host := hL.host
        dat := hL.dat
        levA := hL.levA
        unf := fun σ' hσ' => GlobalTheory.OneMapAll.isUnf_unfExt hle σ' (fun _ => rfl) (hL.unf (σ'.comp (incF c c' hle)) hσ')
        chiTriv := fun σ' hσ' a n hd k γ hγ => by
          rw [laU_unfBC hle U σ' a n]
          exact hL.chiTriv (σ'.comp (incF c c' hle)) hσ' a n hd k γ hγ
        dictU := fun σ' hσ' => hL.dictU (σ'.comp (incF c c' hle)) hσ'
        modelW := fun σ' hσ' => hL.modelW (σ'.comp (incF c c' hle)) hσ' }
  · intro a n _ f
    have hf : (f : Rul Xo c) ∈ cusp Xo c U a n := (cuspW_wtZ (U := U) a n).le f.2
    have hsec : (f : Rul Xo c) ∈ sec Xo c a n := cusp_le_sec _ _ _ _ _ hf
    have hmem : rulBC hle (f : Rul Xo c) ∈ cuspW Xo c' (unfBC hle U) (wtZ a n) := by
      rw [cuspW_wtZ]
      exact (rulBC_cusp _ H Dw l Xo c c' hle D.R.r U a n _ hsec).2.2 hf
    refine ⟨hmem, fun σ' => ?_⟩
    have e1 : normW (unfBC hle U) (xiR D) (fun _ => D.sp.W j) (fun σ => dict (σ.comp (incF c c' hle))) (wtZ a n) σ'
        ⟨_, hmem⟩ = petAt (unfBC hle U (goodOf c' σ')) (xiR D) (D.sp.W j) (dict ((goodOf c' σ').comp (incF c c' hle)))
          (muQ1 (D.sp.W j)) (wtZ a n) (rulBC hle (f : Rul Xo c)) := rfl
    have e2 : normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) (σ'.comp (incF c c' hle)) f =
        petAt (U (goodOf c (σ'.comp (incF c c' hle)))) (xiR D) (D.sp.W j) (dict (goodOf c (σ'.comp (incF c c' hle))))
          (muQ1 (D.sp.W j)) (wtZ a n) (f : Rul Xo c) := rfl
    rw [e1, e2, petAt_unfBC hle U (goodOf c' σ') _ _ _ _ _ hsec]
    have key : ∀ τ τ' : c.F →+* ℂ, τ = τ' →
        petAt (U τ) (xiR D) (D.sp.W j) (dict τ) (muQ1 (D.sp.W j)) (wtZ a n) (f : Rul Xo c) =
        petAt (U τ') (xiR D) (D.sp.W j) (dict τ') (muQ1 (D.sp.W j)) (wtZ a n) (f : Rul Xo c) := by
      rintro τ _ rfl; rfl
    exact key _ _ (goodOf_comp hle σ')

end GlobalTheory.LawsFieldChange
