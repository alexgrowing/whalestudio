import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.LocalParametersCuspidal.DZC

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem tame_lpOfChar_iff (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ) :
    IsTameWD (WD.lpOfChar h ξ hξ) ↔ ∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → ξ σ = 1 := by
  constructor
  · rintro ⟨n, a, ha, H⟩ σ hσ
    unfold WD.lpOfChar at ha
    obtain ⟨e, he, -⟩ := WD.mk_eq_mk.mp ha
    have h1 : ∀ u : Fin 1 → ℂ,
        (WDRep.ofChars h (ι := Fin 1) (fun _ => ξ) fun _ => hξ).ρ σ u = u := by
      intro u
      obtain ⟨v, rfl⟩ := e.surjective u
      rw [← he, H σ hσ]
      rfl
    have h2 := congrFun (h1 fun _ => 1) 0
    rw [WDRep.ofChars_ρ, diagEnd_apply, mul_one] at h2
    exact Units.ext h2
  · intro H
    refine ⟨1, WDRep.ofChars h (ι := Fin 1) (fun _ => ξ) (fun _ => hξ), rfl, fun σ hσ => ?_⟩
    refine LinearMap.ext fun v => funext fun i => ?_
    rw [WDRep.ofChars_ρ, diagEnd_apply, H σ hσ]
    simp

end PositivityTheory.LocalParametersCuspidal.DZC

end
