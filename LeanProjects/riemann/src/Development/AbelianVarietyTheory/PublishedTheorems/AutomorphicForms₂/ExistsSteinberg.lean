import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands.Test

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ}

theorem eps_zero {ε : EpsFamily A} (hε : IsDeligneEps ε) (ψ : AddChar (w.adicCompletion E) Circle)
    (hc : Continuous ψ) (h1 : ψ ≠ 1) : ε E w h ψ (WD.lpZero h) = 1 := by
  have := hε.add E w h ψ hc h1 (WD.lpZero h) (WD.lpZero h)
  rw [WD.lpSum_zero] at this
  exact left_eq_mul.1 this

theorem unr_lpOfChar_iff (ha : IsLocalArtin h a) {χ : (w.adicCompletion E)ˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    (WD.lpOfChar h (χ.comp a) (ha.smooth hχ)).unr ↔ IsUnram χ := by
  rw [WD.lpOfChar, WD.unr_mk]
  constructor
  · rintro ⟨-, H⟩ x hx
    obtain ⟨σ, rfl⟩ := ha.surj x
    have h0 : deg σ = 0 := by
      have := ha.ord_eq σ
      rw [ord_eq_zero_iff.2 hx] at this
      omega
    have h2 := congrFun (LinearMap.congr_fun (H ⟨_, deg_eq_zero_iff.mp h0⟩) fun _ => 1) 0
    have h3 : χ (a (ineIncl h ⟨_, deg_eq_zero_iff.mp h0⟩)) = 1 := by simpa using h2
    exact h3
  · intro H
    refine ⟨rfl, fun σ => LinearMap.ext fun v => funext fun i => ?_⟩
    have : χ (a (ineIncl h σ)) = 1 := H _ (ord_eq_zero_iff.1 (by rw [ha.ord_eq]; simp))
    simp [this]

theorem lpOfChar_unrChar (ha : IsLocalArtin h a) (c : ℂˣ) (hc) :
    WD.lpOfChar h ((SmGL.unrChar (w.adicCompletion E) c).comp a) hc = WD.mk (WDRep.diag h fun _ : Fin 1 => c⁻¹) := by
  simp only [WD.lpOfChar, WDRep.diag, ha.unrChar_comp]

theorem lpChar_lpSp_one (x : WD h) : x.lpChar (WD.lpSp h 1) = x := by
  have h1 : WD.lpSp h 1 = WD.lpOfChar h (WeilDeligne.unrChar h (qPow w 0)) (isSmooth_unrChar h _) := by
    refine WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => ?_⟩
    · funext i
      simp [WDRep.spEig]
    · funext i
      simp [shiftEnd_apply]
  rw [h1, lpChar_lpOfChar]
  exact WD.lpTw_zero x

theorem not_isIrrWD_zero : ¬ IsIrrWD (WD.lpZero h) := by
  rintro ⟨n, b, hb, hi⟩
  have hn : n = 0 := by simpa [WD.lpZero] using congrArg WD.lpDim hb
  subst hn
  have : Nontrivial (Subrepresentation b.ρ) := inferInstance
  obtain ⟨S, T, hST⟩ := this
  exact hST (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

theorem exists_steinberg {ha : IsLocalArtin h a} {ε : EpsFamily A} {rc : IrrGL (w.adicCompletion E) → WD h}
    (H : Laws a ha ε rc) : ∃ x : IrrGL (w.adicCompletion E), x.1 = 2 ∧ rc x = WD.lpSp h 2 ∧ ¬ IsSpherical x.rep := by
  obtain ⟨x, hx⟩ := H.bij.2 (WD.lpSp h 2)
  refine ⟨x, by rw [← H.dim, hx]; simp, hx, fun hs => (sp_two_spec h).2.2.2 (hx ▸ (H.sph x).1 hs)⟩

end GlobalTheory.LocLanglands.Test
