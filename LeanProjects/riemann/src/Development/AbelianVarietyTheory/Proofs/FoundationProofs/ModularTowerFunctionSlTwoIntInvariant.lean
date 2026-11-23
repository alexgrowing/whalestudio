import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Definitions.Foundations.SiegelNeZeroIff
open scoped MatrixGroups
open GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KZ.InvFun

open Filter Topology

theorem mob_ofSL_den_ne_zero (γ : SL(2, ℤ)) {z : ℂ} (hz : z ∈ Hs) :
    (ent (ofSL γ) 1 0 : ℂ) * z + (ent (ofSL γ) 1 1 : ℂ) ≠ 0 := by
  have hz' : 0 < z.im := hz
  have e10 : (ent (ofSL γ) 1 0 : ℂ) = ((γ 1 0 : ℤ) : ℂ) := by simp [ent, ofSL]
  have e11 : (ent (ofSL γ) 1 1 : ℂ) = ((γ 1 1 : ℤ) : ℂ) := by simp [ent, ofSL]
  rw [e10, e11]
  intro h0
  have him := congrArg Complex.im h0
  simp at him
  rcases him with hc | hc
  · have hre := congrArg Complex.re h0
    simp [hc] at hre
    have hdet := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at hdet
    rw [hc, hre] at hdet
    simp at hdet
  · exact absurd hc hz'.ne'

theorem continuousAt_mob_ofSL (γ : SL(2, ℤ)) {z : ℂ} (hz : z ∈ Hs) : ContinuousAt (mob (ofSL γ)) z := by
  unfold mob
  exact ((continuous_const.mul continuous_id).add continuous_const).continuousAt.div
    ((continuous_const.mul continuous_id).add continuous_const).continuousAt (mob_ofSL_den_ne_zero γ hz)

theorem mob_ofSL_mem (γ : SL(2, ℤ)) {z : ℂ} (hz : z ∈ Hs) : mob (ofSL γ) z ∈ Hs := by
  have := SiegelModel.mob_ofSL γ ⟨z, hz⟩
  show 0 < (mob (ofSL γ) z).im
  have e : ((⟨z, hz⟩ : UpperHalfPlane) : ℂ) = z := rfl
  rw [e] at this
  rw [this]
  exact (γ • (⟨z, hz⟩ : UpperHalfPlane)).im_pos

theorem fun_inv {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (h : X.K) (φ : ℂ → ℂ) :
    ContinuousOn φ Hs → X.an h = (φ : Mero) → (∀ γ : SL(2, ℤ), X.sl (ofSL γ) h = h) →
      ∀ γ : SL(2, ℤ), ∀ z ∈ Hs, φ (mob (ofSL γ) z) = φ z := by
  intro hφ han hinv γ z hz
  have e := X.an_sl (ofSL γ) h φ han
  rw [hinv γ, han, Filter.Germ.coe_eq] at e
  have h1 := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 e) z hz
  have h2 : Hs ∈ 𝓝[≠] z := mem_nhdsWithin_of_mem_nhds (SiegelModel.isOpen_Hs.mem_nhds hz)
  have hev : (fun w => φ (mob (ofSL γ) w)) =ᶠ[𝓝[≠] z] φ := by
    filter_upwards [h1, h2] with w hw1 hw2
    rcases hw1 with hw | hw
    · exact hw.symm
    · exact absurd hw2 hw
  have hc1 : ContinuousAt φ z := hφ.continuousAt (SiegelModel.isOpen_Hs.mem_nhds hz)
  have hc2 : ContinuousAt (fun w => φ (mob (ofSL γ) w)) z :=
    ContinuousAt.comp (f := mob (ofSL γ)) (g := φ)
      (hφ.continuousAt (SiegelModel.isOpen_Hs.mem_nhds (mob_ofSL_mem γ hz))) (continuousAt_mob_ofSL γ hz)
  have t1 : Tendsto (fun w => φ (mob (ofSL γ) w)) (𝓝[≠] z) (𝓝 (φ (mob (ofSL γ) z))) :=
    hc2.tendsto.mono_left nhdsWithin_le_nhds
  have t2 : Tendsto (fun w => φ (mob (ofSL γ) w)) (𝓝[≠] z) (𝓝 (φ z)) :=
    (hc1.tendsto.mono_left nhdsWithin_le_nhds).congr' hev.symm
  exact tendsto_nhds_unique t1 t2

example : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (h : X.K) (φ : ℂ → ℂ), ContinuousOn φ Hs → X.an h = (φ : Mero) → (∀ γ : SL(2, ℤ), X.sl (ofSL γ) h = h) → ∀ γ : SL(2, ℤ), ∀ z ∈ Hs, φ (mob (ofSL γ) z) = φ z := @fun_inv

end GlobalTheory.KZ.InvFun
