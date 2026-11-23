import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrbitThickSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos

open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CuspFrom
open scoped ComplexConjugate

namespace GlobalTheory.CuspFrom.FlowMaj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

lemma majForm_conj {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (u w : Fin r → ℂ) :
    X.Hf x τ w u = conj (X.Hf x τ u w) := by
  rw [X.Hf_eq_jp, X.Hf_eq_jp, hermC_conj τ.1 X.Gm_herm, X.hermC_jp_left hx]

lemma majForm_sub_smul (x : Frame X.Ψ r) (τ : X.Ψ) (a : ℂ) (v e w : Fin r → ℂ) :
    X.Hf x τ (v - a • e) w = X.Hf x τ v w - a * X.Hf x τ e w := by
  simp only [X.Hf_eq_jp, X.jp_sub, X.jp_smul, hermC_sub_left, hermC_smul_left]

lemma maj_zero {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) : X.maj x τ 0 = 0 := by
  have h := X.Hf_self hx τ 0
  rw [X.Hf_eq_jp, hermC_zero_right] at h
  exact_mod_cast h.symm

lemma maj_nonneg {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) : 0 ≤ X.maj x τ v := by
  by_cases hv : v = 0
  · rw [hv, maj_zero X hx]
  · exact (X.maj_pos hx τ hv).le

lemma maj_split {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (a : ℂ) (e u : Fin r → ℂ)
    (h : X.Hf x τ u e = 0) : X.maj x τ (u + a • e) = X.maj x τ u + ‖a‖ ^ 2 * X.maj x τ e := by
  have h' : X.Hf x τ e u = 0 := by rw [majForm_conj X hx, h, map_zero]
  have h1 := X.Hf_self hx τ (u + a • e)
  have h2 := X.Hf_self hx τ u
  have h3 := X.Hf_self hx τ e
  simp only [X.Hf_eq_jp] at h h' h1 h2 h3
  simp only [X.jp_add, X.jp_smul, hermC_add_left, hermC_add_right, hermC_smul_left, hermC_smul_right,
    h, h', h2, h3] at h1
  have h4 : a * conj a = ((‖a‖ : ℝ) : ℂ) ^ 2 := Complex.mul_conj' a
  have h5 : ((X.maj x τ (u + a • e) : ℝ) : ℂ) = ((X.maj x τ u + ‖a‖ ^ 2 * X.maj x τ e : ℝ) : ℂ) := by
    rw [← h1]
    push_cast
    linear_combination (X.maj x τ e : ℂ) * h4
  exact_mod_cast h5

lemma majForm_perp {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) {e : Fin r → ℂ} (he : e ≠ 0) :
    X.Hf x τ (v - (X.Hf x τ v e / X.Hf x τ e e) • e) e = 0 := by
  have h0 : X.Hf x τ e e ≠ 0 := by
    rw [X.Hf_self hx]
    exact_mod_cast (X.maj_pos hx τ he).ne'
  rw [majForm_sub_smul, div_mul_cancel₀ _ h0, sub_self]

lemma majForm_cs {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v w : Fin r → ℂ) :
    ‖X.Hf x τ v w‖ ^ 2 ≤ X.maj x τ v * X.maj x τ w := by
  by_cases hw : w = 0
  · rw [hw, maj_zero X hx, X.Hf_eq_jp, hermC_zero_right]
    simp
  have hp := X.maj_pos hx τ hw
  have h1 := maj_split X hx τ (X.Hf x τ v w / X.Hf x τ w w) w _ (majForm_perp X hx τ v hw)
  rw [sub_add_cancel] at h1
  have h2 := maj_nonneg X hx τ (v - (X.Hf x τ v w / X.Hf x τ w w) • w)
  have h3 : ‖X.Hf x τ v w / X.Hf x τ w w‖ ^ 2 * X.maj x τ w * X.maj x τ w = ‖X.Hf x τ v w‖ ^ 2 := by
    rw [norm_div, X.Hf_self hx τ w, Complex.norm_real, Real.norm_of_nonneg hp.le]
    field_simp
  rw [← h3]
  exact mul_le_mul_of_nonneg_right (by linarith) hp.le

lemma maj_jp {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) :
    X.maj x τ (X.jp x τ v) = X.maj x τ v := by
  have h1 := X.Hf_self hx τ (X.jp x τ v)
  have h2 := X.Hf_self hx τ v
  rw [X.Hf_eq_jp, X.hermC_jp_jp hx, ← X.Hf_eq_jp, h2] at h1
  exact_mod_cast h1.symm

lemma herm_cs {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v w : Fin r → ℂ) :
    ‖hermC τ.1 X.Gm v w‖ ^ 2 ≤ X.maj x τ v * X.maj x τ w := by
  have h := majForm_cs X hx τ (X.jp x τ v) w
  rwa [X.Hf_eq_jp, X.jp_jp hx, maj_jp X hx] at h

lemma maj_flow {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (s : X.Ψ → ℂ)
    (hxs : X.flow ξ s x ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) (hv : hermC τ.1 X.Gm v (Data.emb τ.1 ξ) = 0) :
    X.maj (X.flow ξ s x) τ v = X.maj x τ v +
      ‖X.Hf x τ v (Data.emb τ.1 ξ) / X.Hf x τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)‖ ^ 2 *
        (X.maj (X.flow ξ s x) τ (Data.emb τ.1 ξ) - X.maj x τ (Data.emb τ.1 ξ)) := by
  have hiso : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0 := by
    rw [← emb_herm, hξ.2.1, map_zero]
  have he : Data.emb τ.1 ξ ≠ 0 := emb_ne_zero τ.1 hξ.2.2
  have hH := majForm_perp X hx τ v he
  set a := X.Hf x τ v (Data.emb τ.1 ξ) / X.Hf x τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) with ha
  set u := v - a • Data.emb τ.1 ξ with hu
  have hu0 : hermC τ.1 X.Gm u (Data.emb τ.1 ξ) = 0 := by
    rw [hu, hermC_sub_left, hermC_smul_left, hv, hiso, mul_zero, sub_zero]
  have hp : hermC τ.1 X.Gm (X.ppos x τ u) (Data.emb τ.1 ξ) = 0 := by
    have h := hH
    rw [X.Hf_eq_two_ppos, hu0, sub_zero] at h
    exact (mul_eq_zero.mp h).resolve_left two_ne_zero
  have hpp := Data.ppos_flow X ξ τ hx s hxs u hu0 hp
  have hHy : ∀ w, X.Hf (X.flow ξ s x) τ u w = X.Hf x τ u w := fun w => by
    rw [X.Hf_eq_two_ppos, X.Hf_eq_two_ppos, hpp]
  have hm : X.maj (X.flow ξ s x) τ u = X.maj x τ u := by
    have h := hHy u
    rw [X.Hf_self hxs, X.Hf_self hx] at h
    exact_mod_cast h
  have h1 := maj_split X hx τ a _ u hH
  have h2 := maj_split X hxs τ a _ u ((hHy _).trans hH)
  rw [hu, sub_add_cancel, ← hu] at h1 h2
  rw [h1, h2, hm]
  ring

end GlobalTheory.CuspFrom.FlowMaj

namespace GlobalTheory.CuspFrom

theorem flowMajSt_holds : FlowMajSt := fun _ _ _ _ _ X =>
  ⟨fun _ hξ _ hx s hxs τ v hv => FlowMaj.maj_flow X hξ hx s hxs τ v hv,
    fun _ hx τ v w => ⟨FlowMaj.herm_cs X hx τ v w, FlowMaj.majForm_cs X hx τ v w⟩⟩

end GlobalTheory.CuspFrom
