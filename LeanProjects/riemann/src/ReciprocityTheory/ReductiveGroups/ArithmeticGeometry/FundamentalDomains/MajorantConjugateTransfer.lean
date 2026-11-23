import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace MajorantConjugateTransfer

variable {r : ℕ} (X : Data E r)

theorem maj_transfer {x y : Frame X.Ψ r} (hx : x ∈ X.dom) (hy : y ∈ X.dom) (τ : X.Ψ)
    (g g' : Matrix (Fin r) (Fin r) ℂ) (hgg' : ∀ w, Matrix.mulVec g (Matrix.mulVec g' w) = w)
    (hiso : ∀ u v, hermC τ.1 X.Gm (Matrix.mulVec g u) (Matrix.mulVec g v) = hermC τ.1 X.Gm u v)
    (H1 : ∀ c, ∃ K : Fin X.p0 → ℂ, Matrix.mulVec g (X.colP x τ c) = ∑ a, K a • X.colP y τ a)
    (H2 : ∀ a, ∃ L : Fin X.p0 → ℂ, X.colP y τ a = ∑ c, L c • Matrix.mulVec g (X.colP x τ c))
    (w : Fin r → ℂ) : X.maj y τ w = X.maj x τ (Matrix.mulVec g' w) := by
  have pp : ∀ (x' : Frame X.Ψ r) (v : Fin r → ℂ),
      X.posPart x' τ v = (hermC τ.1 X.Gm (X.ppos x' τ v) v).re := by
    intro x' v
    rw [X.hermC_ppos_self]
    rfl
  set u := Matrix.mulVec g' w with hu
  set p := Matrix.mulVec g (X.ppos x τ u) with hp
  set z := Matrix.mulVec g u with hz
  have hA : ∀ d : Fin r → ℂ, (∀ c', hermC τ.1 X.Gm d (X.colP y τ c') = 0) →
      ∀ c, hermC τ.1 X.Gm d (Matrix.mulVec g (X.colP x τ c)) = 0 := by
    intro d hd c
    obtain ⟨K, hK⟩ := H1 c
    rw [hK, hermC_sum_right]
    exact Finset.sum_eq_zero fun a _ => by rw [hermC_smul_right, hd, mul_zero]
  have hB : ∀ b, hermC τ.1 X.Gm z (X.colP y τ b) = hermC τ.1 X.Gm p (X.colP y τ b) := by
    intro b
    rw [← sub_eq_zero, ← hermC_sub_left]
    obtain ⟨L, hL⟩ := H2 b
    rw [hL, hermC_sum_right]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [hermC_smul_right, hz, hp, ← Matrix.mulVec_sub, hiso, hermC_sub_left,
      X.hermC_ppos_colP hx, sub_self, mul_zero]
  have h1 : X.ppos y τ z = X.ppos y τ p := by
    rw [X.ppos_eq, X.ppos_eq]
    simp only [hB]
  have h2 : ∀ c', hermC τ.1 X.Gm (X.ppos y τ p - p) (X.colP y τ c') = 0 := by
    intro c'
    rw [hermC_sub_left, X.hermC_ppos_colP hy, sub_self]
  have h3 : ∀ d, (∀ c', hermC τ.1 X.Gm d (X.colP y τ c') = 0) → hermC τ.1 X.Gm d p = 0 := by
    intro d hd
    rw [hp, X.ppos_eq x τ u, Matrix.mulVec_sum, hermC_sum_right]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [Matrix.mulVec_smul, hermC_smul_right, hA d hd a, mul_zero]
  have key : hermC τ.1 X.Gm (X.ppos y τ z) z = hermC τ.1 X.Gm (X.ppos x τ u) u := by
    have e := h3 _ h2
    rw [hermC_sub_left, sub_eq_zero] at e
    rw [X.hermC_ppos_left hy τ z z, h1, ← X.hermC_ppos_left hy τ p p, e, hp, hiso,
      ← X.hermC_ppos_left hx τ u u]
  have hwz : w = z := (hgg' w).symm
  rw [hwz]
  simp only [Data.maj]
  rw [pp, pp, key, hz, hiso]

theorem maj_zero (x : Frame X.Ψ r) (τ : X.Ψ) : X.maj x τ 0 = 0 := by
  simp [Data.maj, Data.posPart, hermC_zero_left]

theorem maj_nonneg {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) :
    0 ≤ X.maj x τ v := by
  by_cases hv : v = 0
  · rw [hv, maj_zero X x τ]
  · exact (X.maj_pos hx τ hv).le

theorem Hf_sub_left (x : Frame X.Ψ r) (τ : X.Ψ) (u u' w : Fin r → ℂ) :
    X.Hf x τ (u - u') w = X.Hf x τ u w - X.Hf x τ u' w := by
  rw [X.Hf_eq_two_ppos, X.Hf_eq_two_ppos, X.Hf_eq_two_ppos, X.ppos_sub, hermC_sub_left,
    hermC_sub_left]
  ring

theorem Hf_smul_left (x : Frame X.Ψ r) (τ : X.Ψ) (k : ℂ) (u w : Fin r → ℂ) :
    X.Hf x τ (k • u) w = k * X.Hf x τ u w := by
  rw [X.Hf_eq_two_ppos, X.Hf_eq_two_ppos, X.ppos_smul_eq, hermC_smul_left, hermC_smul_left]
  ring

theorem Hf_sub_right (x : Frame X.Ψ r) (τ : X.Ψ) (u w w' : Fin r → ℂ) :
    X.Hf x τ u (w - w') = X.Hf x τ u w - X.Hf x τ u w' := by
  rw [X.Hf_eq_two_ppos, X.Hf_eq_two_ppos, X.Hf_eq_two_ppos, hermC_sub_right, hermC_sub_right]
  ring

theorem Hf_smul_right (x : Frame X.Ψ r) (τ : X.Ψ) (k : ℂ) (u w : Fin r → ℂ) :
    X.Hf x τ u (k • w) = conj k * X.Hf x τ u w := by
  rw [X.Hf_eq_two_ppos, X.Hf_eq_two_ppos, hermC_smul_right, hermC_smul_right]
  ring

theorem Hf_conj {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (u w : Fin r → ℂ) :
    conj (X.Hf x τ u w) = X.Hf x τ w u := by
  rw [X.Hf_eq_two_ppos, X.Hf_eq_two_ppos, map_sub, map_mul, map_ofNat, hermC_conj _ X.Gm_herm,
    hermC_conj _ X.Gm_herm, X.ppos_selfadj hx τ w u]

theorem cs {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (u v : Fin r → ℂ) :
    ‖X.Hf x τ u v‖ ^ 2 ≤ X.maj x τ u * X.maj x τ v := by
  by_cases hv : v = 0
  · have h0 : X.Hf x τ u 0 = 0 := by
      have := Hf_sub_right X x τ u 0 0
      simpa using this
    rw [hv, h0, maj_zero X x τ]
    simp
  have hm : 0 < X.maj x τ v := X.maj_pos hx τ hv
  have hmu := maj_nonneg X hx τ u

  set H := X.Hf x τ u v with hH
  have hw := X.Hf_self hx τ ((X.maj x τ v : ℂ) • u - H • v)
  have hn := maj_nonneg X hx τ ((X.maj x τ v : ℂ) • u - H • v)
  simp only [Hf_sub_left, Hf_sub_right, Hf_smul_left, Hf_smul_right] at hw
  rw [X.Hf_self hx τ u, X.Hf_self hx τ v, ← Hf_conj X hx τ u v, ← hH, Complex.conj_ofReal] at hw
  have hHH : H * conj H = (Complex.normSq H : ℂ) := Complex.mul_conj H
  have e : ((X.maj x τ ((X.maj x τ v : ℂ) • u - H • v) : ℝ) : ℂ) =
      ((X.maj x τ v * (X.maj x τ v * X.maj x τ u - Complex.normSq H) : ℝ) : ℂ) := by
    rw [← hw]
    push_cast
    linear_combination (-(X.maj x τ v : ℂ)) * hHH
  have e' := Complex.ofReal_injective e
  rw [e'] at hn
  have hle : Complex.normSq H ≤ X.maj x τ v * X.maj x τ u := by
    by_contra hc
    push_neg at hc
    have : X.maj x τ v * (X.maj x τ v * X.maj x τ u - Complex.normSq H) < 0 :=
      mul_neg_of_pos_of_neg hm (by linarith)
    linarith
  rw [Complex.sq_norm]
  linarith [mul_comm (X.maj x τ u) (X.maj x τ v)]

end MajorantConjugateTransfer

end ReciprocityTheory.ChartRestriction.G.FD
