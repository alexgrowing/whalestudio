import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.UnitFrame

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open NumberField Matrix in
open scoped nonZeroDivisors ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
omit [IsCMField E] in

theorem _root_.GlobalTheory.UnitFrame.trace_eq_sum_re (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (z : E) :
    ((Algebra.trace ℚ E z : ℚ) : ℝ) = ∑ τ : Ψ, 2 * (τ.1 z).re := by
  classical
  apply Complex.ofReal_injective
  have htr : ((Algebra.trace ℚ E z : ℚ) : ℂ) = ∑ τ : E →+* ℂ, τ z := by
    have h := trace_eq_sum_embeddings (K := ℚ) (L := E) (E := ℂ) (x := z)
    rw [eq_ratCast] at h
    rw [h]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) (fun τ => τ z) (fun σ => σ z)
      (fun _ => rfl)).symm
  rw [Complex.ofReal_ratCast, htr]
  push_cast
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ Ψ)]
  have hsplit : ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ ∉ Ψ), τ z
      = ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ ∈ Ψ), conj (τ z) := by
    refine Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
    · intro τ hτ
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
      by_contra h
      exact hτ ((hΨ _).2 (by simpa using h))
    · intro τ hτ
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
      exact (hΨ τ).1 hτ
    · intro τ _; simp
    · intro τ _; simp
    · intro τ _; simp [ComplexEmbedding.conjugate_coe_eq]
  rw [hsplit, ← Finset.sum_add_distrib]
  rw [Finset.sum_subtype (Finset.univ.filter (· ∈ Ψ)) (p := (· ∈ Ψ)) (by simp)]
  refine Fintype.sum_congr _ _ (fun τ => ?_)
  rw [Complex.add_conj]
  push_cast; ring

open NumberField Matrix in
open scoped nonZeroDivisors ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
omit [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.UnitFrame.hermC_eq {r : ℕ} (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (u v : Fin r → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G u v = u ⬝ᵥ (G.map τ) *ᵥ (star v) := by
  simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

open NumberField Matrix in
open scoped nonZeroDivisors ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
omit [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.UnitFrame.gram_eq {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (x : Matrix (Fin r) (Fin r) ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G x = xᵀ * (G.map τ * x.map conj) := by
  ext a b
  simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.gram, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC, _root_.ReciprocityTheory.ChartRestriction.G.FD.col, mul_apply, Finset.mul_sum, mul_assoc]

open NumberField Matrix in
open scoped nonZeroDivisors ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
omit [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.UnitFrame.hermC_mulVec {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (x : Matrix (Fin r) (Fin r) ℂ) (c c' : Fin r → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G (x *ᵥ c) (x *ᵥ c') = c ⬝ᵥ (_root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G x) *ᵥ (star c') := by
  have hstar : star (x *ᵥ c') = x.map conj *ᵥ star c' := by
    funext i
    simp [mulVec, dotProduct, star_sum, mul_comm]
  rw [_root_.GlobalTheory.UnitFrame.hermC_eq, _root_.GlobalTheory.UnitFrame.gram_eq,
    ← mulVec_mulVec, ← mulVec_mulVec, hstar, dotProduct_mulVec c xᵀ, vecMul_transpose]

open NumberField Matrix in
open scoped nonZeroDivisors ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
omit [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.UnitFrame.im_sum_periods {r : ℕ} (q : ℕ) (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E)
    (x : Matrix (Fin r) (Fin r) ℂ)
    (hx : _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G x = Matrix.diagonal fun a : Fin r => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ))
    (u v : Fin r → ℂ) :
    (∑ a : Fin r, (if (a : ℕ) < q then _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G (_root_.ReciprocityTheory.ChartRestriction.G.FD.col x a) u else (x⁻¹ *ᵥ u) a) *
      conj (if (a : ℕ) < q then _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G (_root_.ReciprocityTheory.ChartRestriction.G.FD.col x a) v else (x⁻¹ *ᵥ v) a)).im =
      -(_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G u v).im := by
  have hsgn : ∀ a : ℕ, _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn q a = 1 ∨ _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn q a = -1 := by
    intro a; unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn; split_ifs <;> simp
  have hdet : x.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hx
    rw [_root_.GlobalTheory.UnitFrame.gram_eq, det_mul, det_transpose, h0, zero_mul,
      det_diagonal] at h1
    refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) h1.symm
    rcases hsgn a with h | h <;> simp [h]
  have hx1 : x * x⁻¹ = 1 := mul_nonsing_inv x (isUnit_iff_ne_zero.2 hdet)
  have hback : ∀ y : Fin r → ℂ, x *ᵥ (x⁻¹ *ᵥ y) = y := by
    intro y; rw [mulVec_mulVec, hx1, one_mulVec]
  have hcol : ∀ a, _root_.ReciprocityTheory.ChartRestriction.G.FD.col x a = x *ᵥ Pi.single a 1 := by
    intro a; funext k; simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.col, mulVec_single_one]
  have hkey : ∀ a (y : Fin r → ℂ), _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G (_root_.ReciprocityTheory.ChartRestriction.G.FD.col x a) y
      = ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ) * conj ((x⁻¹ *ᵥ y) a) := by
    intro a y
    conv_lhs => rw [hcol, ← hback y]
    rw [_root_.GlobalTheory.UnitFrame.hermC_mulVec, hx]
    simp [mulVec_diagonal]
  have hfull : _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G u v
      = ∑ a, (x⁻¹ *ᵥ u) a * (((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ) * conj ((x⁻¹ *ᵥ v) a)) := by
    conv_lhs => rw [← hback u, ← hback v]
    rw [_root_.GlobalTheory.UnitFrame.hermC_mulVec, hx]
    simp [dotProduct, mulVec_diagonal]
  rw [hfull, Complex.im_sum, Complex.im_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : (a : ℕ) < q
  · simp only [ha, if_true, hkey]
    have : _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn q a = 1 := by simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, ha]
    simp [this, Complex.mul_im]
    ring
  · simp only [ha, if_false]
    have : _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn q a = -1 := by simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, ha]
    simp [this, Complex.mul_im]

open NumberField Matrix in
open scoped nonZeroDivisors ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma mem_iff_conjugate_not_mem (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) (τ : E →+* ℂ) :
    τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hrt : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (fun y : 𝓞 E => (y : E)) H.rt_sq
    simpa using this
  have hw : (τ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
    rw [← map_pow, hrt]; simp
  have h0 := H.sqrt_neg_disc_sq
  rw [hΨ, hΨ, ComplexEmbedding.conjugate_coe_eq]
  set w := τ (H.rt : E)
  set m := H.rt0
  have reZero : ∀ z : ℂ, z ^ 2 = -(H.d : ℂ) → z.re = 0 ∧ z.im ^ 2 = H.d := by
    intro z hz
    have e1 := congrArg Complex.re hz
    have e2 := congrArg Complex.im hz
    simp [sq, Complex.mul_re, Complex.mul_im] at e1 e2
    have hre : z.re = 0 := by
      rcases mul_eq_zero.1 (show z.re * z.im = 0 by linarith) with h | h
      · exact h
      · exfalso; rw [h] at e1; nlinarith [sq_nonneg z.re]
    refine ⟨hre, ?_⟩
    rw [hre] at e1; nlinarith
  obtain ⟨hwr, hwi⟩ := reZero w hw
  obtain ⟨hmr, hmi⟩ := reZero m h0
  have hm0 : m.im ≠ 0 := by
    intro h; rw [h] at hmi; linarith
  constructor
  · intro h hc
    rw [h] at hc
    have := congrArg Complex.im hc
    simp at this
    exact hm0 (by linarith)
  · intro hn
    apply Complex.ext
    · rw [hwr, hmr]
    · have : (w.im - m.im) * (w.im + m.im) = 0 := by nlinarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · exfalso; apply hn
        apply Complex.ext
        · simp [hwr, hmr]
        · simp; linarith

open NumberField Matrix in
open scoped nonZeroDivisors ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.UnitFrame.im_hermForm_eq :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (hΨ : ∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) (g : ℕ) (idx : Fin g ≃ Ψ × Fin r) (ty : Fin g → (E →+* ℂ)) (hty : ∀ k, ty k = if ((idx k).2 : ℕ) < D.q then ComplexEmbedding.conjugate (idx k).1.1 else (idx k).1.1), _root_.ReciprocityTheory.ChartRestriction.G.FD.cc ξ = -ξ → (∀ τ ∈ Ψ, 0 < (τ ξ).im) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm (φ x) (φ y))) → ∀ (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) (P : D.La →+ (Fin g → ℂ)), (∀ v k, P v k = if ((idx k).2 : ℕ) < D.q then _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC (idx k).1.1 Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (idx k).1) (idx k).2) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (idx k).1.1 (φ v)) else ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (idx k).1)⁻¹ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (idx k).1.1 (φ v)) (idx k).2) → (∀ τ : Ψ, _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) = Matrix.diagonal fun a : Fin r => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn D.q (a : ℕ) : ℝ) : ℂ)) → ∀ v w, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Matrix.diagonal fun k => ((2 * ‖(idx k).1.1 ξ‖ : ℝ) : ℂ)) (P v) (P w)).im = D.EF v w := by
  intro E _ _ _ H D r ξ Gm φ Ψ hΨ g idx ty hty hξ hpos hdata x P hP hgram v w
  have hEF := hdata.2.2.2.2
  have hcm := mem_iff_conjugate_not_mem H Ψ hΨ
  have hherm : ∀ (τ : E →+* ℂ) (a b : Fin r → E),
      τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm a b) = _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ a) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ b) := by
    intro τ a b
    simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.herm, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC, _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc, map_sum, map_mul,
      IsCMField.complexEmbedding_complexConj]
  have hre : ∀ τ : Ψ, (τ.1 (ξ * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm (φ v) (φ w))).re
      = -‖τ.1 ξ‖ * (_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (φ v)) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (φ w))).im := by
    intro τ
    have hc : conj (τ.1 ξ) = -τ.1 ξ := by
      rw [← IsCMField.complexEmbedding_complexConj, ← map_neg]
      congr 1
    have hr : (τ.1 ξ).re = 0 := by
      have := congrArg Complex.re hc
      simp at this; linarith
    have hn : ‖τ.1 ξ‖ = (τ.1 ξ).im := by
      have hz : τ.1 ξ = ((τ.1 ξ).im : ℂ) * Complex.I := by
        apply Complex.ext <;> simp [hr]
      rw [hz, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos]
      · simp
      · simpa using hpos τ.1 τ.2
    rw [map_mul, hherm, Complex.mul_re, hr, hn]
    ring
  have hL : (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Matrix.diagonal fun k => ((2 * ‖(idx k).1.1 ξ‖ : ℝ) : ℂ)) (P v) (P w)).im
      = ∑ k, 2 * ‖(idx k).1.1 ξ‖ * (P v k * conj (P w k)).im := by
    simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, dotProduct, mulVec_diagonal, Complex.im_sum, Pi.star_apply,
      Complex.star_def]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_left_comm, Complex.im_ofReal_mul]
  rw [hL, ← Rat.cast_intCast, hEF, _root_.GlobalTheory.UnitFrame.trace_eq_sum_re Ψ hcm, ← idx.symm.sum_comp,
    Fintype.sum_prod_type]
  refine Fintype.sum_congr _ _ fun τ => ?_
  simp only [Equiv.apply_symm_apply]
  rw [← Finset.mul_sum, ← Complex.im_sum]
  have hPv : ∀ u, ∀ a : Fin r, P u (idx.symm (τ, a)) = if (a : ℕ) < D.q then
      _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) a) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (φ u))
      else ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (φ u)) a := by
    intro u a; rw [hP]; simp
  simp only [hPv]
  rw [_root_.GlobalTheory.UnitFrame.im_sum_periods D.q τ.1 Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (hgram τ), hre]
  ring

end GlobalTheory.UnitFrame
