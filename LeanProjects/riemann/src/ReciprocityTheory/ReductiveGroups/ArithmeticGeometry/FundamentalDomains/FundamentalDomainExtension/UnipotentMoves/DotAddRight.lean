import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.UnipotentMoves.BotMulVecExt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SignTypeCancelIdentity

namespace UnipMove.MajH

open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds UnipMove.GraphH NumberField Complex
open scoped ComplexConjugate Matrix

noncomputable section

def dot {n : ℕ} (u w : Fin n → ℂ) : ℂ := ∑ i, u i * conj (w i)

lemma dot_add_left {n : ℕ} (u u' w : Fin n → ℂ) : dot (u + u') w = dot u w + dot u' w := by
  simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma dot_add_right {n : ℕ} (u w w' : Fin n → ℂ) : dot u (w + w') = dot u w + dot u w' := by
  simp only [dot, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

lemma conj_dot {n : ℕ} (u w : Fin n → ℂ) : conj (dot u w) = dot w u := by
  simp only [dot, map_sum, map_mul, Complex.conj_conj]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

lemma re_dot_comm {n : ℕ} (u w : Fin n → ℂ) : (dot u w).re = (dot w u).re := by
  rw [← conj_dot, Complex.conj_re]

lemma re_dot_self {n : ℕ} (u : Fin n → ℂ) : (dot u u).re = nsq u := by
  unfold dot nsq
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

lemma nsq_add {n : ℕ} (u w : Fin n → ℂ) : nsq (u + w) = nsq u + nsq w + 2 * (dot u w).re := by
  rw [← re_dot_self, ← re_dot_self u, ← re_dot_self w, dot_add_left, dot_add_right,
    dot_add_right]
  simp only [Complex.add_re]
  rw [re_dot_comm w u]
  ring

lemma dot_adj {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (a : Fin n → ℂ) (b : Fin m → ℂ) :
    dot (A *ᵥ a) b = dot a (Aᴴ *ᵥ b) := by
  simp only [dot, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [RCLike.star_def, Complex.conj_conj]
  ring

lemma norm_dot_le {n : ℕ} (u w : Fin n → ℂ) : ‖dot u w‖ ≤ en u * en w := by
  have h : dot u w = inner ℂ (WithLp.toLp 2 w : EuclideanSpace ℂ (Fin n)) (WithLp.toLp 2 u) := by
    simp only [dot, PiLp.inner_apply, RCLike.inner_apply, PiLp.toLp_apply]
  rw [h, en, en, mul_comm]
  exact norm_inner_le_norm _ _

lemma key_ineq {A Bn u w D ρ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ Bn) (hu0 : 0 ≤ u) (hw0 : 0 ≤ w)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hu : u ≤ ρ * A) (hw : w ≤ ρ * Bn) (h1 : |D| ≤ u * Bn)
    (h2 : |D| ≤ A * w) :
    (1 - ρ) * (A ^ 2 + w ^ 2 + 2 * D + (u ^ 2 + Bn ^ 2 + 2 * D)) ≤
        (1 + ρ) * (A ^ 2 - u ^ 2 + Bn ^ 2 - w ^ 2) ∧
      (1 - ρ) * (A ^ 2 - u ^ 2 + Bn ^ 2 - w ^ 2) ≤
        (1 + ρ) * (A ^ 2 + w ^ 2 + 2 * D + (u ^ 2 + Bn ^ 2 + 2 * D)) := by
  have hD1 : |D| ≤ ρ * A * Bn := h1.trans (by nlinarith)
  have hD2 : |D| ≤ ρ * A * Bn := h2.trans (by nlinarith)
  have hAB : 2 * (A * Bn) ≤ A ^ 2 + Bn ^ 2 := by nlinarith [sq_nonneg (A - Bn)]
  have hu2 : u ^ 2 ≤ ρ ^ 2 * A ^ 2 := by nlinarith
  have hw2 : w ^ 2 ≤ ρ ^ 2 * Bn ^ 2 := by nlinarith
  have hDa := abs_le.1 hD1
  constructor
  · nlinarith [mul_nonneg hρ0.le hA, mul_nonneg (sub_nonneg.2 hρ1.le) hρ0.le]
  · have hsum : 2 * ρ * (A * Bn) + 2 * (u * w) ≤ ρ * (A ^ 2 + Bn ^ 2) + (u ^ 2 + w ^ 2) := by
      nlinarith [sq_nonneg (A - Bn), sq_nonneg (u - w)]
    have hkey : (1 + ρ) * (-D) ≤ ρ * (A * Bn) + u * w := by
      rcases le_or_gt (-D) 0 with hd | hd
      · nlinarith [mul_nonneg hA hB, mul_nonneg hu0 hw0]
      · have hd1 : -D ≤ u * Bn := (neg_le_abs D).trans h1
        have hd2 : -D ≤ A * w := (neg_le_abs D).trans h2
        have hdAB : -D ≤ ρ * (A * Bn) := by nlinarith [mul_le_mul_of_nonneg_right hu hB]
        have hAB0 : 0 < A * Bn := pos_of_mul_pos_right (by linarith : 0 < ρ * (A * Bn)) hρ0.le
        have hsq : (-D) * (-D) ≤ (u * Bn) * (A * w) := mul_le_mul hd1 hd2 hd.le (mul_nonneg hu0 hB)
        have hq : 0 ≤ (-D - ρ * (A * Bn)) * (-D - A * Bn) :=
          mul_nonneg_of_nonpos_of_nonpos (by linarith) (by nlinarith)
        have hmain : (A * Bn) * ((1 + ρ) * (-D)) ≤ (A * Bn) * (ρ * (A * Bn) + u * w) := by
          nlinarith
        exact le_of_mul_le_mul_left hmain hAB0
    nlinarith

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

lemma sum_splitC (f : Fin r → ℂ) :
    ∑ j, f j = ∑ a : Fin X.p0, f (Fin.castLE X.p0_le a) + ∑ m : Fin (r - X.p0), f (nI X m) := by
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℂ, ∀ i, g i = if h : i < r then f ⟨i, h⟩ else 0 := ⟨_, fun _ => rfl⟩
  have hr : X.p0 + (r - X.p0) = r := Nat.add_sub_cancel' X.p0_le
  have e1 : ∑ j, f j = ∑ i ∈ Finset.range r, g i := by
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hg, dif_pos j.isLt]
  have e2 : ∑ a : Fin X.p0, f (Fin.castLE X.p0_le a) = ∑ i ∈ Finset.range X.p0, g i := by
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hg, dif_pos (lt_of_lt_of_le a.isLt X.p0_le)]
    rfl
  have e3 : ∑ m : Fin (r - X.p0), f (nI X m) = ∑ i ∈ Finset.range (r - X.p0), g (X.p0 + i) := by
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hm : X.p0 + (m : ℕ) < r := by have := m.isLt; omega
    rw [hg, dif_pos hm]
    rfl
  rw [e1, e2, e3, ← Finset.sum_range_add, hr]

private lemma sum_three_rotate {α β γ M : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [AddCommMonoid M] (T : α → β → γ → M) :
    ∑ i, ∑ j, ∑ b, T i j b = ∑ b, ∑ i, ∑ j, T i j b :=
  (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm

lemma hpair_ortho {x : Frame X.Ψ r} (ho : X.IsOrtho x) (τ : X.Ψ) (c : Fin r → ℂ) (b : Fin r) :
    hermC τ.1 X.Gm (mat x τ *ᵥ c) (col (mat x τ) b) = c b * ((sgn X.p0 (b : ℕ) : ℝ) : ℂ) := by
  have hg : ∀ a, (∑ i, ∑ j, mat x τ i a * τ.1 (X.Gm i j) * conj (mat x τ j b)) =
      if a = b then ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) else 0 := by
    intro a
    have := congrFun (congrFun (ho τ) a) b
    simpa [gram, hermC, col, Matrix.diagonal_apply] using this
  simp only [hermC, Matrix.mulVec, dotProduct, col, Finset.sum_mul]
  rw [sum_three_rotate]
  have e : ∀ a, (∑ i, ∑ j, mat x τ i a * c a * τ.1 (X.Gm i j) * conj (mat x τ j b)) =
      c a * (if a = b then ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) else 0) := by
    intro a
    rw [← hg a, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp only [e, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma hermC_ortho {x : Frame X.Ψ r} (ho : X.IsOrtho x) (τ : X.Ψ) (u w : Fin r → ℂ) :
    hermC τ.1 X.Gm (mat x τ *ᵥ u) (mat x τ *ᵥ w) =
      dot (top X u) (top X w) - dot (bot X u) (bot X w) := by
  have hlin : ∀ U : Fin r → ℂ, hermC τ.1 X.Gm U (mat x τ *ᵥ w) =
      ∑ b, conj (w b) * hermC τ.1 X.Gm U (col (mat x τ) b) := by
    intro U
    simp only [hermC, col, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.mul_sum]
    rw [sum_three_rotate]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => ?_
    ring
  have hn : ∀ m : Fin (r - X.p0), ((nI X m : Fin r) : ℕ) = X.p0 + m := fun m => rfl
  have hs1 : ∀ a : Fin X.p0, sgn X.p0 ((Fin.castLE X.p0_le a : Fin r) : ℕ) = 1 :=
    fun a => by simp [sgn, a.isLt]
  have hs2 : ∀ m : Fin (r - X.p0), sgn X.p0 ((nI X m : Fin r) : ℕ) = -1 :=
    fun m => by simp [sgn, hn]
  rw [hlin]
  simp only [hpair_ortho X ho τ u]
  rw [sum_splitC X]
  simp only [hs1, hs2, dot, top, bot]
  push_cast
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1 <;> refine Finset.sum_congr rfl fun _ _ => ?_ <;> ring

lemma mulVec_ext (P : Matrix (Fin r) (Fin r) ℂ) (d : Fin X.p0 → ℂ) :
    P *ᵥ ext X d = ∑ a, d a • col P (Fin.castLE X.p0_le a) := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, col]
  rw [sum_splitC X]
  have h2 : ∑ m : Fin (r - X.p0), P i (nI X m) * ext X d (nI X m) = 0 := by
    refine Finset.sum_eq_zero fun m _ => ?_
    have hm : ¬ (((nI X m : Fin r) : ℕ) < X.p0) := by
      show ¬ (X.p0 + (m : ℕ) < X.p0)
      omega
    rw [show ext X d (nI X m) = 0 from dif_neg hm, mul_zero]
  rw [h2, add_zero]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show ext X d (Fin.castLE X.p0_le a) = d a from dif_pos a.isLt]
  try ring

lemma dot_top_col (Z : X.Coord) (τ : X.Ψ) (u : Fin r → ℂ) (b : Fin X.p0) :
    dot (top X u) (top X (col (X.lowBlock Z τ) (Fin.castLE X.p0_le b))) = top X u b := by
  simp [dot, top, col, L_pp]

lemma dot_bot_col (Z : X.Coord) (τ : X.Ψ) (u : Fin r → ℂ) (b : Fin X.p0) :
    dot (bot X u) (bot X (col (X.lowBlock Z τ) (Fin.castLE X.p0_le b))) =
      ((Matrix.of (Z τ))ᴴ *ᵥ bot X u) b := by
  simp [dot, bot, col, L_np, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, mul_comm]

lemma en_mulVec_le (Z : X.Coord) (τ : X.Ψ) {ρ : ℝ} (hρ : 0 ≤ ρ) (hZ : X.zN Z ≤ ρ)
    (a : Fin X.p0 → ℂ) : en (Matrix.of (Z τ) *ᵥ a) ≤ ρ * en a := by
  have hop : Data.opN (Matrix.of (Z τ)) ≤ ρ := (opN_le_zN X Z τ).trans hZ
  have hen : ∀ {n : ℕ} (v : Fin n → ℂ), en v = Real.sqrt (nsq v) := fun v => by
    simp [en, nsq, EuclideanSpace.norm_eq]
  rw [hen, hen]
  calc Real.sqrt (nsq (Matrix.of (Z τ) *ᵥ a)) ≤ Real.sqrt (Data.opN (Matrix.of (Z τ)) ^ 2 * nsq a) :=
        Real.sqrt_le_sqrt (nsq_mulVec_le_opN _ _)
    _ = Data.opN (Matrix.of (Z τ)) * Real.sqrt (nsq a) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (opN_nonneg _)]
    _ ≤ ρ * Real.sqrt (nsq a) := mul_le_mul_of_nonneg_right hop (Real.sqrt_nonneg _)

lemma en_adj_le (Z : X.Coord) (τ : X.Ψ) {ρ : ℝ} (hρ : 0 ≤ ρ) (hZ : X.zN Z ≤ ρ)
    (b : Fin (r - X.p0) → ℂ) : en ((Matrix.of (Z τ))ᴴ *ᵥ b) ≤ ρ * en b := by
  have hen : ∀ {n : ℕ} (v : Fin n → ℂ), en v = Real.sqrt (nsq v) := fun v => by
    simp [en, nsq, EuclideanSpace.norm_eq]
  have hsq : en ((Matrix.of (Z τ))ᴴ *ᵥ b) ^ 2 = nsq ((Matrix.of (Z τ))ᴴ *ᵥ b) := by
    rw [hen, Real.sq_sqrt]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h1 : nsq ((Matrix.of (Z τ))ᴴ *ᵥ b) ≤
      en b * (ρ * en ((Matrix.of (Z τ))ᴴ *ᵥ b)) := by
    rw [← re_dot_self, dot_adj, Matrix.conjTranspose_conjTranspose]
    calc (dot b (Matrix.of (Z τ) *ᵥ ((Matrix.of (Z τ))ᴴ *ᵥ b))).re
        ≤ ‖dot b (Matrix.of (Z τ) *ᵥ ((Matrix.of (Z τ))ᴴ *ᵥ b))‖ := Complex.re_le_norm _
      _ ≤ en b * en (Matrix.of (Z τ) *ᵥ ((Matrix.of (Z τ))ᴴ *ᵥ b)) := norm_dot_le _ _
      _ ≤ en b * (ρ * en ((Matrix.of (Z τ))ᴴ *ᵥ b)) :=
        mul_le_mul_of_nonneg_left (en_mulVec_le X Z τ hρ hZ _) (norm_nonneg _)
  have hy0 : 0 ≤ en ((Matrix.of (Z τ))ᴴ *ᵥ b) := norm_nonneg _
  have hb0 : 0 ≤ en b := norm_nonneg _
  rcases hy0.eq_or_lt with h | h
  · rw [← h]
    positivity
  · exact le_of_mul_le_mul_right (by nlinarith) h

private lemma hermC_sum_smul_left_fin_p0 (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (α : Fin X.p0 → ℂ) (w : Fin X.p0 → Fin r → ℂ) (z : Fin r → ℂ) :
    hermC τ G (∑ a, α a • w a) z = ∑ a, α a * hermC τ G (w a) z := by
  simp only [hermC, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [sum_three_rotate]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  ring

theorem maj_xZ' {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ : ρ ≤ 1 / 10) {Z : X.Coord} (hZ : X.zN Z ≤ ρ) (τ : X.Ψ) (v : Fin r → ℂ) :
    (1 - ρ) / (1 + ρ) * X.maj x τ v ≤ X.maj (X.xZ x Z) τ v ∧
      X.maj (X.xZ x Z) τ v ≤ (1 + ρ) / (1 - ρ) * X.maj x τ v := by
  have hρ1 : ρ < 1 := by linarith
  have hy : X.xZ x Z ∈ X.dom := xZ_mem_dom X hx ho (by linarith)
  have hdet : IsUnit (mat x τ).det := isUnit_iff_ne_zero.2 (hx τ).1
  obtain ⟨ν, rfl⟩ : ∃ ν, v = mat x τ *ᵥ ν :=
    ⟨(mat x τ)⁻¹ *ᵥ v, by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]⟩
  have hmy : mat (X.xZ x Z) τ = mat x τ * X.lowBlock Z τ := rfl
  have hcol : ∀ k, col (mat (X.xZ x Z) τ) k = mat x τ *ᵥ col (X.lowBlock Z τ) k := by
    intro k
    ext j
    simp [hmy, col, Matrix.mul_apply, Matrix.mulVec, dotProduct]

  have hpair : ∀ (u : Fin r → ℂ) (d : Fin X.p0),
      hermC τ.1 X.Gm (mat x τ *ᵥ u) (col (mat (X.xZ x Z) τ) (Fin.castLE X.p0_le d)) =
        top X u d - ((Matrix.of (Z τ))ᴴ *ᵥ bot X u) d := by
    intro u d
    rw [hcol, hermC_ortho X ho τ, dot_top_col X Z τ, dot_bot_col X Z τ]

  have hgx : X.gramPos x τ = 1 := by
    ext a b
    simp only [Data.gramPos, Matrix.submatrix_apply, ho τ, Matrix.diagonal_apply, Matrix.one_apply,
      Fin.castLE_inj]
    split_ifs with h
    · simp [sgn]
    · rfl
  have htopx : ∀ a : Fin X.p0,
      hermC τ.1 X.Gm (mat x τ *ᵥ ν) (col (mat x τ) (Fin.castLE X.p0_le a)) = top X ν a := by
    intro a
    rw [hpair_ortho X ho τ ν]
    simp [top, sgn]
  have hposx : X.posPart x τ (mat x τ *ᵥ ν) = nsq (top X ν) := by
    unfold Data.posPart
    rw [hgx, inv_one, ← re_dot_self]
    congr 1
    unfold dot
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single a (fun b _ hb => by rw [Matrix.one_apply_ne (Ne.symm hb)]; ring)
      (by simp), Matrix.one_apply_eq, htopx, mul_one]
  have hhv : (hermC τ.1 X.Gm (mat x τ *ᵥ ν) (mat x τ *ᵥ ν)).re =
      nsq (top X ν) - nsq (bot X ν) := by
    rw [hermC_ortho X ho τ, Complex.sub_re, re_dot_self, re_dot_self]
  have hmajx : X.maj x τ (mat x τ *ᵥ ν) = nsq (top X ν) + nsq (bot X ν) := by
    unfold Data.maj
    rw [hposx, hhv]
    ring

  have hGinv : (X.gramPos (X.xZ x Z) τ)⁻¹ * X.gramPos (X.xZ x Z) τ = 1 := by
    open scoped ComplexOrder in
    exact Matrix.nonsing_inv_mul _
      ((Matrix.isUnit_iff_isUnit_det _).1 (X.gramPos_posDef hy τ).isUnit)
  obtain ⟨h', hh'⟩ : ∃ h' : Fin X.p0 → ℂ, ∀ d, h' d =
      hermC τ.1 X.Gm (mat x τ *ᵥ ν) (col (mat (X.xZ x Z) τ) (Fin.castLE X.p0_le d)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨α, hα⟩ : ∃ α : Fin X.p0 → ℂ, ∀ a,
      α a = ∑ b, h' b * (X.gramPos (X.xZ x Z) τ)⁻¹ b a := ⟨_, fun _ => rfl⟩
  have hppos : X.ppos (X.xZ x Z) τ (mat x τ *ᵥ ν) =
      mat x τ *ᵥ (X.lowBlock Z τ *ᵥ ext X α) := by
    rw [Matrix.mulVec_mulVec, ← hmy, mulVec_ext X]
    unfold Data.ppos
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hα]
    simp only [hh']
  have htopP : top X (X.lowBlock Z τ *ᵥ ext X α) = α := by
    funext a
    simp only [top, mulVec_ext X, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, col, L_pp, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hbotP : bot X (X.lowBlock Z τ *ᵥ ext X α) = Matrix.of (Z τ) *ᵥ α := by
    rw [mulVec_ext X]
    funext m
    simp only [bot, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, col, L_np]
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    refine Finset.sum_congr rfl fun _ _ => ?_
    ring
  have horth : ∀ d, hermC τ.1 X.Gm (X.ppos (X.xZ x Z) τ (mat x τ *ᵥ ν))
      (col (mat (X.xZ x Z) τ) (Fin.castLE X.p0_le d)) = h' d := by
    intro d
    have hG : ∀ a, hermC τ.1 X.Gm (col (mat (X.xZ x Z) τ) (Fin.castLE X.p0_le a))
        (col (mat (X.xZ x Z) τ) (Fin.castLE X.p0_le d)) = X.gramPos (X.xZ x Z) τ a d :=
      fun a => (X.gramPos_apply _ τ a d).symm
    unfold Data.ppos
    rw [hermC_sum_smul_left_fin_p0]
    simp only [← hh', hG, Finset.sum_mul]
    rw [Finset.sum_comm]
    have e : h' d = ∑ b, h' b *
        ((X.gramPos (X.xZ x Z) τ)⁻¹ * X.gramPos (X.xZ x Z) τ) b d := by
      rw [hGinv]
      simp [Matrix.one_apply]
    rw [e]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring

  have hcoord : ∀ d, top X ν d - ((Matrix.of (Z τ))ᴴ *ᵥ bot X ν) d =
      α d - ((Matrix.of (Z τ))ᴴ *ᵥ (Matrix.of (Z τ) *ᵥ α)) d := by
    intro d
    have h1 := horth d
    rw [hppos, hpair, hh', hpair, htopP, hbotP] at h1
    exact h1.symm
  obtain ⟨q, hq⟩ : ∃ q, q = bot X ν - Matrix.of (Z τ) *ᵥ α := ⟨_, rfl⟩
  have hs : bot X ν = Matrix.of (Z τ) *ᵥ α + q := by
    rw [hq]
    abel
  have ht : top X ν = α + (Matrix.of (Z τ))ᴴ *ᵥ q := by
    funext d
    have := hcoord d
    rw [hq, Matrix.mulVec_sub]
    simp only [Pi.add_apply, Pi.sub_apply]
    linear_combination this

  have hposy0 : X.posPart (X.xZ x Z) τ (mat x τ *ᵥ ν) =
      (hermC τ.1 X.Gm (X.ppos (X.xZ x Z) τ (mat x τ *ᵥ ν)) (mat x τ *ᵥ ν)).re :=
    (congrArg Complex.re (X.hermC_ppos_self τ (X.xZ x Z) (mat x τ *ᵥ ν))).symm
  have hposy : X.posPart (X.xZ x Z) τ (mat x τ *ᵥ ν) =
      nsq α - nsq (Matrix.of (Z τ) *ᵥ α) := by
    rw [hposy0, hppos, hermC_ortho X ho τ, htopP, hbotP, ht, hs, dot_add_right, dot_add_right,
      ← dot_adj]
    simp only [Complex.sub_re, Complex.add_re, re_dot_self]
    ring
  have hmajy : X.maj (X.xZ x Z) τ (mat x τ *ᵥ ν) =
      2 * (nsq α - nsq (Matrix.of (Z τ) *ᵥ α)) - (nsq (top X ν) - nsq (bot X ν)) := by
    unfold Data.maj
    rw [hposy, hhv]
  have hen2 : ∀ {n : ℕ} (u : Fin n → ℂ), en u ^ 2 = nsq u := fun u => by
    rw [show en u = Real.sqrt (nsq u) by simp [en, nsq, EuclideanSpace.norm_eq],
      Real.sq_sqrt (show 0 ≤ nsq u from Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  have hnt : nsq (top X ν) = en α ^ 2 + en ((Matrix.of (Z τ))ᴴ *ᵥ q) ^ 2 +
      2 * (dot (Matrix.of (Z τ) *ᵥ α) q).re := by
    rw [ht, nsq_add, ← dot_adj, hen2, hen2]
  have hns : nsq (bot X ν) = en (Matrix.of (Z τ) *ᵥ α) ^ 2 + en q ^ 2 +
      2 * (dot (Matrix.of (Z τ) *ᵥ α) q).re := by
    rw [hs, nsq_add, hen2, hen2]
  have hu := en_mulVec_le X Z τ hρ0.le hZ α
  have hw := en_adj_le X Z τ hρ0.le hZ q
  have hD1 : |(dot (Matrix.of (Z τ) *ᵥ α) q).re| ≤ en (Matrix.of (Z τ) *ᵥ α) * en q :=
    (Complex.abs_re_le_norm _).trans (norm_dot_le _ _)
  have hD2 : |(dot (Matrix.of (Z τ) *ᵥ α) q).re| ≤ en α * en ((Matrix.of (Z τ))ᴴ *ᵥ q) := by
    rw [dot_adj]
    exact (Complex.abs_re_le_norm _).trans (norm_dot_le _ _)
  have hn0 : ∀ {n : ℕ} (u : Fin n → ℂ), 0 ≤ en u := fun u => norm_nonneg _
  obtain ⟨k1, k2⟩ := key_ineq (hn0 α) (hn0 q) (hn0 _) (hn0 _) hρ0 hρ1 hu hw hD1 hD2
  rw [hmajx, hmajy, hnt, hns, ← hen2 α, ← hen2 (Matrix.of (Z τ) *ᵥ α)]
  constructor
  · rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith [k1]
  · rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    nlinarith [k2]

end Frames

end

end UnipMove.MajH

namespace UnipMove

open ReciprocityTheory.ChartRestriction.G.FD NumberField

theorem sMajXZ {E : Type} [Field E] [NumberField E] [IsCMField E] : SMajXZ E := by
  intro r X x hx ho ρ hρ0 hρ Z hZ τ v
  exact MajH.maj_xZ' X hx ho hρ0 hρ hZ τ v

end UnipMove
