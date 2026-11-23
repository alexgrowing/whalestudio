import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.AEConst

noncomputable section

open scoped InnerProductSpace

namespace PositivityTheory.KB.SpectralGap.HilbertPairing

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def q (W : Submodule ℝ H) [W.HasOrthogonalProjection] (x : H) : H := x - W.starProjection x

section One

variable (W : Submodule ℝ H) [W.HasOrthogonalProjection]

lemma q_add (x y : H) : q W (x + y) = q W x + q W y := by
  simp only [q, map_add]; abel

lemma q_smul (c : ℝ) (x : H) : q W (c • x) = c • q W x := by
  simp only [q, map_smul, smul_sub]

lemma q_of_mem {x : H} (hx : x ∈ W) : q W x = 0 := by
  simp only [q, Submodule.starProjection_eq_self_iff.mpr hx, sub_self]

lemma mem_of_q {x : H} (hx : q W x = 0) : x ∈ W := by
  have : W.starProjection x = x := (sub_eq_zero.mp hx).symm
  exact Submodule.starProjection_eq_self_iff.mp this

lemma split (x : H) : x = W.starProjection x + q W x := by
  simp only [q]; abel

lemma inner_P_q (x : H) : ⟪W.starProjection x, q W x⟫_ℝ = 0 := by
  rw [real_inner_comm]
  exact Submodule.starProjection_inner_eq_zero x _ (W.starProjection_apply_mem x)

lemma norm_split (x : H) : ‖x‖ ^ 2 = ‖W.starProjection x‖ ^ 2 + ‖q W x‖ ^ 2 := by
  conv_lhs => rw [split W x]
  rw [norm_add_sq_real, inner_P_q, mul_zero, add_zero]

lemma inner_q_self (x : H) : ⟪q W x, x⟫_ℝ = ‖q W x‖ ^ 2 := by
  have h := split W x
  calc ⟪q W x, x⟫_ℝ = ⟪q W x, W.starProjection x + q W x⟫_ℝ := by rw [← h]
    _ = _ := by
      rw [inner_add_right, real_inner_comm, inner_P_q, zero_add, real_inner_self_eq_norm_sq]

lemma inner_x_P (x : H) : ⟪x, W.starProjection x⟫_ℝ = ‖W.starProjection x‖ ^ 2 := by
  have h := split W x
  calc ⟪x, W.starProjection x⟫_ℝ = ⟪W.starProjection x + q W x, W.starProjection x⟫_ℝ := by rw [← h]
    _ = _ := by
      rw [inner_add_left, real_inner_comm (W.starProjection x) (q W x), inner_P_q, add_zero, real_inner_self_eq_norm_sq]

lemma q_symm (x y : H) : ⟪q W x, y⟫_ℝ = ⟪x, q W y⟫_ℝ := by
  simp only [q, inner_sub_left, inner_sub_right, Submodule.inner_starProjection_left_eq_right]

end One

lemma pair_pos (Wa Wb K : Submodule ℝ H) [Wa.HasOrthogonalProjection] [Wb.HasOrthogonalProjection]
    (hK : K ≤ Wa) (hang : ∀ u ∈ Wa, u ∈ Kᗮ → ∀ u' ∈ Wb, |⟪u, u'⟫_ℝ| ≤ 1 / 5 * (‖u‖ * ‖u'‖))
    (x : H) (hx : x ∈ Kᗮ) : 4 / 5 * ‖x‖ ^ 2 ≤ ‖q Wa x‖ ^ 2 + ‖q Wb x‖ ^ 2 := by
  set a := Wa.starProjection x with ha_def
  set b := Wb.starProjection x with hb_def
  have ha : a ∈ Kᗮ := by
    rw [Submodule.mem_orthogonal]
    intro k hk
    rw [real_inner_comm, ha_def, Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr (hK hk)]
    exact (Submodule.mem_orthogonal' _ _).1 hx k hk
  have hab := hang a (Wa.starProjection_apply_mem x) ha b (Wb.starProjection_apply_mem x)
  have hxa := inner_x_P Wa x
  have hxb := inner_x_P Wb x
  have na := norm_split Wa x
  have nb := norm_split Wb x
  rw [← ha_def] at hxa na
  rw [← hb_def] at hxb nb
  have hcs : ⟪x, a + b⟫_ℝ ≤ ‖x‖ * ‖a + b‖ := real_inner_le_norm _ _
  have hn : ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + 2 * ⟪a, b⟫_ℝ + ‖b‖ ^ 2 := norm_add_sq_real a b
  rw [inner_add_right, hxa, hxb] at hcs
  set s := ‖a‖ ^ 2 + ‖b‖ ^ 2 with hs
  have hs0 : 0 ≤ s := by positivity
  have h1 : 2 * ⟪a, b⟫_ℝ ≤ 1 / 5 * s := by
    have := le_abs_self ⟪a, b⟫_ℝ
    nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  have h2 : s * s ≤ ‖x‖ ^ 2 * (6 / 5 * s) := by
    have e1 : s * s ≤ (‖x‖ * ‖a + b‖) * (‖x‖ * ‖a + b‖) := mul_self_le_mul_self hs0 hcs
    have e2 : ‖a + b‖ ^ 2 ≤ 6 / 5 * s := by rw [hn]; linarith
    calc s * s ≤ (‖x‖ * ‖a + b‖) * (‖x‖ * ‖a + b‖) := e1
      _ = ‖x‖ ^ 2 * ‖a + b‖ ^ 2 := by ring
      _ ≤ ‖x‖ ^ 2 * (6 / 5 * s) := mul_le_mul_of_nonneg_left e2 (by positivity)
  have h3 : s ≤ 6 / 5 * ‖x‖ ^ 2 := by nlinarith [sq_nonneg ‖x‖]
  linarith

lemma pair_all (Wa Wb K : Submodule ℝ H) [Wa.HasOrthogonalProjection] [Wb.HasOrthogonalProjection]
    [K.HasOrthogonalProjection] (hKa : K ≤ Wa) (hKb : K ≤ Wb)
    (hang : ∀ u ∈ Wa, u ∈ Kᗮ → ∀ u' ∈ Wb, |⟪u, u'⟫_ℝ| ≤ 1 / 5 * (‖u‖ * ‖u'‖)) (x : H) :
    4 / 5 * (‖q Wa x‖ ^ 2 + ‖q Wb x‖ ^ 2) ≤ ‖q Wa x + q Wb x‖ ^ 2 := by
  have hx : x = K.starProjection x + q K x := split K x
  have hk := K.starProjection_apply_mem x
  have hy : q K x ∈ Kᗮ := K.sub_starProjection_mem_orthogonal x
  set y := q K x
  have ea : q Wa x = q Wa y := by
    conv_lhs => rw [hx]
    rw [q_add, q_of_mem Wa (hKa hk), zero_add]
  have eb : q Wb x = q Wb y := by
    conv_lhs => rw [hx]
    rw [q_add, q_of_mem Wb (hKb hk), zero_add]
  rw [ea, eb]
  have hp := pair_pos Wa Wb K hKa hang y hy
  have hT : ⟪q Wa y + q Wb y, y⟫_ℝ = ‖q Wa y‖ ^ 2 + ‖q Wb y‖ ^ 2 := by
    rw [inner_add_left, inner_q_self, inner_q_self]
  have h0 : 0 ≤ ‖(q Wa y + q Wb y) - (4 / 5 : ℝ) • y‖ ^ 2 := by positivity
  rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, hT, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 4 / 5)] at h0
  nlinarith [sq_nonneg ‖y‖]

lemma three (u₁ u₂ u₃ : H) : ‖u₁ + u₂ + u₃‖ ^ 2 =
    ‖u₁ + u₂‖ ^ 2 + ‖u₃ + u₁‖ ^ 2 + ‖u₃ + u₂‖ ^ 2 - (‖u₁‖ ^ 2 + ‖u₂‖ ^ 2 + ‖u₃‖ ^ 2) := by
  simp only [norm_add_sq_real, inner_add_left]
  rw [real_inner_comm u₃ u₁, real_inner_comm u₃ u₂]
  ring

lemma form_cs (D : H →L[ℝ] H) (hsym : ∀ x y, ⟪D x, y⟫_ℝ = ⟪x, D y⟫_ℝ) (hpos : ∀ x, 0 ≤ ⟪D x, x⟫_ℝ)
    (x y : H) : ⟪D x, y⟫_ℝ ^ 2 ≤ ⟪D x, x⟫_ℝ * ⟪D y, y⟫_ℝ := by
  have e : ⟪D y, x⟫_ℝ = ⟪D x, y⟫_ℝ := by rw [hsym, real_inner_comm]
  have h : ∀ t : ℝ, 0 ≤ ⟪D y, y⟫_ℝ * (t * t) + (2 * ⟪D x, y⟫_ℝ) * t + ⟪D x, x⟫_ℝ := by
    intro t
    have := hpos (x + t • y)
    simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right] at this
    rw [e] at this
    nlinarith [this]
  have := discrim_le_zero h
  unfold discrim at this
  nlinarith [this]

lemma range_bound (D : H →L[ℝ] H) (hsym : ∀ x y, ⟪D x, y⟫_ℝ = ⟪x, D y⟫_ℝ) (hpos : ∀ x, 0 ≤ ⟪D x, x⟫_ℝ)
    (hsum : ∀ x, 3 / 5 * ⟪D x, x⟫_ℝ ≤ ‖D x‖ ^ 2) (x : H) :
    3 / 5 * ‖D x‖ ^ 2 ≤ ⟪D (D x), D x⟫_ℝ := by
  have hc := form_cs D hsym hpos x (D x)
  rw [real_inner_self_eq_norm_sq] at hc
  have h1 := hsum x
  have h2 := hpos x
  have h3 := hpos (D x)
  by_contra hne
  replace hne := not_le.mp hne
  have hY : 0 < ‖D x‖ ^ 2 := by linarith
  have h4 : ⟪D x, x⟫_ℝ * ⟪D (D x), D x⟫_ℝ ≤ 5 / 3 * ‖D x‖ ^ 2 * ⟪D (D x), D x⟫_ℝ :=
    mul_le_mul_of_nonneg_right (by linarith) h3
  have h5 : ‖D x‖ ^ 2 * ⟪D (D x), D x⟫_ℝ < ‖D x‖ ^ 2 * (3 / 5 * ‖D x‖ ^ 2) :=
    mul_lt_mul_of_pos_left hne hY
  nlinarith

lemma closure_bound [CompleteSpace H] (D : H →L[ℝ] H) (W : Submodule ℝ H)
    (hker : ∀ u, ⟪D u, u⟫_ℝ = 0 → u ∈ W) (hr : ∀ x, 3 / 5 * ‖D x‖ ^ 2 ≤ ⟪D (D x), D x⟫_ℝ)
    (z : H) (hz : z ∈ Wᗮ) : 3 / 5 * ‖z‖ ^ 2 ≤ ⟪D z, z⟫_ℝ := by
  have hle : (LinearMap.range (D : H →ₗ[ℝ] H))ᗮ ≤ W := by
    intro u hu
    apply hker
    exact (Submodule.mem_orthogonal _ _).1 hu (D u) (LinearMap.mem_range_self (D : H →ₗ[ℝ] H) u)
  have hz' : z ∈ (LinearMap.range (D : H →ₗ[ℝ] H)).topologicalClosure := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure]
    exact Submodule.orthogonal_le hle hz
  have hcl : IsClosed {y : H | 3 / 5 * ‖y‖ ^ 2 ≤ ⟪D y, y⟫_ℝ} :=
    isClosed_le (by fun_prop) (D.continuous.inner continuous_id)
  have hsub : ((LinearMap.range (D : H →ₗ[ℝ] H) : Submodule ℝ H) : Set H) ⊆ {y : H | 3 / 5 * ‖y‖ ^ 2 ≤ ⟪D y, y⟫_ℝ} := by
    rintro _ ⟨x, rfl⟩
    exact hr x
  have : z ∈ closure ((LinearMap.range (D : H →ₗ[ℝ] H) : Submodule ℝ H) : Set H) := by
    rw [← Submodule.topologicalClosure_coe]; exact hz'
  exact closure_minimal hsub hcl this

lemma upper (W₁ W₂ W₃ : Submodule ℝ H) [W₁.HasOrthogonalProjection] [W₂.HasOrthogonalProjection]
    [W₃.HasOrthogonalProjection]
    (hcl : ∀ z ∈ (W₁ ⊓ W₂ ⊓ W₃)ᗮ, 3 / 5 * ‖z‖ ^ 2 ≤ ‖q W₁ z‖ ^ 2 + ‖q W₂ z‖ ^ 2 + ‖q W₃ z‖ ^ 2)
    (v w : H) (hv : v ∈ W₁ ⊓ W₂) (hvp : v ∈ (W₁ ⊓ W₂ ⊓ W₃)ᗮ) (hw : w ∈ W₁ ⊓ W₃)
    (hwp : w ∈ (W₁ ⊓ W₂ ⊓ W₃)ᗮ) : ⟪v, w⟫_ℝ ≤ 2 / 5 * (‖v‖ * ‖w‖) := by
  have hv1 : v ∈ W₁ := (Submodule.mem_inf.1 hv).1
  have hv2 : v ∈ W₂ := (Submodule.mem_inf.1 hv).2
  have hw1 : w ∈ W₁ := (Submodule.mem_inf.1 hw).1
  have hw3 : w ∈ W₃ := (Submodule.mem_inf.1 hw).2
  have hxp : ‖w‖ • v + ‖v‖ • w ∈ (W₁ ⊓ W₂ ⊓ W₃)ᗮ :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ hvp) (Submodule.smul_mem _ _ hwp)
  have e1 : q W₁ (‖w‖ • v + ‖v‖ • w) = 0 :=
    q_of_mem W₁ (W₁.add_mem (W₁.smul_mem _ hv1) (W₁.smul_mem _ hw1))
  have e2 : q W₂ (‖w‖ • v + ‖v‖ • w) = ‖v‖ • q W₂ w := by
    rw [q_add, q_smul, q_smul, q_of_mem W₂ hv2, smul_zero, zero_add]
  have e3 : q W₃ (‖w‖ • v + ‖v‖ • w) = ‖w‖ • q W₃ v := by
    rw [q_add, q_smul, q_smul, q_of_mem W₃ hw3, smul_zero, add_zero]
  have h := hcl _ hxp
  rw [e1, e2, e3, norm_zero, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_norm,
    abs_norm] at h
  have hxn : ‖‖w‖ • v + ‖v‖ • w‖ ^ 2 = 2 * (‖v‖ * ‖w‖) ^ 2 + 2 * (‖v‖ * ‖w‖) * ⟪v, w⟫_ℝ := by
    rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_norm, abs_norm]
    ring
  rw [hxn] at h
  have n2 := norm_split W₂ w
  have n3 := norm_split W₃ v
  have c2 : |⟪v, w⟫_ℝ| ≤ ‖W₂.starProjection w‖ * ‖v‖ := by
    have : ⟪W₂.starProjection w, v⟫_ℝ = ⟪w, v⟫_ℝ := by
      rw [Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr hv2]
    rw [real_inner_comm, ← this]
    exact abs_real_inner_le_norm _ _
  have c3 : |⟪v, w⟫_ℝ| ≤ ‖W₃.starProjection v‖ * ‖w‖ := by
    have : ⟪W₃.starProjection v, w⟫_ℝ = ⟪v, w⟫_ℝ := by
      rw [Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr hw3]
    rw [← this]
    exact abs_real_inner_le_norm _ _
  have s2 : ⟪v, w⟫_ℝ ^ 2 ≤ (‖W₂.starProjection w‖ * ‖v‖) ^ 2 :=
    sq_le_sq.2 (c2.trans (le_abs_self _))
  have s3 : ⟪v, w⟫_ℝ ^ 2 ≤ (‖W₃.starProjection v‖ * ‖w‖) ^ 2 :=
    sq_le_sq.2 (c3.trans (le_abs_self _))
  have m2 : ‖v‖ ^ 2 * ‖w‖ ^ 2 = ‖v‖ ^ 2 * ‖W₂.starProjection w‖ ^ 2 + ‖v‖ ^ 2 * ‖q W₂ w‖ ^ 2 := by
    rw [n2]; ring
  have m3 : ‖w‖ ^ 2 * ‖v‖ ^ 2 = ‖w‖ ^ 2 * ‖W₃.starProjection v‖ ^ 2 + ‖w‖ ^ 2 * ‖q W₃ v‖ ^ 2 := by
    rw [n3]; ring
  have key : 3 / 5 * (2 * (‖v‖ * ‖w‖) ^ 2 + 2 * (‖v‖ * ‖w‖) * ⟪v, w⟫_ℝ) ≤
      2 * (‖v‖ * ‖w‖) ^ 2 - 2 * ⟪v, w⟫_ℝ ^ 2 := by
    nlinarith [h, s2, s3, m2, m3]
  have hcs : -(‖v‖ * ‖w‖) ≤ ⟪v, w⟫_ℝ := (abs_le.1 (abs_real_inner_le_norm v w)).1
  have hA : 0 ≤ ‖v‖ * ‖w‖ := by positivity
  nlinarith [key, hcs, hA]

end PositivityTheory.KB.SpectralGap.HilbertPairing

namespace PositivityTheory.KB.SpectralGap

open HilbertPairing in
theorem hilb_holds : Hilb := by
  intro H _ _ _ W₁ W₂ W₃ K₁₂ K₁₃ K₂₃ c1 c2 c3 c12 c13 c23 d12 d13 d23 a12 a13 a23 v hv hvp w hw
  have : CompleteSpace W₁ := c1.completeSpace_coe
  have : CompleteSpace W₂ := c2.completeSpace_coe
  have : CompleteSpace W₃ := c3.completeSpace_coe
  have : CompleteSpace K₁₂ := c12.completeSpace_coe
  have : CompleteSpace K₁₃ := c13.completeSpace_coe
  have : CompleteSpace K₂₃ := c23.completeSpace_coe
  have c123 : IsClosed ((W₁ ⊓ W₂ ⊓ W₃ : Submodule ℝ H) : Set H) := by
    rw [Submodule.coe_inf, Submodule.coe_inf]; exact (c1.inter c2).inter c3
  have : CompleteSpace ↥(W₁ ⊓ W₂ ⊓ W₃) := c123.completeSpace_coe
  let D : H →L[ℝ] H := (ContinuousLinearMap.id ℝ H - W₁.starProjection) +
    (ContinuousLinearMap.id ℝ H - W₂.starProjection) + (ContinuousLinearMap.id ℝ H - W₃.starProjection)
  have hD : ∀ x, D x = q W₁ x + q W₂ x + q W₃ x := fun x => by simp [D, q]
  have hself : ∀ x, ⟪D x, x⟫_ℝ = ‖q W₁ x‖ ^ 2 + ‖q W₂ x‖ ^ 2 + ‖q W₃ x‖ ^ 2 := by
    intro x
    rw [hD, inner_add_left, inner_add_left, inner_q_self, inner_q_self, inner_q_self]
  have hsym : ∀ x y, ⟪D x, y⟫_ℝ = ⟪x, D y⟫_ℝ := by
    intro x y
    rw [hD, hD, inner_add_left, inner_add_left, inner_add_right, inner_add_right, q_symm, q_symm,
      q_symm]
  have hpos : ∀ x, 0 ≤ ⟪D x, x⟫_ℝ := fun x => by rw [hself]; positivity
  have hsum : ∀ x, 3 / 5 * ⟪D x, x⟫_ℝ ≤ ‖D x‖ ^ 2 := by
    intro x
    have p12 := pair_all W₁ W₂ K₁₂ (d12.trans inf_le_left) (d12.trans inf_le_right) a12 x
    have p31 := pair_all W₃ W₁ K₁₃ (d13.trans inf_le_right) (d13.trans inf_le_left) a13 x
    have p32 := pair_all W₃ W₂ K₂₃ (d23.trans inf_le_right) (d23.trans inf_le_left) a23 x
    rw [hself, hD, three]
    linarith
  have hker : ∀ u, ⟪D u, u⟫_ℝ = 0 → u ∈ W₁ ⊓ W₂ ⊓ W₃ := by
    intro u hu
    rw [hself] at hu
    have z1 : ‖q W₁ u‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖q W₁ u‖, sq_nonneg ‖q W₂ u‖, sq_nonneg ‖q W₃ u‖]
    have z2 : ‖q W₂ u‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖q W₁ u‖, sq_nonneg ‖q W₂ u‖, sq_nonneg ‖q W₃ u‖]
    have z3 : ‖q W₃ u‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖q W₁ u‖, sq_nonneg ‖q W₂ u‖, sq_nonneg ‖q W₃ u‖]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, norm_eq_zero] at z1 z2 z3
    exact Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨mem_of_q W₁ z1, mem_of_q W₂ z2⟩, mem_of_q W₃ z3⟩
  have hcl : ∀ z ∈ (W₁ ⊓ W₂ ⊓ W₃)ᗮ, 3 / 5 * ‖z‖ ^ 2 ≤ ‖q W₁ z‖ ^ 2 + ‖q W₂ z‖ ^ 2 + ‖q W₃ z‖ ^ 2 := by
    intro z hz
    rw [← hself]
    exact closure_bound D _ hker (range_bound D hsym hpos hsum) z hz
  have hPw := (W₁ ⊓ W₂ ⊓ W₃).starProjection_apply_mem w
  have hle : W₁ ⊓ W₂ ⊓ W₃ ≤ W₁ ⊓ W₃ := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hw' : q (W₁ ⊓ W₂ ⊓ W₃) w ∈ W₁ ⊓ W₃ := Submodule.sub_mem _ hw (hle hPw)
  have hw'p : q (W₁ ⊓ W₂ ⊓ W₃) w ∈ (W₁ ⊓ W₂ ⊓ W₃)ᗮ := Submodule.sub_starProjection_mem_orthogonal w
  have hvw : ⟪v, w⟫_ℝ = ⟪v, q (W₁ ⊓ W₂ ⊓ W₃) w⟫_ℝ := by
    have h0 : ⟪v, (W₁ ⊓ W₂ ⊓ W₃).starProjection w⟫_ℝ = 0 := (Submodule.mem_orthogonal' _ _).1 hvp _ hPw
    simp only [q, inner_sub_right, h0, sub_zero]
  have hnw : ‖q (W₁ ⊓ W₂ ⊓ W₃) w‖ ≤ ‖w‖ := by
    have := norm_split (W₁ ⊓ W₂ ⊓ W₃) w
    nlinarith [norm_nonneg (q (W₁ ⊓ W₂ ⊓ W₃) w), norm_nonneg w,
      sq_nonneg ‖(W₁ ⊓ W₂ ⊓ W₃).starProjection w‖]
  have u1 := upper W₁ W₂ W₃ hcl v _ hv hvp hw' hw'p
  have u2 := upper W₁ W₂ W₃ hcl v _ hv hvp (Submodule.neg_mem _ hw') (Submodule.neg_mem _ hw'p)
  rw [inner_neg_right, norm_neg] at u2
  have hm := mul_le_mul_of_nonneg_left hnw (norm_nonneg v)
  rw [hvw, abs_le]
  constructor <;> nlinarith [hm]

end PositivityTheory.KB.SpectralGap

end
