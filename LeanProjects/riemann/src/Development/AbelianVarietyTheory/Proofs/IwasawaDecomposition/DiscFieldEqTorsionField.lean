import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.DiscRoot

open Polynomial WeierstrassCurve

theorem exists_vieta_two (p q : ℂ) : ∃ x y : ℂ, x + y = p ∧ x * y = q := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (p ^ 2 - 4 * q) (show 0 < 2 by norm_num)
  exact ⟨(p + s) / 2, (p - s) / 2, by ring, by linear_combination (-1 / 4 : ℂ) * hs⟩

theorem exists_vieta_three (p q r : ℂ) :
    ∃ x y z : ℂ, x + y + z = p ∧ x * y + x * z + y * z = q ∧ x * y * z = r := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (X ^ 3 - C p * X ^ 2 + C q * X - C r : ℂ[X]) (by
    have : (X ^ 3 - C p * X ^ 2 + C q * X - C r : ℂ[X]).degree = 3 := by compute_degree!
    rw [this]; decide)
  simp only [IsRoot.def, eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C] at hx
  obtain ⟨y, z, h1, h2⟩ := exists_vieta_two (p - x) (q - x * (p - x))
  exact ⟨x, y, z, by linear_combination h1, by linear_combination x * h1 + h2, by linear_combination x * h2 + hx⟩

theorem exists_vieta_four (p q r t : ℂ) :
    ∃ x y z w : ℂ, x + y + z + w = p ∧ x * y + x * z + x * w + y * z + y * w + z * w = q ∧
      x * y * z + x * y * w + x * z * w + y * z * w = r ∧ x * y * z * w = t := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (X ^ 4 - C p * X ^ 3 + C q * X ^ 2 - C r * X + C t : ℂ[X]) (by
    have : (X ^ 4 - C p * X ^ 3 + C q * X ^ 2 - C r * X + C t : ℂ[X]).degree = 4 := by compute_degree!
    rw [this]; decide)
  simp only [IsRoot.def, eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C] at hx
  obtain ⟨y, z, w, h1, h2, h3⟩ := exists_vieta_three (p - x) (q - x * (p - x)) (r - x * (q - x * (p - x)))
  exact ⟨x, y, z, w, by linear_combination h1, by linear_combination x * h1 + h2, by linear_combination x * h2 + h3,
    by linear_combination x * h3 - hx⟩

variable {W : WeierstrassCurve ℂ}

theorem four_torsion (hΔ : W.Δ ≠ 0) {e s t : ℂ} (h2 : W.b₂ = -4 * (3 * e - s ^ 2 - t ^ 2))
    (h4 : W.b₄ = 2 * (e * (e - s ^ 2) + e * (e - t ^ 2) + (e - s ^ 2) * (e - t ^ 2)))
    (h6 : W.b₆ = -4 * (e * (e - s ^ 2) * (e - t ^ 2))) (hs : s ≠ 0) (ht : t ≠ 0) (hst : s + t ≠ 0) :
    e + s * t ∈ torsionCoords W 4 ∧
      s * t * (s + t) - (W.a₁ * (e + s * t) + W.a₃) / 2 ∈ torsionCoords W 4 := by
  simp only [b₂, b₄, b₆] at h2 h4 h6
  set x := e + s * t with hx
  set y := s * t * (s + t) - (W.a₁ * x + W.a₃) / 2 with hy
  have heq : W.toAffine.Equation x y := by
    rw [Affine.equation_iff]
    simp only [toAffine]
    rw [hy, hx]
    linear_combination (-(e + s * t) ^ 2 / 4) * h2 - (e + s * t) / 2 * h4 - 1 / 4 * h6
  have hns : W.toAffine.Nonsingular x y := (Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).1 heq
  have hd : y - W.toAffine.negY x y = 2 * (s * t * (s + t)) := by
    simp only [Affine.negY, toAffine]
    rw [hy]; ring
  have hd0 : y - W.toAffine.negY x y ≠ 0 := by
    rw [hd]; exact mul_ne_zero two_ne_zero (mul_ne_zero (mul_ne_zero hs ht) hst)
  have hne : y ≠ W.toAffine.negY x y := sub_ne_zero.1 hd0
  have hl : W.toAffine.slope x x y y = s + t - W.a₁ / 2 := by
    rw [Affine.slope_of_Y_ne rfl hne, div_eq_iff hd0, hd]
    simp only [toAffine]
    rw [hy, hx]
    linear_combination (e + s * t) / 2 * h2 + 1 / 2 * h4
  have h0 : 4 • Affine.Point.some x y hns = 0 := by
    rw [show 4 = 2 * 2 from rfl, mul_smul, two_smul, two_smul, Affine.Point.add_self_of_Y_ne hne]
    apply Affine.Point.add_self_of_Y_eq
    simp only [Affine.addY, Affine.negY, Affine.negAddY, Affine.addX, hl, toAffine]
    rw [hy, hx]
    linear_combination (s + t) / 2 * h2
  exact ⟨⟨x, y, hns, h0, Or.inl rfl⟩, ⟨x, y, hns, h0, Or.inr rfl⟩⟩

theorem three_torsion (hΔ : W.Δ ≠ 0) {x : ℂ}
    (h : 3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈ = 0) : x ∈ torsionCoords W 3 := by
  simp only [b₂, b₄, b₆, b₈] at h
  obtain ⟨y, y', h1, h2⟩ := exists_vieta_two (-(W.a₁ * x + W.a₃)) (-(x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆))
  have heq : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
    linear_combination y * h1 - h2
  have hns : W.toAffine.Nonsingular x y :=
    (Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).1 ((Affine.equation_iff _ _).2 heq)
  have key : (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) ^ 2 +
      W.a₁ * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) * (2 * y + W.a₁ * x + W.a₃) =
      (W.a₂ + 3 * x) * (2 * y + W.a₁ * x + W.a₃) ^ 2 := by
    linear_combination -h - (W.a₁ ^ 2 + 4 * W.a₂ + 12 * x) * heq
  have hd : y - W.toAffine.negY x y = 2 * y + W.a₁ * x + W.a₃ := by
    simp only [Affine.negY, toAffine]; ring
  have hd0 : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
    intro h0
    rw [h0] at key
    have h3 : 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y = 0 := by
      apply pow_eq_zero_iff (n := 2) two_ne_zero |>.1
      linear_combination key
    rcases ((Affine.nonsingular_iff _ _).1 hns).2 with h4 | h4
    · exact h4 (by simp only [toAffine]; linear_combination -h3)
    · exact h4 (by simp only [toAffine]; linear_combination h0)
  have hne : y ≠ W.toAffine.negY x y := sub_ne_zero.1 (hd ▸ hd0)
  have hX : W.toAffine.addX x x (W.toAffine.slope x x y y) = x := by
    have hl : W.toAffine.slope x x y y * (2 * y + W.a₁ * x + W.a₃) =
        3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
      rw [Affine.slope_of_Y_ne rfl hne, hd, div_mul_cancel₀ _ hd0]
    rw [← hl] at key
    simp only [Affine.addX, toAffine] at key ⊢
    apply mul_right_cancel₀ (pow_ne_zero 2 hd0)
    linear_combination key
  refine ⟨x, y, hns, ?_, Or.inl rfl⟩
  rw [show 3 = 2 + 1 from rfl, add_smul, two_smul, one_smul, Affine.Point.add_self_of_Y_ne hne]
  apply Affine.Point.add_of_Y_eq hX
  simp only [Affine.addY, Affine.negAddY, hX, sub_self, mul_zero, zero_add]

variable {M : IntermediateField ℚ ℂ}

theorem sqrt_mem (hΔ : W.Δ ≠ 0) (ha₁ : W.a₁ ∈ M) (ha₃ : W.a₃ ∈ M) (hM : torsionCoords W 4 ⊆ M) {e₁ e₂ e₃ s : ℂ}
    (h2 : W.b₂ = -4 * (e₁ + e₂ + e₃)) (h4 : W.b₄ = 2 * (e₁ * e₂ + e₁ * e₃ + e₂ * e₃)) (h6 : W.b₆ = -4 * (e₁ * e₂ * e₃))
    (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃) (hs : s ^ 2 = e₁ - e₂) : s ∈ M := by
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (e₁ - e₃) (show 0 < 2 by norm_num)
  have key : ∀ t : ℂ, t ^ 2 = e₁ - e₃ → s * t ≠ 0 ∧ e₁ + s * t ∈ M ∧ s * t * (s + t) ∈ M := by
    intro t ht
    have hs0 : s ≠ 0 := fun h => h12 (by rw [h] at hs; linear_combination -hs)
    have ht0 : t ≠ 0 := fun h => h13 (by rw [h] at ht; linear_combination -ht)
    have hst : s + t ≠ 0 := fun h => h23 (by linear_combination hs - ht - (s - t) * h)
    obtain ⟨k1, k2⟩ := four_torsion (e := e₁) hΔ (by rw [hs, ht, h2]; ring) (by rw [hs, ht, h4]; ring)
      (by rw [hs, ht, h6]; ring) hs0 ht0 hst
    have k1 : e₁ + s * t ∈ M := hM k1
    have k2 : _ ∈ M := hM k2
    refine ⟨mul_ne_zero hs0 ht0, k1, ?_⟩
    have := add_mem k2 (div_mem (add_mem (mul_mem ha₁ k1) ha₃) (ofNat_mem M 2))
    rwa [sub_add_cancel] at this
  obtain ⟨h0, k1, k2⟩ := key t ht
  obtain ⟨-, k3, k4⟩ := key (-t) (by rw [neg_sq, ht])
  have hs0 : s ≠ 0 := left_ne_zero_of_mul h0
  have ht0 : t ≠ 0 := right_ne_zero_of_mul h0
  have : s = (s * t * (s + t) - s * -t * (s + -t)) / ((e₁ + s * t) - (e₁ + s * -t)) := by
    rw [eq_div_iff (by
      rw [show (e₁ + s * t) - (e₁ + s * -t) = 2 * (s * t) by ring]
      exact mul_ne_zero two_ne_zero h0)]
    ring
  rw [this]
  exact div_mem (sub_mem k2 k4) (sub_mem k1 k3)

theorem fourth_root_mem (hΔ : W.Δ ≠ 0) (ha₁ : W.a₁ ∈ M) (ha₃ : W.a₃ ∈ M) (hM : torsionCoords W 4 ⊆ M) {c : ℂ}
    (hc : c ^ 4 = W.Δ) : c ∈ M := by
  obtain ⟨e₁, e₂, e₃, k2, k4, k6⟩ := exists_vieta_three (-W.b₂ / 4) (W.b₄ / 2) (-W.b₆ / 4)
  have h2 : W.b₂ = -4 * (e₁ + e₂ + e₃) := by linear_combination 4 * k2
  have h4 : W.b₄ = 2 * (e₁ * e₂ + e₁ * e₃ + e₂ * e₃) := by linear_combination -2 * k4
  have h6 : W.b₆ = -4 * (e₁ * e₂ * e₃) := by linear_combination 4 * k6
  have h8 : W.b₈ = (W.b₂ * W.b₆ - W.b₄ ^ 2) / 4 := by linear_combination W.b_relation / 4
  have hD : W.Δ = 16 * ((e₁ - e₂) * (e₁ - e₃) * (e₂ - e₃)) ^ 2 := by
    rw [Δ, h8, h2, h4, h6]; ring
  have h12 : e₁ ≠ e₂ := fun h => hΔ (by rw [hD, h]; ring)
  have h13 : e₁ ≠ e₃ := fun h => hΔ (by rw [hD, h]; ring)
  have h23 : e₂ ≠ e₃ := fun h => hΔ (by rw [hD, h]; ring)
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (e₁ - e₂) (show 0 < 2 by norm_num)
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (e₁ - e₃) (show 0 < 2 by norm_num)
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (e₂ - e₃) (show 0 < 2 by norm_num)
  have ms : s ∈ M := sqrt_mem hΔ ha₁ ha₃ hM h2 h4 h6 h12 h13 h23 hs
  have mt : t ∈ M := sqrt_mem (e₁ := e₁) (e₂ := e₃) (e₃ := e₂) hΔ ha₁ ha₃ hM (by rw [h2]; ring) (by rw [h4]; ring)
    (by rw [h6]; ring) h13 h12 h23.symm ht
  have mu : u ∈ M := sqrt_mem (e₁ := e₂) (e₂ := e₃) (e₃ := e₁) hΔ ha₁ ha₃ hM (by rw [h2]; ring) (by rw [h4]; ring)
    (by rw [h6]; ring) h23 h12.symm h13.symm hu
  have mi : Complex.I * s ∈ M := sqrt_mem (e₁ := e₂) (e₂ := e₁) (e₃ := e₃) hΔ ha₁ ha₃ hM (by rw [h2]; ring)
    (by rw [h4]; ring) (by rw [h6]; ring) h12.symm h23 h13 (by rw [mul_pow, Complex.I_sq, hs]; ring)
  have mb : 2 * (s * t * u) ∈ M := mul_mem (ofNat_mem M 2) (mul_mem (mul_mem ms mt) mu)
  have mb' : Complex.I * (2 * (s * t * u)) ∈ M := by
    rw [show Complex.I * (2 * (s * t * u)) = 2 * (Complex.I * s * t * u) by ring]
    exact mul_mem (ofNat_mem M 2) (mul_mem (mul_mem mi mt) mu)
  have hb : (2 * (s * t * u)) ^ 4 = c ^ 4 := by
    rw [hc, hD, ← hs, ← ht, ← hu]; ring
  generalize 2 * (s * t * u) = b at mb mb' hb
  have hf : (c - b) * (c + b) * ((c - Complex.I * b) * (c + Complex.I * b)) = 0 := by
    linear_combination -hb - (c ^ 2 - b ^ 2) * b ^ 2 * Complex.I_sq
  simp only [mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg] at hf
  rcases hf with (h | h) | h | h <;> rw [h]
  exacts [mb, neg_mem mb, mb', neg_mem mb']

theorem cube_root_mem (hΔ : W.Δ ≠ 0) (hM : torsionCoords W 3 ⊆ M) {c : ℂ} (hc : c ^ 3 = W.Δ) : c ∈ M := by
  obtain ⟨x, y, z, w, k2, k4, k6, k8⟩ := exists_vieta_four (-W.b₂ / 3) W.b₄ (-W.b₆) (W.b₈ / 3)
  have h2 : W.b₂ = -3 * (x + y + z + w) := by linear_combination 3 * k2
  have h4 := k4.symm
  have h6 : W.b₆ = -(x * y * z + x * y * w + x * z * w + y * z * w) := by linear_combination k6
  have h8 : W.b₈ = 3 * (x * y * z * w) := by linear_combination -3 * k8
  have mx : x ∈ M := hM (three_torsion hΔ (by rw [h2, h4, h6, h8]; ring))
  have my : y ∈ M := hM (three_torsion hΔ (by rw [h2, h4, h6, h8]; ring))
  have mz : z ∈ M := hM (three_torsion hΔ (by rw [h2, h4, h6, h8]; ring))
  have mw : w ∈ M := hM (three_torsion hΔ (by rw [h2, h4, h6, h8]; ring))
  have m4 : W.b₄ ∈ M := by
    rw [h4]
    exact add_mem (add_mem (add_mem (add_mem (add_mem (mul_mem mx my) (mul_mem mx mz)) (mul_mem mx mw))
      (mul_mem my mz)) (mul_mem my mw)) (mul_mem mz mw)
  have hr := W.b_relation
  have res : ∀ u : ℂ, u ^ 3 - W.b₄ * u ^ 2 + (W.b₂ * W.b₆ - 4 * W.b₈) / 3 * u -
      (W.b₂ ^ 2 * W.b₈ / 27 + W.b₆ ^ 2 - 4 * W.b₄ * W.b₈ / 3) = 0 → (W.b₄ - 3 * u) ^ 3 = W.Δ := by
    intro u hu
    rw [Δ]
    linear_combination -27 * hu + (9 * W.b₄ - 9 * u) * hr
  have a1 := res (x * y + z * w) (by rw [h2, h4, h6, h8]; ring)
  have a2 := res (x * z + y * w) (by rw [h2, h4, h6, h8]; ring)
  have a3 := res (x * w + y * z) (by rw [h2, h4, h6, h8]; ring)
  have m1 : W.b₄ - 3 * (x * y + z * w) ∈ M :=
    sub_mem m4 (mul_mem (ofNat_mem M 3) (add_mem (mul_mem mx my) (mul_mem mz mw)))
  have m2 : W.b₄ - 3 * (x * z + y * w) ∈ M :=
    sub_mem m4 (mul_mem (ofNat_mem M 3) (add_mem (mul_mem mx mz) (mul_mem my mw)))
  rw [show W.b₄ - 3 * (x * w + y * z) = -((W.b₄ - 3 * (x * y + z * w)) + (W.b₄ - 3 * (x * z + y * w))) by
    linear_combination 3 * h4] at a3
  generalize W.b₄ - 3 * (x * y + z * w) = a at a1 a3 m1
  generalize W.b₄ - 3 * (x * z + y * w) = b at a2 a3 m2
  have hab : b - a ≠ 0 := fun h => hΔ (by
    rw [sub_eq_zero.1 h] at a3
    linear_combination (-8 / 9 : ℂ) * a1 - 1 / 9 * a3)
  have hq : b ^ 2 + b * a + a ^ 2 = 0 := mul_left_cancel₀ hab (by linear_combination a2 - a1)
  have hf : (c - a) * (c - b) * (c + (a + b)) = 0 := by
    linear_combination hc - a1 + (a - c) * hq
  simp only [mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg] at hf
  rcases hf with (h | h) | h <;> rw [h]
  exacts [m1, m2, neg_mem (add_mem m1 m2)]

theorem twelfth_root_mem (hΔ : W.Δ ≠ 0) (ha₁ : W.a₁ ∈ M) (ha₃ : W.a₃ ∈ M) (hM : torsionCoords W 12 ⊆ M) {z : ℂ}
    (hz : z ^ 12 = W.Δ) : z ∈ M := by
  have h0 : z ≠ 0 := fun h => hΔ (by rw [← hz, h]; norm_num)
  have h3 : z ^ 3 ∈ M := fourth_root_mem hΔ ha₁ ha₃ ((torsionCoords_mono W (by norm_num)).trans hM)
    (by rw [← hz]; ring)
  have h4 : z ^ 4 ∈ M := cube_root_mem hΔ ((torsionCoords_mono W (by norm_num)).trans hM) (by rw [← hz]; ring)
  rw [show z = z ^ 4 / z ^ 3 by field_simp]
  exact div_mem h4 h3

theorem discField_eq_torsionField (d : ℕ) (F : IntermediateField ℚ ℂ) (A : WeierstrassCurve F) [A.IsElliptic] :
    discField d A = torsionField d A := by
  refine le_antisymm (sup_le le_rfl ?_) (torsionField_le_discField d A)
  rw [IntermediateField.adjoin_le_iff]
  intro z (hz : z ^ 12 = _)
  have hF : F ≤ torsionField d A := le_sup_right.trans (hilbertField_le_torsionField d A)
  have hD : (A.baseChange ℂ).Δ = (A.Δ : ℂ) := by rw [baseChange, map_Δ]; rfl
  refine twelfth_root_mem (W := A.baseChange ℂ) ?_ (hF A.a₁.2) (hF A.a₃.2) ?_ (hD ▸ hz)
  · rw [hD]
    exact fun h => A.isUnit_Δ.ne_zero (Subtype.ext h)
  · exact fun w hw => (le_sup_right : _ ≤ torsionField d A) (IntermediateField.subset_adjoin ℚ _ hw)

end GlobalTheory.Mem.DiscRoot
