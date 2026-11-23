import Mathlib
import Formalism.UnipotentAdelicQuotients.SWXSDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.QuadricCount

open ComplexConjugate

variable {k : Type} [Field k] [Fintype k] {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def quadForm (B : Matrix ι ι k) (x : ι → k) : k :=
  (2 : k)⁻¹ * (x ⬝ᵥ (B *ᵥ x))

theorem quadForm_add (h2 : (2 : k) ≠ 0) {B : Matrix ι ι k} (hB : B.IsSymm) (y z : ι → k) :
    quadForm B (y + z) = quadForm B y + quadForm B z + y ⬝ᵥ (B *ᵥ z) := by
  have hs : z ⬝ᵥ (B *ᵥ y) = y ⬝ᵥ (B *ᵥ z) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hB.eq, dotProduct_comm]
  unfold quadForm
  rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, hs]
  field_simp
  ring

theorem sum_char_dot (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) {w : ι → k} (hw : w ≠ 0) :
    ∑ y : ι → k, ψ (y ⬝ᵥ w) = 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
  obtain ⟨c, hc⟩ := (AddChar.ne_one_iff).mp hψ
  have hi' : w i ≠ 0 := hi
  have he : (Pi.single i (c / w i) : ι → k) ⬝ᵥ w = c := by
    rw [single_dotProduct]
    field_simp
  have hS : ψ c * ∑ y : ι → k, ψ (y ⬝ᵥ w) = ∑ y : ι → k, ψ (y ⬝ᵥ w) := by
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.addRight (Pi.single i (c / w i) : ι → k)) _ _ ?_
    intro x
    rw [Equiv.coe_addRight, add_dotProduct, he, AddChar.map_add_eq_mul, mul_comm]
  have h0 : (ψ c - 1) * ∑ y : ι → k, ψ (y ⬝ᵥ w) = 0 := by
    rw [sub_mul, hS, one_mul, sub_self]
  exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hc)

theorem gauss_mul_conj (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (h2 : (2 : k) ≠ 0) {B : Matrix ι ι k}
    (hB : B.IsSymm) (hdet : B.det ≠ 0) {t : k} (ht : t ≠ 0) :
    (∑ x, ψ (t * quadForm B x)) * conj (∑ x, ψ (t * quadForm B x)) =
      (Fintype.card k : ℂ) ^ Fintype.card ι := by
  classical
  have inner : ∀ z : ι → k, ∑ y : ι → k, ψ (t * (y ⬝ᵥ (B *ᵥ z))) =
      if z = 0 then (Fintype.card k : ℂ) ^ Fintype.card ι else 0 := by
    intro z
    split_ifs with hz
    · subst hz
      simp
    · have hw : t • (B *ᵥ z) ≠ 0 := by
        intro h
        have h' : B *ᵥ z = 0 := (smul_eq_zero.mp h).resolve_left ht
        exact hz (Matrix.eq_zero_of_mulVec_eq_zero hdet h')
      have := sum_char_dot ψ hψ hw
      simpa [dotProduct_smul, smul_eq_mul] using this
  have step : ∀ y : ι → k, ∑ x, ψ (t * quadForm B x) * conj (ψ (t * quadForm B y)) =
      ∑ z, ψ (t * quadForm B z) * ψ (t * (y ⬝ᵥ (B *ᵥ z))) := by
    intro y
    refine (Fintype.sum_equiv (Equiv.addLeft y) _ _ ?_).symm
    intro z
    rw [Equiv.coe_addLeft, ← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul,
      ← AddChar.map_add_eq_mul, quadForm_add h2 hB]
    congr 1
    ring
  rw [map_sum, Finset.sum_mul_sum, Finset.sum_comm]
  simp_rw [step]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, inner]
  simp [quadForm]

theorem norm_gauss (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (h2 : (2 : k) ≠ 0) {B : Matrix ι ι k}
    (hB : B.IsSymm) (hdet : B.det ≠ 0) {M : ℕ} (hM : Fintype.card ι = 2 * M) {t : k}
    (ht : t ≠ 0) : ‖∑ x, ψ (t * quadForm B x)‖ = (Fintype.card k : ℝ) ^ M := by
  have h := gauss_mul_conj ψ hψ h2 hB hdet ht
  rw [Complex.mul_conj', hM] at h
  have h' : ‖∑ x, ψ (t * quadForm B x)‖ ^ 2 = ((Fintype.card k : ℝ) ^ M) ^ 2 := by
    rw [← pow_mul, mul_comm M 2]
    exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h'

theorem count_mul_card (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (B : Matrix ι ι k) (s : k) :
    (Nat.card {x : ι → k // quadForm B x = s} : ℂ) * (Fintype.card k : ℂ) =
      ∑ t : k, ψ (-(t * s)) * ∑ x, ψ (t * quadForm B x) := by
  classical
  have hprim := AddChar.IsPrimitive.of_ne_one hψ
  have h1 : ∀ x : ι → k, ∑ t : k, ψ (t * (quadForm B x - s)) =
      if quadForm B x = s then (Fintype.card k : ℂ) else 0 := by
    intro x
    rw [AddChar.sum_mulShift _ hprim]
    simp [sub_eq_zero]
  have h2 : ∑ t : k, ψ (-(t * s)) * ∑ x, ψ (t * quadForm B x) =
      ∑ x : ι → k, ∑ t : k, ψ (t * (quadForm B x - s)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [h2]
  simp_rw [h1]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.sum_ite, Finset.sum_const,
    Finset.sum_const_zero, add_zero, nsmul_eq_mul]

theorem card_quadric_even (k : Type) [Field k] [Fintype k] (hchar : ringChar k ≠ 2)
    (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (hM : Fintype.card ι = 2 * M) (hM1 : 1 ≤ M)
    (B : Matrix ι ι k) (hB : B.IsSymm) (hdet : B.det ≠ 0) (s : k) :
    |(Nat.card {x : ι → k // (2 : k)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) = s} : ℝ) -
      (Fintype.card k : ℝ) ^ (2 * M - 1)| ≤ (Fintype.card k : ℝ) ^ M := by
  classical
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hchar
  obtain ⟨ψ, hψ⟩ : ∃ ψ : AddChar k ℂ, ψ 1 ≠ 1 :=
    AddChar.exists_apply_ne_zero.mpr one_ne_zero
  have hψ1 : ψ ≠ 1 := fun h => hψ (by simp [h])
  have hq : (0 : ℝ) < (Fintype.card k : ℝ) := by exact_mod_cast Fintype.card_pos
  set N : ℕ := Nat.card {x : ι → k // quadForm B x = s} with hNdef
  have hcount := count_mul_card ψ hψ1 B s
  rw [← hNdef, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : k))] at hcount
  have hzero : ψ (-((0 : k) * s)) * ∑ x, ψ ((0 : k) * quadForm B x) =
      (Fintype.card k : ℂ) ^ (2 * M) := by
    simp [hM]
  rw [hzero] at hcount
  have hbound : ‖∑ t ∈ Finset.univ.erase (0 : k), ψ (-(t * s)) * ∑ x, ψ (t * quadForm B x)‖ ≤
      ((Fintype.card k : ℝ) - 1) * (Fintype.card k : ℝ) ^ M := by
    have hterm : ∀ t ∈ Finset.univ.erase (0 : k),
        ‖ψ (-(t * s)) * ∑ x, ψ (t * quadForm B x)‖ ≤ (Fintype.card k : ℝ) ^ M := by
      intro t ht
      rw [norm_mul, AddChar.norm_apply, one_mul,
        norm_gauss ψ hψ1 h2 hB hdet hM (Finset.ne_of_mem_erase ht)]
    have := norm_sum_le_of_le _ hterm
    refine this.trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      nsmul_eq_mul, Nat.cast_sub Fintype.card_pos]
    simp
  have hreal : ((((N : ℝ) * (Fintype.card k : ℝ) - (Fintype.card k : ℝ) ^ (2 * M) : ℝ)) : ℂ) =
      ∑ t ∈ Finset.univ.erase (0 : k), ψ (-(t * s)) * ∑ x, ψ (t * quadForm B x) := by
    push_cast
    rw [hcount]
    ring
  have habs : |(N : ℝ) * (Fintype.card k : ℝ) - (Fintype.card k : ℝ) ^ (2 * M)| ≤
      ((Fintype.card k : ℝ) - 1) * (Fintype.card k : ℝ) ^ M := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, hreal]
    exact hbound
  have hpow : (Fintype.card k : ℝ) ^ (2 * M) =
      (Fintype.card k : ℝ) ^ (2 * M - 1) * (Fintype.card k : ℝ) := by
    rw [← pow_succ]
    congr 1
    omega
  have hfac : (N : ℝ) * (Fintype.card k : ℝ) - (Fintype.card k : ℝ) ^ (2 * M) =
      ((N : ℝ) - (Fintype.card k : ℝ) ^ (2 * M - 1)) * (Fintype.card k : ℝ) := by
    rw [hpow]
    ring
  rw [hfac, abs_mul, abs_of_pos hq] at habs
  have hqM : (0 : ℝ) ≤ (Fintype.card k : ℝ) ^ M := by positivity
  have hfin : |(N : ℝ) - (Fintype.card k : ℝ) ^ (2 * M - 1)| * (Fintype.card k : ℝ) ≤
      (Fintype.card k : ℝ) ^ M * (Fintype.card k : ℝ) := by
    nlinarith
  exact le_of_mul_le_mul_right hfin hq

theorem quadric_count_even : ∀ (k : Type) [Field k] [Fintype k], ringChar k ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ), Fintype.card ι = 2 * M → 1 ≤ M → ∀ (B : Matrix ι ι k), B.IsSymm → B.det ≠ 0 → ∀ s : k, |(Nat.card {x : ι → k // (2 : k)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) = s} : ℝ) - (Fintype.card k : ℝ) ^ (2 * M - 1)| ≤ (Fintype.card k : ℝ) ^ M :=
  fun k _ _ h ι _ _ M hM hM1 B hB hd s => card_quadric_even k h ι M hM hM1 B hB hd s

end GlobalTheory.CompanionTheory.SW.QuadricCount
