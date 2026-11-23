import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsPeriodMapDet
import Formalism.FormalDegreeBessel.FinalG

open Matrix MeasureTheory Finset Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.Mom.LowVec

variable {k r : ℕ}

abbrev flagSpan (k r : ℕ) (a : Fin (r + 1)) : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) :=
  Submodule.span ℂ (Set.range fun b : {b : Fin r // b.val < a.val} => bvec (eI k r b.1))

theorem mem_flagSpan {a : Fin (r + 1)} {y : Fin (2 * r + k + 1) → ℂ} :
    y ∈ flagSpan k r a ↔ ∀ i : Fin (2 * r + k + 1), a.val ≤ i.val → y i = 0 := by
  constructor
  · intro hy i hi
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      have := b.2
      exact Pi.single_eq_of_ne (fun e => by rw [e] at hi; simp only [eI] at hi; omega) _
    | zero => rfl
    | add x y _ _ hx hy => simp [hx, hy]
    | smul c x _ hx => simp [hx]
  · intro hy
    rw [← Finset.univ_sum_single y]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : a.val ≤ i.val
    · rw [hy i hi, Pi.single_zero]; exact Submodule.zero_mem _
    · have ha := a.isLt
      have : (Pi.single i (y i) : Fin (2 * r + k + 1) → ℂ) = y i • bvec (eI k r ⟨i.val, by omega⟩) := by
        rw [bvec, ← Pi.single_smul, smul_eq_mul, mul_one]; rfl
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨⟨i.val, by omega⟩, by simpa using hi⟩, rfl⟩)

theorem mulVec_sub {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {s : Mat k r} (hs : s ∈ Sset k r z)
    (a : Fin (r + 1)) {y : Fin (2 * r + k + 1) → ℂ} (hy : y ∈ flagSpan k r a) :
    ∃ y' ∈ flagSpan k r a, s *ᵥ (fvec k r z a - y) = fvec k r z a - y' := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  have hc := ((WeylGroupFacts.nset_iff m).1 hm).2
  have ha := a.isLt
  have h1 : fvec k r z a - m *ᵥ (fvec k r z a - y) ∈ flagSpan k r a := by
    refine mem_flagSpan.2 fun i hi => ?_
    have : (m *ᵥ (fvec k r z a - y)) i = ((1 : Mat k r) *ᵥ (fvec k r z a - y)) i := by
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : j.val ≤ r + k ∧ (j.val ≤ i.val ∨ r ≤ i.val)
      · rw [hc i j hj.1 hj.2, Matrix.one_apply]
      · have e1 : y j = 0 := mem_flagSpan.1 hy j (by omega)
        have e2 : fvec k r z a j = 0 := by
          unfold fvec
          split_ifs with h'
          · exact Pi.single_eq_of_ne (fun e => by rw [e] at hj; simp only [eI] at hj; omega) _
          · exact hz j (by omega)
        simp [e1, e2]
    rw [Pi.sub_apply, this, Matrix.one_mulVec, Pi.sub_apply, mem_flagSpan.1 hy i hi]; ring
  have h2 : ∀ x ∈ flagSpan k r a, h *ᵥ x = x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨b, rfl⟩ := hx; exact (hh.2.1 b.1).1
    | zero => exact Matrix.mulVec_zero _
    | add x y _ _ hx hy => rw [Matrix.mulVec_add, hx, hy]
    | smul c x _ hx => rw [Matrix.mulVec_smul, hx]
  have h3 : h *ᵥ fvec k r z a = fvec k r z a := by
    unfold fvec
    split_ifs with h'
    · exact (hh.2.1 _).1
    · exact hh.2.2
  refine ⟨_, h1, ?_⟩
  rw [← Matrix.mulVec_mulVec]
  have := h2 _ h1
  rw [Matrix.mulVec_sub, h3] at this
  rw [sub_sub_cancel]
  exact sub_right_injective this

theorem lA_left {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {s : Mat k r} (hs : s ∈ Sset k r z) (g : Mat k r)
    (a : Fin (r + 1)) : lA k r z (s * g) a = lA k r z g a := by
  have hH : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1
  have hu : IsUnit s.det := by
    obtain ⟨h, hh, m, hm, rfl⟩ := hs
    rw [Matrix.det_mul]
    exact ((uHGroup _ _ hH).2.2 h hh.1).1.mul ((uHGroup _ _ hH).2.2 m hm.1).1
  unfold lA
  congr 1
  ext t
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨y', hy', e⟩ := mulVec_sub hz ((sGroup k r z hz).2.2 s hs) a hy
    exact ⟨y', hy', by rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, e]⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨y', hy', e⟩ := mulVec_sub hz hs a hy
    refine ⟨y', hy', ?_⟩
    rw [← e, Matrix.mulVec_mulVec, Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

theorem eucl_unitary {N : ℕ} {t : Matrix (Fin N) (Fin N) ℂ} (ht : t ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (v : Fin N → ℂ) : eucl (t *ᵥ v) = eucl v := by
  have e : ∀ v : Fin N → ℂ, ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) = star v ⬝ᵥ v := fun v => by
    simp [dotProduct, Complex.normSq_eq_conj_mul_self]
  have h1 : tᴴ * t = 1 := Matrix.mem_unitaryGroup_iff'.1 ht
  unfold eucl
  congr 1
  apply Complex.ofReal_injective
  rw [e, e, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, h1, Matrix.vecMul_one]

theorem lA_right (z : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) {t : Mat k r}
    (ht : t ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ) (a : Fin (r + 1)) :
    lA k r z (g * t) a = lA k r z g a := by
  have h1 : t⁻¹ ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := by
    rw [Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 ht)]
    exact Unitary.star_mem ht
  unfold lA
  simp only [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, eucl_unitary h1]

theorem measurable_lA (z : Fin (2 * r + k + 1) → ℂ) (a : Fin (r + 1)) :
    Measurable fun x : Mt k r => lA k r z (Matrix.of x) a := by
  refine measurable_of_Iio fun t => ?_
  have ho : IsOpen {x : Mt k r | ∃ y ∈ flagSpan k r a, eucl (Matrix.of x *ᵥ (fvec k r z a - y)) < t} := by
    simp only [Set.ofPred_exists, Set.ofPred_and]
    refine isOpen_iUnion fun y => IsOpen.inter isOpen_const (isOpen_lt ?_ continuous_const)
    simp only [eucl, Matrix.mulVec, dotProduct, Matrix.of_apply]
    fun_prop
  have hi : Measurable fun x : Mt k r => (fun i j => (Matrix.of x)⁻¹ i j : Mt k r) := by
    have h1 : Continuous fun x : Mt k r => (Matrix.of x).det := Continuous.matrix_det continuous_id
    have h2 : Continuous fun x : Mt k r => (Matrix.of x).adjugate := Continuous.matrix_adjugate continuous_id
    refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
    simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
    exact h1.measurable.inv.mul (h2.matrix_elem i j).measurable
  convert hi ho.measurableSet using 1
  ext x
  simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_ofPred_eq, lA]
  refine (csInf_lt_iff ?_ ?_).trans ⟨?_, ?_⟩
  · exact ⟨0, by rintro _ ⟨y, -, rfl⟩; exact Real.sqrt_nonneg _⟩
  · exact Set.nonempty_of_mem (x := eucl ((Matrix.of x)⁻¹ *ᵥ (fvec k r z a - 0))) ⟨0, Submodule.zero_mem _, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, h⟩; exact ⟨y, hy, h⟩
  · rintro ⟨y, hy, h⟩; exact ⟨_, ⟨y, hy, rfl⟩, h⟩

theorem exists_filt_zero (hA : LowAny) (hK : LowestK) {P : Mat k r} {A : HRep k r} {μ : Fin (2 * r + k + 1) → ℝ}
    {F : Flag k r} {κ : ℝ} (hP : IsCayleyU k r (sgnCN k r) P) (hμ : IsHCParam μ) (hD : A.IsDSAt P μ) (hF : F.Ok κ)
    {B : A.H → F.W} (hB : F.Iso A B) {w : A.H} (hw : w ∈ A.iso P (lowK (sgnCN k r) μ)) :
    ∃ w₀ ∈ A.filt P μ 0, ‖w₀‖ₑ = ‖w‖ₑ ∧ ∀ Φ : (Fin (r + 1) → ℝ) → ℝ, Measurable Φ →
      A.mass F.ν B (fun g => Φ (lA k r F.z g)) w = A.mass F.ν B (fun g => Φ (lA k r F.z g)) w₀ := by
  obtain ⟨v, hv, hv0, hvw⟩ := (hK k r P A μ hP hμ hD).1.2.2.2.1
  have hf : v ∈ A.filt P μ 0 := Submodule.subset_span ⟨_, _, by simp [dist1], by simp [dist1], hv, hvw⟩
  have hn : ‖w‖ = ‖((‖w‖ / ‖v‖ : ℝ) : ℂ) • v‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity), div_mul_cancel₀ _ (norm_ne_zero_iff.2 hv0)]
  refine ⟨((‖w‖ / ‖v‖ : ℝ) : ℂ) • v, Submodule.smul_mem _ _ hf, ?_, fun Φ hΦ => ?_⟩
  · rw [← ofReal_norm, ← ofReal_norm, ← hn]
  · refine hA k r P A μ F κ hP hμ hD hF B hB _ (hΦ.comp (measurable_pi_lambda _ (measurable_lA F.z))) ?_ ?_ w hw _
      (Submodule.smul_mem _ _ hv) hn
    · intro g _ s hs
      exact congrArg Φ (funext (lA_left hF.1 hs g))
    · intro g _ t _ ht
      exact congrArg Φ (funext (lA_right F.z g ht))

theorem isHCParam_of_setup {c Ch bv h q : ℝ} {P : Mat k r} {lam μ : Fin (2 * r + k + 1) → ℝ}
    {R : (Fin (2 * r + k + 1) → ℝ) → HRep k r} (hS : Setup k r c Ch P lam bv h q R) (hμ : InPP lam q μ) :
    IsHCParam μ := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · linarith [hμ.gap hab.ne, hS.2.2.1.le_gap hS.2.1 hab, hS.2.1.1.1 hab]
  · obtain ⟨m, hm⟩ := hμ.1 a
    obtain ⟨m', hm'⟩ := hS.2.1.1.2 a
    exact ⟨m + m', by rw [Int.cast_add]; linarith⟩

theorem momentLow : LowAny → MomentCor → LowestK → MomentLow := by
  intro hA hC hK c hc
  obtain ⟨Ch, hCh, H⟩ := hC c hc
  refine ⟨Ch, hCh, fun k r P lam bv h q₀ b R hS F κ hF hZ hT q μ B hB w hw => ⟨fun h1 h2 => ?_, fun l hl h1 h2 => ?_⟩⟩
  · have h0 : InPP lam q₀ μ := h1.mono (sub_le_self _ (Nat.cast_nonneg _))
    obtain ⟨w₀, hw₀, hn, hm⟩ := exists_filt_zero hA hK hS.1 (isHCParam_of_setup hS h0) (hS.2.2.2.2 μ h0) hF hB hw
    have h3 := (H k r P lam bv h q₀ b R hS F κ hF hZ hT 0 q μ B hB w₀ hw₀).1 h1 (by rwa [zero_add])
    rw [MomAll, hn] at h3
    refine ⟨fun a => ⟨?_, ?_⟩, fun t ht => ?_⟩
    · exact (hm (fun x => x a ^ (2 * q)) (by fun_prop)).trans_le (h3.1 a).1
    · exact (hm (fun x => (x a)⁻¹ ^ (2 * q)) (by fun_prop)).trans_le (h3.1 a).2
    · refine (hm (Set.indicator {x | ∃ a, t * H1 k r (Tz k r F.z) κ b 4 bv ≤ max (x a) (x a)⁻¹} 1)
        (measurable_one.indicator ?_)).trans_le (h3.2 t ht)
      rw [Set.ofPred_exists]
      exact MeasurableSet.iUnion fun a => measurableSet_le measurable_const (by fun_prop)
  · have h0 : InPP lam q₀ μ := h1.mono (sub_le_self _ (Nat.cast_nonneg _))
    obtain ⟨w₀, hw₀, hn, hm⟩ := exists_filt_zero hA hK hS.1 (isHCParam_of_setup hS h0) (hS.2.2.2.2 μ h0) hF hB hw
    have h3 := (H k r P lam bv h q₀ b R hS F κ hF hZ hT 0 q μ B hB w₀ hw₀).2 l hl h1 (by rwa [zero_add])
    rw [MomProd, hn] at h3
    exact (hm (fun x => (∏ a : Fin l, x (Fin.castLE hl a)) ^ (2 * q)) (by fun_prop)).trans_le h3

end GlobalTheory.Mom.LowVec
