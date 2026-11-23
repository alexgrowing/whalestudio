import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.GsFramesOfIso
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.PGsWitt

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Matrix

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

section iso

variable {k r : ℕ}

lemma herm_X_gen {x w : Fin (2 * r + k + 1) → ℂ} (hx : x ∈ Xsp k r) (hw : ∀ i : Fin (2 * r + k + 1), r + k < i.val → w i = 0) :
    herm (Hpk k r) x w = 0 := by
  have hlo : ∀ j : Fin (2 * r + k + 1), r ≤ j.val → x j = 0 := by
    intro j hj
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      have hne : j ≠ eI k r a := by
        intro h
        have := congrArg Fin.val h
        simp [eI] at this
        omega
      simp [bvec, Pi.single_apply, hne]
    | zero => rfl
    | add y z _ _ hy hz => simp [hy, hz]
    | smul c y _ hy => simp [hy]
  unfold herm
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : r ≤ j.val
  · rw [hlo j hj, mul_zero, mul_zero]
  · push_neg at hj
    by_cases hi : r + k < i.val
    · rw [hw i hi, star_zero, zero_mul]
    · push_neg at hi
      have hH : Hpk k r i j = 0 := by
        unfold Hpk
        simp only [Fin.ext_iff]
        split_ifs <;> first | rfl | (exfalso; omega)
      rw [hH, zero_mul, mul_zero]

lemma herm_wb_X {x w : Fin (2 * r + k + 1) → ℂ} (hx : x ∈ Xsp k r) (hw : ∀ i : Fin (2 * r + k + 1), r + k < i.val → w i = 0) :
    herm (Hpk k r) w x = 0 := by
  have hlo : ∀ j : Fin (2 * r + k + 1), r ≤ j.val → x j = 0 := by
    intro j hj
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      have hne : j ≠ eI k r a := by
        intro h
        have := congrArg Fin.val h
        simp [eI] at this
        omega
      simp [bvec, Pi.single_apply, hne]
    | zero => rfl
    | add y z _ _ hy hz => simp [hy, hz]
    | smul c y _ hy => simp [hy]
  unfold herm
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  by_cases hi : r ≤ i.val
  · rw [hlo i hi, star_zero, zero_mul]
  · push_neg at hi
    by_cases hj : r + k < j.val
    · rw [hw j hj, mul_zero, mul_zero]
    · push_neg at hj
      have hH : Hpk k r i j = 0 := by
        unfold Hpk
        simp only [Fin.ext_iff]
        split_ifs <;> first | rfl | (exfalso; omega)
      rw [hH, zero_mul, mul_zero]

lemma X_hi {x : Fin (2 * r + k + 1) → ℂ} (hx : x ∈ Xsp k r) : ∀ i : Fin (2 * r + k + 1), r + k < i.val → x i = 0 := by
  intro i hi
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    have hne : i ≠ eI k r a := by
      intro h
      have := congrArg Fin.val h
      simp [eI] at this
      omega
    simp [bvec, Pi.single_apply, hne]
  | zero => rfl
  | add y z _ _ hy hz => simp [hy, hz]
  | smul c y _ hy => simp [hy]

lemma wb_hi {x : Fin (2 * r + k + 1) → ℂ} (hx : inWb k r x) : ∀ i : Fin (2 * r + k + 1), r + k < i.val → x i = 0 := by
  intro i hi
  exact hx i (Or.inr hi)

lemma fix_X {g : B.Mat k r} (hg : ∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a)) {x : Fin (2 * r + k + 1) → ℂ}
    (hx : x ∈ Xsp k r) : g *ᵥ x = x := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    exact hg a
  | zero => exact Matrix.mulVec_zero g
  | add y z _ _ hy hz => rw [Matrix.mulVec_add, hy, hz]
  | smul c y _ hy => rw [Matrix.mulVec_smul, hy]

lemma uw_eq {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) {nu : Fin (2 * r + k + 1) → ℂ} {U0 : Set (Fin (2 * r + k + 1) → ℂ)}
    (hnu : nu ∈ Wsp k r z) (hnu1 : herm (Hpk k r) nu nu = 1)
    (hU0 : ∀ u, u ∈ U0 ↔ u ∈ Wsp k r z ∧ herm (Hpk k r) u nu = 0)
    {h α : B.Mat k r} (hh : h ∈ UWset k r z) (hα : α ∈ UWset k r z)
    (hU : ∀ u ∈ U0, h *ᵥ u = α *ᵥ u) (hn : h *ᵥ nu = α *ᵥ nu) : h = α := by
  obtain ⟨hzW, hTz⟩ := hz
  have hzz : herm (Hpk k r) z z ≠ 0 := by
    intro h0
    unfold Formalism.QuantumDeterminants.Tz at hTz
    rw [h0] at hTz
    simp at hTz
  have hlin_sub : ∀ a b w, herm (Hpk k r) (a - b) w = herm (Hpk k r) a w - herm (Hpk k r) b w := by
    intro a b w
    simp [herm, Matrix.mulVec_sub, dotProduct_sub]
  have hlin_smul : ∀ (c : ℂ) a w, herm (Hpk k r) (c • a) w = c * herm (Hpk k r) a w := by
    intro c a w
    simp [herm, Matrix.mulVec_smul, dotProduct_smul]
  have hW : ∀ v, inWb k r v → h *ᵥ v = α *ᵥ v := by
    intro v hv
    obtain ⟨d, hd⟩ : ∃ d, d = herm (Hpk k r) v z / herm (Hpk k r) z z := ⟨_, rfl⟩
    have hv'W : inWb k r (v - d • z) := fun i hi => by simp [hv i hi, hzW i hi]
    have hv'z : herm (Hpk k r) (v - d • z) z = 0 := by
      rw [hlin_sub, hlin_smul, hd, div_mul_cancel₀ _ hzz, sub_self]
    obtain ⟨c, hc⟩ : ∃ c, c = herm (Hpk k r) (v - d • z) nu := ⟨_, rfl⟩
    have hu : (v - d • z) - c • nu ∈ U0 := by
      rw [hU0]
      refine ⟨⟨fun i hi => by simp [hv'W i hi, hnu.1 i hi], ?_⟩, ?_⟩
      · rw [hlin_sub, hlin_smul, hv'z, hnu.2, mul_zero, sub_zero]
      · rw [hlin_sub, hlin_smul, hnu1, mul_one, hc, sub_self]
    have hv_dec : v = ((v - d • z) - c • nu) + c • nu + d • z := by abel
    rw [hv_dec, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_add,
      Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, hU _ hu, hn, hh.2.2,
      hα.2.2]
  have hcol : ∀ j : Fin (2 * r + k + 1), h *ᵥ Pi.single j 1 = α *ᵥ Pi.single j 1 := by
    intro j
    by_cases hj1 : j.val < r
    · have e : (Pi.single j (1 : ℂ) : Fin (2 * r + k + 1) → ℂ) = bvec (eI k r ⟨j.val, hj1⟩) := by
        show Pi.single j 1 = Pi.single (eI k r ⟨j.val, hj1⟩) 1
        congr 1
      rw [e, (hh.2.1 _).1, (hα.2.1 _).1]
    · by_cases hj2 : r + k < j.val
      · have hlt := j.isLt
        have e : (Pi.single j (1 : ℂ) : Fin (2 * r + k + 1) → ℂ) =
            bvec (esI k r ⟨2 * r + k - j.val, by omega⟩) := by
          show Pi.single j 1 = Pi.single (esI k r ⟨2 * r + k - j.val, by omega⟩) 1
          congr 1
          exact Fin.ext (by simp only [esI]; omega)
        rw [e, (hh.2.1 _).2, (hα.2.1 _).2]
      · apply hW
        intro i hi
        have hne : i ≠ j := by
          intro hij
          subst hij
          omega
        simp [Pi.single_apply, hne]
  ext i j
  have h1 := congrFun (hcol j) i
  simpa [Matrix.mulVec_single_one] using h1

end iso

end PI.UnitaryGroupMassFormula.GsFr
