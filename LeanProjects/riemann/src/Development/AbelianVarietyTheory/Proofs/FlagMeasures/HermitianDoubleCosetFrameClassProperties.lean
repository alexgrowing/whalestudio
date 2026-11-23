import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FrameClass

theorem exists_inv {E : Type} [CommRing E] {σ : Type} [SetLike σ E] [SubringClass σ E] (O : σ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) E) (hO : ∀ i j, A i j ∈ O) (ht : ∀ i j, j < i → A i j = 0)
    (hd : ∀ i, A i i = 1) :
    ∃ B : Matrix (Fin n) (Fin n) E, (∀ i j, B i j ∈ O) ∧ (∀ i j, j < i → B i j = 0) ∧ (∀ i, B i i = 1) ∧
      A * B = 1 ∧ B * A = 1 := by
  let M : Matrix (Fin n) (Fin n) O := fun i j => ⟨A i j, hO i j⟩
  have hM : M.BlockTriangular id := fun i j h => Subtype.ext (ht i j h)
  have hMd : ∀ i, M i i = 1 := fun i => Subtype.ext (hd i)
  have hdet : M.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hM]; simp [hMd]
  have hu : IsUnit M.det := by rw [hdet]; exact isUnit_one
  let _ : Invertible M := Matrix.invertibleOfIsUnitDet M hu
  have hI : (M⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hM
  have h1 : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hu
  have h2 : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hu
  have hA : M.map (SubringClass.subtype O) = A := rfl
  refine ⟨(M⁻¹).map (SubringClass.subtype O), fun i j => (M⁻¹ i j).2, fun i j h => ?_, fun i => ?_, ?_, ?_⟩
  · have : M⁻¹ i j = 0 := hI h
    simp [Matrix.map_apply, this]
  · have h := congrFun (congrFun h1 i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i, hMd, one_mul] at h
    · simp [Matrix.map_apply, h]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with hk | hk
      · have : M i k = 0 := hM hk
        rw [this, zero_mul]
      · have : M⁻¹ k i = 0 := hI hk
        rw [this, mul_zero]
    · simp
  · rw [← hA, ← Matrix.map_mul, h1]; simp
  · rw [← hA, ← Matrix.map_mul, h2]; simp

theorem sum_comp {E V : Type} [CommRing E] [AddCommGroup V] [Module E V] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) E) (g p q : Fin n → V) (hp : ∀ j, p j = ∑ i, A i j • g i)
    (hq : ∀ j, q j = ∑ i, B i j • p i) (j : Fin n) : q j = ∑ i, (A * B) i j • g i := by
  rw [hq]
  simp only [hp, Finset.smul_sum, Matrix.mul_apply, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem th_ne_zero : S.th ≠ 0 := by
  unfold Frames.th
  split_ifs
  · intro h
    exact S.ϖ_irr.ne_zero (Subtype.ext h)
  · exact one_ne_zero

theorem intM_mul {n : ℕ} {A B : Matrix (Fin n) (Fin n) E} (hA : IsIntM L A) (hB : IsIntM L B) :
    IsIntM L (A * B) := fun i j => by
  rw [Matrix.mul_apply]
  exact sum_mem fun l _ => mul_mem (hA i l) (hB l j)

theorem cong_iff {n : ℕ} (t : E) (A A' : Matrix (Fin n) (Fin n) E) :
    (∀ i j, ∃ c ∈ L.O, A' i j - A i j = t * c) ↔ ∃ C, IsIntM L C ∧ A' - A = t • C := by
  constructor
  · intro h
    choose C hC hC' using h
    exact ⟨C, hC, by ext i j; exact hC' i j⟩
  · rintro ⟨C, hC, h⟩ i j
    exact ⟨C i j, hC i j, congrFun (congrFun h i) j⟩

theorem refl_mem (g g' : Fin (r + 1) → S.V) : (g, g') ∈ S.frameCls g g' := by
  have h1 : IsIntM L (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) := fun i j => by
    rw [Matrix.one_apply]; split_ifs
    exacts [one_mem _, zero_mem _]
  refine ⟨1, 1, h1, h1, fun i j h => ?_, fun i => by simp, fun i j => ⟨0, zero_mem _, by simp⟩, fun j => ?_,
    fun j => ?_⟩
  · simp [Matrix.one_apply_ne h.ne']
  · simp [Matrix.one_apply]
  · simp [Matrix.one_apply]

omit [TopologicalSpace E] in
theorem tri_mul {n : ℕ} {A B : Matrix (Fin n) (Fin n) E} (hA : ∀ i j, j < i → A i j = 0)
    (hB : ∀ i j, j < i → B i j = 0) : ∀ i j, j < i → (A * B) i j = 0 := fun i j h => by
  have hA' : A.BlockTriangular id := fun i j h => hA i j h
  have hB' : B.BlockTriangular id := fun i j h => hB i j h
  exact hA'.mul hB' h

omit [TopologicalSpace E] in
theorem diag_mul {n : ℕ} {A B : Matrix (Fin n) (Fin n) E} (hA : ∀ i j, j < i → A i j = 0)
    (hB : ∀ i j, j < i → B i j = 0) (i : Fin n) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro l _ hl
    rcases lt_or_gt_of_ne hl with hl | hl
    · rw [hA i l hl, zero_mul]
    · rw [hB l i hl, mul_zero]
  · simp

theorem trans_mem {g g' : Fin (r + 1) → S.V} {p q : S.FrP} (hp : p ∈ S.frameCls g g')
    (hq : q ∈ S.frameCls p.1 p.2) : q ∈ S.frameCls g g' := by
  obtain ⟨A, A', hA, hA', ht, hd, hc, h1, h2⟩ := hp
  obtain ⟨B, B', hB, hB', kt, kd, kc, k1, k2⟩ := hq
  obtain ⟨C, hC, hc⟩ := (cong_iff _ _ _).1 hc
  obtain ⟨D, hD, kc⟩ := (cong_iff _ _ _).1 kc
  refine ⟨A * B, A' * B', intM_mul hA hB, intM_mul hA' hB', fun i j h => ⟨?_, ?_⟩, fun i => ⟨?_, ?_⟩, ?_,
    sum_comp A B g p.1 q.1 h1 k1, sum_comp A' B' g' p.2 q.2 h2 k2⟩
  · exact tri_mul (fun i j h => (ht i j h).1) (fun i j h => (kt i j h).1) i j h
  · exact tri_mul (fun i j h => (ht i j h).2) (fun i j h => (kt i j h).2) i j h
  · rw [diag_mul (fun i j h => (ht i j h).1) (fun i j h => (kt i j h).1), (hd i).1, (kd i).1, one_mul]
  · rw [diag_mul (fun i j h => (ht i j h).2) (fun i j h => (kt i j h).2), (hd i).2, (kd i).2, one_mul]
  · refine (cong_iff _ _ _).2 ⟨C * B' + A * D, fun i j => ?_, ?_⟩
    · exact add_mem (intM_mul hC hB' i j) (intM_mul hA hD i j)
    · rw [smul_add, ← Matrix.smul_mul, ← Matrix.mul_smul, ← hc, ← kc, sub_mul, mul_sub]; abel

theorem symm_mem {g g' : Fin (r + 1) → S.V} {p : S.FrP} (hp : p ∈ S.frameCls g g') :
    (g, g') ∈ S.frameCls p.1 p.2 := by
  obtain ⟨A, A', hA, hA', ht, hd, hc, h1, h2⟩ := hp
  obtain ⟨C, hC, hc⟩ := (cong_iff _ _ _).1 hc
  obtain ⟨B, hB, bt, bd, hAB, hBA⟩ := exists_inv L.O A hA (fun i j h => (ht i j h).1) (fun i => (hd i).1)
  obtain ⟨B', hB', bt', bd', hAB', hBA'⟩ :=
    exists_inv L.O A' hA' (fun i j h => (ht i j h).2) (fun i => (hd i).2)
  refine ⟨B, B', hB, hB', fun i j h => ⟨bt i j h, bt' i j h⟩, fun i => ⟨bd i, bd' i⟩, ?_, fun j => ?_,
    fun j => ?_⟩
  · refine (cong_iff _ _ _).2 ⟨-(B' * C * B), fun i j => ?_, ?_⟩
    · exact neg_mem (intM_mul (intM_mul hB' hC) hB i j)
    · rw [smul_neg, ← Matrix.smul_mul, ← Matrix.mul_smul, ← hc, mul_sub, sub_mul, hBA', mul_assoc, hAB]
      simp
  · have := sum_comp A B g p.1 (fun j => ∑ i, B i j • p.1 i) h1 (fun _ => rfl) j
    rw [this, hAB]; simp [Matrix.one_apply]
  · have := sum_comp A' B' g' p.2 (fun j => ∑ i, B' i j • p.2 i) h2 (fun _ => rfl) j
    rw [this, hAB']; simp [Matrix.one_apply]

theorem Mof_le {g g' : Fin (r + 1) → S.V} {p : S.FrP} (hp : p ∈ S.frameCls g g') :
    S.Mof p.1 p.2 ≤ S.Mof g g' := by
  obtain ⟨A, A', hA, hA', ht, hd, hc, h1, h2⟩ := hp
  have hsm : ∀ c ∈ L.O, ∀ v ∈ S.Mof g g', c • v ∈ S.Mof g g' := fun c hc v hv =>
    (S.Mof g g').smul_mem ⟨c, hc⟩ hv
  have hg : ∀ i, g i ∈ S.Mof g g' := fun i => Submodule.subset_span (Or.inl ⟨i, rfl⟩)
  have hg' : ∀ i, algebraMap F E S.th⁻¹ • (g' i - g i) ∈ S.Mof g g' := fun i =>
    Submodule.subset_span (Or.inr ⟨i, rfl⟩)
  have hth : algebraMap F E S.th⁻¹ * algebraMap F E S.th = 1 := by
    rw [← map_mul, inv_mul_cancel₀ (th_ne_zero S), map_one]
  choose C hC hC' using hc
  refine Submodule.span_le.2 ?_
  rintro _ (⟨j, rfl⟩ | ⟨j, rfl⟩)
  · rw [h1]
    exact sum_mem fun i _ => hsm _ (hA i j) _ (hg i)
  · have : algebraMap F E S.th⁻¹ • (p.2 j - p.1 j) =
        ∑ i, (A' i j • (algebraMap F E S.th⁻¹ • (g' i - g i)) + C i j • g i) := by
      rw [h1, h2, ← Finset.sum_sub_distrib, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hCi : C i j = algebraMap F E S.th⁻¹ * (A' i j - A i j) := by
        rw [hC', ← mul_assoc, hth, one_mul]
      rw [hCi]; module
    show algebraMap F E S.th⁻¹ • (p.2 j - p.1 j) ∈ S.Mof g g'
    rw [this]
    exact sum_mem fun i _ => add_mem (hsm _ (hA' i j) _ (hg' i)) (hsm _ (hC i j) _ (hg i))

theorem smul_mem (h : S.GLV) {g g' : Fin (r + 1) → S.V} {p : S.FrP} (hp : p ∈ S.frameCls g g') :
    h • p ∈ S.frameCls (fun b => h (g b)) (fun b => h (g' b)) := by
  obtain ⟨A, A', hA, hA', ht, hd, hc, h1, h2⟩ := hp
  refine ⟨A, A', hA, hA', ht, hd, hc, fun j => ?_, fun j => ?_⟩
  · show h (p.1 j) = _
    rw [h1]; simp
  · show h (p.2 j) = _
    rw [h2]; simp

theorem smul_cls (h : S.GLV) (g g' : Fin (r + 1) → S.V) :
    h • S.frameCls g g' = S.frameCls (fun b => h (g b)) (fun b => h (g' b)) := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact smul_mem S h hq
  · intro hp
    have := smul_mem S h⁻¹ hp
    refine ⟨h⁻¹ • p, ?_, smul_inv_smul h p⟩
    have e : ∀ v : S.V, h⁻¹ (h v) = v := fun v => h.symm_apply_apply v
    simpa only [e] using this

theorem frame_classes : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ g g' : Fin (r + 1) → S.V, (g, g') ∈ S.frameCls g g' ∧ (∀ p ∈ S.frameCls g g', S.frameCls p.1 p.2 = S.frameCls g g' ∧ S.Mof p.1 p.2 = S.Mof g g') ∧ ∀ h : S.GLV, h • S.frameCls g g' = S.frameCls (fun b => h (g b)) (fun b => h (g' b)) := by
  intro F _ _ _ _ _ E _ _ _ L r k S g g'
  refine ⟨refl_mem S g g', fun p hp => ⟨?_, ?_⟩, fun h => smul_cls S h g g'⟩
  · ext q
    exact ⟨fun hq => trans_mem S hp hq, fun hq => trans_mem S (symm_mem S hp) hq⟩
  · exact le_antisymm (Mof_le S hp) (Mof_le S (p := (g, g')) (symm_mem S hp))

end GlobalTheory.HL.FrameClass
