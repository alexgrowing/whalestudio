import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.OfFnProdSmul
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.CauchyBinet

open Matrix Finset

noncomputable section

namespace AAInvW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3

theorem eI_inj (k r : ℕ) : Function.Injective (eI k r) := by
  unfold eI
  intro a b h
  have h1 := congrArg Fin.val h
  simp only at h1
  exact Fin.ext h1

theorem esI_inj (k r : ℕ) : Function.Injective (esI k r) := by
  unfold esI
  intro a b h
  have h1 := congrArg Fin.val h
  simp only at h1
  have ha := a.isLt
  have hb := b.isLt
  exact Fin.ext (by omega)

theorem keyS_inj (k r : ℕ) : Function.Injective (keyS k r) := by
  unfold keyS
  intro p q h
  simp only at h
  have hp := p.isLt
  have hq := q.isLt
  split_ifs at h <;> exact Fin.ext (by omega)

theorem strictMono_val_iff {m N : ℕ} (C : Fin m → Fin N) :
    StrictMono (fun l => (C l).val) ↔ StrictMono C :=
  ⟨fun h _ _ hab => h hab, fun h _ _ hab => h hab⟩

theorem not_inj {α β : Type*} {c : α → β} (hc : ¬ Function.Injective c) :
    ∃ p q, p ≠ q ∧ c p = c q := by
  simp only [Function.Injective, not_forall] at hc
  obtain ⟨p, q, h, hne⟩ := hc
  exact ⟨p, q, hne, h⟩

theorem det_transpose_apply {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) :
    M.det = ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M i (σ i) := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  simp [Units.smul_def, zsmul_eq_mul, Matrix.transpose_apply]

theorem algebra_aa : AlgAA := by
  intro A _ _ k r m hm E P Q xi u hE hQP hP
  classical
  have hrow : ∀ D : Fin m → Fin (2 * r + k + 1),
      qminor (fun i j => ∑ c, ∑ d, (P c i * Q j d) • E c d) (xR k r m hm) D u =
        ∑ d : Fin m → Fin (2 * r + k + 1), (∏ j, Q (D j) (d j)) • qminor E (xR k r m hm) d u := by
    intro D
    rw [q_expansion A _ m E P Q _ D u hQP]
    simp only [mul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [show (∑ c : Fin m → Fin (2 * r + k + 1), (∏ j, P (c j) (xR k r m hm j)) • (∏ j, Q (D j) (d j)) •
        qminor E c d u) = ∑ c : Fin m → Fin (2 * r + k + 1), (∏ j, Q (D j) (d j)) •
        (∏ j, P (c j) (xR k r m hm j)) • qminor E c d u from
      Finset.sum_congr rfl (fun c _ => smul_comm _ _ _)]
    rw [← Finset.smul_sum]
    congr 1
    exact collapse hm (eI k r) (eI_inj k r) P hP (fun c => qminor E c d u)
      (fun c hc => by
        obtain ⟨p, q, hpq, h⟩ := not_inj hc
        exact quantumMinor_eq_zero_of_row_eq quantumMinorRowSkew_holds E c d u p q hpq h)
  simp only [hrow]
  have h1 : ∀ D : Fin m → Fin (2 * r + k + 1),
      (if StrictMono D then (Matrix.of fun a l : Fin m => xi a (D l)).det •
        ∑ d : Fin m → Fin (2 * r + k + 1), (∏ j, Q (D j) (d j)) • qminor E (xR k r m hm) d u else 0) =
      ∑ d : Fin m → Fin (2 * r + k + 1), (if StrictMono D then
        (Matrix.of fun a l : Fin m => xi a (D l)).det * ∏ j, Q (D j) (d j) else 0) •
          qminor E (xR k r m hm) d u := by
    intro D
    split_ifs
    · rw [Finset.smul_sum]; simp only [smul_smul]
    · simp
  simp only [h1]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  rw [grouping (fun i => i.val) Fin.val_injective (fun d => qminor E (xR k r m hm) d u)
    (fun d τ => quantumMinorColSkew_holds A _ m E hE (xR k r m hm) d τ u)
    (fun d hd => by
      obtain ⟨p, q, hpq, h⟩ := not_inj hd
      exact quantumMinor_eq_zero_of_col_eq quantumMinorColSkew_holds E hE (xR k r m hm) d u p q hpq h)]
  refine Finset.sum_congr rfl (fun C _ => ?_)
  simp only [strictMono_val_iff]
  split_ifs with hC
  · congr 1
    have hM : (Matrix.of fun a l : Fin m => ∑ d, Q d (C l) * xi a d) =
        (Matrix.of fun a d => xi a d) * (Matrix.of fun d l => Q d (C l)) := by
      ext a l; simp [Matrix.mul_apply, mul_comm]
    rw [hM, cauchyBinet (fun i => i.val) Fin.val_injective]
    simp only [strictMono_val_iff, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun D _ => ?_)
    split_ifs with hD
    · simp only [Matrix.of_apply]
      rw [det_transpose_apply (Matrix.of fun i l => Q (D i) (C l)), Finset.mul_sum]
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      simp only [Matrix.of_apply, Function.comp_apply]
      ring
    · simp
  · rfl

theorem algebra_aa_vector : AlgAAv := by
  intro A _ _ k r m hm E P Q eta v hE hQP hQ
  classical
  have hcol : ∀ B : Fin m → Fin (2 * r + k + 1),
      qminor (fun i j => ∑ c, ∑ d, (P c i * Q j d) • E c d) B (sR k r m hm) v =
        ∑ c : Fin m → Fin (2 * r + k + 1), (∏ j, P (c j) (B j)) • qminor E c (sR k r m hm) v := by
    intro B
    rw [q_expansion A _ m E P Q B _ v hQP]
    simp only [mul_smul]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [← Finset.smul_sum]
    congr 1
    exact collapse hm (esI k r) (esI_inj k r) (fun i j => Q j i) hQ (fun d => qminor E c d v)
      (fun d hd => by
        obtain ⟨p, q, hpq, h⟩ := not_inj hd
        exact quantumMinor_eq_zero_of_col_eq quantumMinorColSkew_holds E hE c d v p q hpq h)
  simp only [hcol]
  have h1 : ∀ B : Fin m → Fin (2 * r + k + 1),
      (if StrictMono (fun l => keyS k r (B l)) then (Matrix.of fun a l : Fin m => eta a (B l)).det •
        ∑ c : Fin m → Fin (2 * r + k + 1), (∏ j, P (c j) (B j)) • qminor E c (sR k r m hm) v else 0) =
      ∑ c : Fin m → Fin (2 * r + k + 1), (if StrictMono (fun l => keyS k r (B l)) then
        (Matrix.of fun a l : Fin m => eta a (B l)).det * ∏ j, P (c j) (B j) else 0) •
          qminor E c (sR k r m hm) v := by
    intro B
    split_ifs
    · rw [Finset.smul_sum]; simp only [smul_smul]
    · simp
  simp only [h1]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  rw [grouping (keyS k r) (keyS_inj k r) (fun c => qminor E c (sR k r m hm) v)
    (fun c τ => quantumMinorRowSkew_holds A _ m E c (sR k r m hm) τ v)
    (fun c hc => by
      obtain ⟨p, q, hpq, h⟩ := not_inj hc
      exact quantumMinor_eq_zero_of_row_eq quantumMinorRowSkew_holds E c (sR k r m hm) v p q hpq h)]
  refine Finset.sum_congr rfl (fun C _ => ?_)
  split_ifs with hC
  · congr 1
    have hM : (Matrix.of fun a l : Fin m => ∑ d, P (C l) d * eta a d) =
        (Matrix.of fun a d => eta a d) * (Matrix.of fun d l => P (C l) d) := by
      ext a l; simp [Matrix.mul_apply, mul_comm]
    rw [hM, cauchyBinet (keyS k r) (keyS_inj k r)]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun B _ => ?_)
    split_ifs with hB
    · simp only [Matrix.of_apply]
      rw [det_transpose_apply (Matrix.of fun i l => P (C l) (B i)), Finset.mul_sum]
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      simp only [Matrix.of_apply, Function.comp_apply]
      ring
    · simp
  · rfl

end AAInvW
