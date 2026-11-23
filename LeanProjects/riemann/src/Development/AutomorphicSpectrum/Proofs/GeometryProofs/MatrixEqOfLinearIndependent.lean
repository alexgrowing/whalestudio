import Mathlib

namespace GlobalTheory.CompanionTheory.Ggeo.FrameDet

open scoped BigOperators

private theorem det_mem_of_forall_mem' {Ω : Type} [CommRing Ω] (R : Subring Ω) {n : ℕ}
    (P : Matrix (Fin n) (Fin n) Ω) (hP : ∀ i j, P i j ∈ R) : P.det ∈ R := by
  have h : P = R.subtype.mapMatrix (Matrix.of fun i j => (⟨P i j, hP i j⟩ : R)) := by
    ext i j
    rfl
  rw [h, ← RingHom.map_det]
  exact (Matrix.det (Matrix.of fun i j => (⟨P i j, hP i j⟩ : R))).2

theorem matrix_eq_of_linearIndependent {Ω M : Type} [Field Ω] [AddCommGroup M] [Module Ω M]
    {n : ℕ} {w : Fin n → M} (hw : LinearIndependent Ω w)
    {C D : Matrix (Fin n) (Fin n) Ω}
    (h : ∀ i, ∑ j, C i j • w j = ∑ j, D i j • w j) : C = D := by
  ext i j
  have h' : ∑ k, (C i k - D i k) • w k = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, h i, sub_self]
  exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hw (fun k => C i k - D i k) h' j)

theorem sum_smul_sum_smul {Ω M : Type} [Field Ω] [AddCommGroup M] [Module Ω M]
    {n : ℕ} (w : Fin n → M) (C D : Matrix (Fin n) (Fin n) Ω) (i : Fin n) :
    ∑ j, C i j • ∑ k, D j k • w k = ∑ k, (C * D) i k • w k := by
  simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  exact Finset.sum_comm

theorem det_eq_unit_mul : ∀ (Ω M : Type) [Field Ω] [AddCommGroup M] [Module Ω M] (R : Subring Ω) (n : ℕ) (u : Fin n → M) (A B : Matrix (Fin n) (Fin n) Ω), LinearIndependent Ω u → LinearIndependent Ω (fun i => ∑ j, A i j • u j) → LinearIndependent Ω (fun i => ∑ j, B i j • u j) → Submodule.span R (Set.range fun i => ∑ j, A i j • u j) = Submodule.span R (Set.range fun i => ∑ j, B i j • u j) → ∃ c : Ω, c ∈ R ∧ c⁻¹ ∈ R ∧ c ≠ 0 ∧ B.det = c * A.det := by
  intro Ω M _ _ _ R n u A B hu ha _ hspan
  have key : ∀ a b : Fin n → M, Submodule.span R (Set.range b) ≤ Submodule.span R (Set.range a) →
      ∃ P : Matrix (Fin n) (Fin n) Ω, (∀ i j, P i j ∈ R) ∧ ∀ i, b i = ∑ j, P i j • a j := by
    intro a b hle
    have hex : ∀ i, ∃ c : Fin n → R, ∑ j, c j • a j = b i := fun i =>
      (Submodule.mem_span_range_iff_exists_fun R).mp (hle (Submodule.subset_span ⟨i, rfl⟩))
    choose c hc using hex
    refine ⟨Matrix.of fun i j => (c i j : Ω), fun i j => (c i j).2, fun i => ?_⟩
    rw [← hc i]
    exact Finset.sum_congr rfl fun j _ => Subring.smul_def _ _
  obtain ⟨P, hPR, hP⟩ := key (fun i => ∑ j, A i j • u j) (fun i => ∑ j, B i j • u j) hspan.ge
  obtain ⟨Q, hQR, hQ⟩ := key (fun i => ∑ j, B i j • u j) (fun i => ∑ j, A i j • u j) hspan.le
  have hP' : ∀ i, ∑ j, B i j • u j = ∑ j, P i j • ∑ k, A j k • u k := hP
  have hQ' : ∀ i, ∑ j, A i j • u j = ∑ j, Q i j • ∑ k, B j k • u k := hQ
  have hBPA : B = P * A := GlobalTheory.CompanionTheory.Ggeo.FrameDet.matrix_eq_of_linearIndependent hu fun i =>
    (hP' i).trans (GlobalTheory.CompanionTheory.Ggeo.FrameDet.sum_smul_sum_smul u P A i)
  have hQP : Q * P = 1 := by
    apply GlobalTheory.CompanionTheory.Ggeo.FrameDet.matrix_eq_of_linearIndependent ha
    intro i
    calc ∑ j, (Q * P) i j • ∑ k, A j k • u k
        = ∑ j, Q i j • ∑ k, P j k • ∑ l, A k l • u l :=
          (GlobalTheory.CompanionTheory.Ggeo.FrameDet.sum_smul_sum_smul (fun k => ∑ l, A k l • u l) Q P i).symm
      _ = ∑ j, Q i j • ∑ k, B j k • u k := Finset.sum_congr rfl fun j _ => by rw [hP' j]
      _ = ∑ k, A i k • u k := (hQ' i).symm
      _ = ∑ j, (1 : Matrix (Fin n) (Fin n) Ω) i j • ∑ k, A j k • u k := by
          simp [Matrix.one_apply]
  have hdet : P.det * Q.det = 1 := by
    rw [mul_comm, ← Matrix.det_mul, hQP, Matrix.det_one]
  refine ⟨P.det, det_mem_of_forall_mem' R P hPR, ?_, left_ne_zero_of_mul_eq_one hdet, ?_⟩
  · rw [inv_eq_of_mul_eq_one_right hdet]
    exact det_mem_of_forall_mem' R Q hQR
  · rw [hBPA, Matrix.det_mul]

end GlobalTheory.CompanionTheory.Ggeo.FrameDet
