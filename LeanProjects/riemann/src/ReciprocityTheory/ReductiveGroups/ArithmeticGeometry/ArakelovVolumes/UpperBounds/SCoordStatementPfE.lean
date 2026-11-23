import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SCoordStatementPfB

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.SCoE

open MvPolynomial

noncomputable section

def pdet {Ω : Type} [Field Ω] {n N : ℕ} {j0 : Fin (N + 1)} {B : Set {j // j ≠ j0}} (e : Fin n ≃ B)
    (a : {j // j ≠ j0} → B → Ω) : MvPolynomial (Fin n × {j // j ≠ j0}) Ω :=
  (Matrix.of fun i k : Fin n => ∑ j : {j // j ≠ j0}, X (i, j) * C (a j (e k))).det

theorem pdet_ne {Ω : Type} [Field Ω] {n N : ℕ} {j0 : Fin (N + 1)} {B : Set {j // j ≠ j0}} (e : Fin n ≃ B)
    (a : {j // j ≠ j0} → B → Ω) (ha : ∀ b : B, a b.1 = Pi.single b 1) : pdet e a ≠ 0 := by
  classical
  intro h0
  have h1 := congrArg (eval (fun q : Fin n × {j // j ≠ j0} => if q.2 = (e q.1).1 then (1 : Ω) else 0)) h0
  rw [map_zero, pdet, RingHom.map_det] at h1
  have h2 : (eval (fun q : Fin n × {j // j ≠ j0} => if q.2 = (e q.1).1 then (1 : Ω) else 0)).mapMatrix
      (Matrix.of fun i k : Fin n => ∑ j : {j // j ≠ j0}, X (i, j) * C (a j (e k))) = 1 := by
    ext i k
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul,
      eval_X, eval_C, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, ha,
      Matrix.one_apply]
    rw [Pi.single_apply]
    simp [e.apply_eq_iff_eq, eq_comm]
  rw [h2, Matrix.det_one] at h1
  exact one_ne_zero h1

theorem eval_pdet {Ω : Type} [Field Ω] {n N : ℕ} {j0 : Fin (N + 1)} {B : Set {j // j ≠ j0}} (e : Fin n ≃ B)
    (a : {j // j ≠ j0} → B → Ω) (φ : Ω →+* ℂ) (t : Fin (n + 1) × Fin (N + 1) → ℂ) :
    eval₂ φ (fun q : Fin n × {j // j ≠ j0} => t (q.1.succ, q.2.1)) (pdet e a) =
      (Matrix.of fun i k : Fin n => ∑ j : {j // j ≠ j0}, t (i.succ, j.1) * φ (a j (e k))).det := by
  classical
  rw [pdet, ← coe_eval₂Hom, RingHom.map_det]
  congr 1
  ext i k
  simp [RingHom.mapMatrix_apply, Matrix.map_apply]

theorem det_ne {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {n N : ℕ} (sg : K →+* ℂ)
    (φ : Ω →+* ℂ) (hφ : φ.comp (algebraMap K Ω) = sg) (j0 : Fin (N + 1)) (u : Fin (N + 1) → Ω)
    (hu0 : u j0 = 1) (B : Set {j // j ≠ j0}) [Fintype B]
    (hy : IsTranscendenceBasis K (fun b : B => u b.1.1)) (e : Fin n ≃ B)
    (a : {j // j ≠ j0} → B → Ω) (ha : ∀ b : B, a b.1 = Pi.single b 1)
    (t : Fin (n + 1) × Fin (N + 1) → ℂ)
    (ht : ∀ Q : MvPolynomial (Fin (n + 1) × Fin (N + 1)) K, Q ≠ 0 → eval₂ sg t Q ≠ 0)
    (hrel : ∀ i : Fin n, ∑ j, t (i.succ, j) * φ (u j) = 0) :
    (Matrix.of fun i k : Fin n => ∑ j : {j // j ≠ j0}, t (i.succ, j.1) * φ (a j (e k))).det ≠ 0 := by
  classical
  have hcard : Fintype.card B ≤ Fintype.card (Fin n) := (Fintype.card_congr e).symm.le
  let f : Fin n × Fin (N + 1) → Fin (n + 1) × Fin (N + 1) := fun p => (p.1.succ, p.2)
  have hf : Function.Injective f := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    simp only [f, Prod.mk.injEq, Fin.succ_inj] at h
    rw [h.1, h.2]
  have ht' : ∀ Q : MvPolynomial (Fin n × Fin (N + 1)) K, Q ≠ 0 →
      eval₂ sg (fun p => (fun i j => t (i.succ, j)) p.1 p.2) Q ≠ 0 := by
    intro Q hQ
    have h1 := ht (rename f Q) (by simpa using (rename_injective f hf).ne hQ)
    rwa [eval₂_rename] at h1
  have hgen : ∀ p : MvPolynomial (Fin n × {j // j ≠ j0}) Ω, p ≠ 0 →
      eval₂ φ (fun q => t (q.1.succ, q.2.1)) p ≠ 0 :=
    SCoB.gen_indep (ιB := B) (R := Fin n) sg φ hφ hy j0 u hu0 (fun i j => t (i.succ, j)) ht' hrel hcard
  rw [← eval_pdet e a φ t]
  exact hgen _ (pdet_ne e a ha)

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.SCoE
