import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.LinDefs

noncomputable section

namespace PI.UnitaryGroupMassFormula.ScXuExists

open Matrix

section Pr

variable {K : Type} [Field K] {n : ℕ} (P : Matrix (Fin n) (Fin n) K)

theorem pr_add_left (β β' x : Fin n → K) : pr P (β + β') x = pr P β x + pr P β' x := by
  first
  | simp [pr]
  | simp [pr, dotProduct, Finset.sum_add_distrib, add_mul]

theorem pr_sub_left (β β' x : Fin n → K) : pr P (β - β') x = pr P β x - pr P β' x := by
  first
  | simp [pr]
  | simp [pr, dotProduct, Finset.sum_sub_distrib, sub_mul]

theorem pr_smul_left (c : K) (β x : Fin n → K) : pr P (c • β) x = c * pr P β x := by
  first
  | simp [pr]
  | simp [pr, dotProduct, Finset.mul_sum, mul_assoc]

theorem pr_add_right (β x y : Fin n → K) : pr P β (x + y) = pr P β x + pr P β y := by
  unfold pr
  rw [Matrix.mulVec_add, dotProduct_add]

theorem pr_sub_right (β x y : Fin n → K) : pr P β (x - y) = pr P β x - pr P β y := by
  unfold pr
  rw [Matrix.mulVec_sub, dotProduct_sub]

theorem pr_smul_right (c : K) (β x : Fin n → K) : pr P β (c • x) = c * pr P β x := by
  unfold pr
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem pr_sum_left {ι : Type} (s : Finset ι) (β : ι → Fin n → K) (x : Fin n → K) :
    pr P (∑ i ∈ s, β i) x = ∑ i ∈ s, pr P (β i) x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [pr]
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, pr_add_left, ih]

theorem pr_sum_right {ι : Type} (s : Finset ι) (β : Fin n → K) (x : ι → Fin n → K) :
    pr P β (∑ i ∈ s, x i) = ∑ i ∈ s, pr P β (x i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [pr]
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, pr_add_right, ih]

theorem pr_eq_vecMul (β x : Fin n → K) : pr P β x = (β ᵥ* P) ⬝ᵥ x := by
  first
  | exact dotProduct_mulVec β P x
  | exact Matrix.dotProduct_mulVec β P x
  | simp [pr, dotProduct_mulVec]

end Pr

section Rk1

variable {R : Type} [CommRing R] {n : ℕ}

theorem one_add_smul_vecMulVec_mul (p q : Fin n → R) (c d : R) :
    (1 + c • vecMulVec p q) * (1 + d • vecMulVec p q) =
      1 + (c + d + c * d * (q ⬝ᵥ p)) • vecMulVec p q := by
  have key : vecMulVec p q * vecMulVec p q = (q ⬝ᵥ p) • vecMulVec p q := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, dotProduct,
      Finset.sum_mul]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, key, smul_smul]
  first
  | (module; done)
  | (rw [add_smul, add_smul, show c * d * (q ⬝ᵥ p) = d * (c * (q ⬝ᵥ p)) by ring]; abel; done)
  | (rw [add_smul, add_smul, show c * d * (q ⬝ᵥ p) = c * (d * (q ⬝ᵥ p)) by ring]; abel; done)

def rankOneUnitGL (p q : Fin n → R) (c d : R) (h : c + d + c * d * (q ⬝ᵥ p) = 0) : GL (Fin n) R :=
  ⟨1 + c • vecMulVec p q, 1 + d • vecMulVec p q, by rw [one_add_smul_vecMulVec_mul, h, zero_smul, add_zero],
    by rw [one_add_smul_vecMulVec_mul, show d + c + d * c * (q ⬝ᵥ p) = 0 by linear_combination h, zero_smul, add_zero]⟩

theorem coe_rankOneGL (p q : Fin n → R) (c d : R) (h : c + d + c * d * (q ⬝ᵥ p) = 0) :
    ((rankOneUnitGL p q c d h : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = 1 + c • vecMulVec p q := rfl

theorem coe_rankOneGL_inv (p q : Fin n → R) (c d : R) (h : c + d + c * d * (q ⬝ᵥ p) = 0) :
    (((rankOneUnitGL p q c d h)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = 1 + d • vecMulVec p q := rfl

theorem one_add_smul_vecMulVec_mulVec (p q x : Fin n → R) (c : R) :
    (1 + c • vecMulVec p q) *ᵥ x = x + (c * (q ⬝ᵥ x)) • p := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec]
  ext i
  simp only [Pi.add_apply, add_right_inj, Matrix.mulVec, dotProduct, Matrix.smul_apply,
    Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  all_goals exact Finset.sum_congr rfl (fun j _ => by ring)

theorem vecMul_one_add_smul_vecMulVec (p q y : Fin n → R) (c : R) :
    y ᵥ* (1 + c • vecMulVec p q) = y + (c * (y ⬝ᵥ p)) • q := by
  rw [Matrix.vecMul_add, Matrix.vecMul_one]
  ext j
  simp only [Pi.add_apply, add_right_inj, Matrix.vecMul, dotProduct, Matrix.smul_apply,
    Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  all_goals exact Finset.sum_congr rfl (fun i _ => by ring)

end Rk1

section Good

variable {K : Type} [Field K] (O : ValuationSubring K) {n r : ℕ} (P : Matrix (Fin n) (Fin n) K)
  (Λ1 Λ2 : Submodule O (Fin n → K)) (a a' α α' : Fin r → Fin n → K)

theorem smem {M : Submodule O (Fin n → K)} {c : K} (hc : c ∈ O) {x : Fin n → K} (hx : x ∈ M) :
    c • x ∈ M := by
  first
  | exact M.smul_mem (⟨c, hc⟩ : O) hx
  | (have h := M.smul_mem (⟨c, hc⟩ : O) hx
     simpa [Algebra.smul_def] using h)

def Good (T : GL (Fin n) K) : Prop :=
  (∀ x ∈ Λ1, (T : Matrix (Fin n) (Fin n) K) *ᵥ x ∈ Λ1 ∧
        ((T⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x ∈ Λ1) ∧
      (∀ β ∈ Λ2, (∃ β' ∈ Λ2, β' ᵥ* P = (β ᵥ* P) ᵥ* (T : Matrix (Fin n) (Fin n) K)) ∧
        (∃ β' ∈ Λ2, β' ᵥ* P = (β ᵥ* P) ᵥ* ((T⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) ∧
      (∀ i, (T : Matrix (Fin n) (Fin n) K) *ᵥ a i = a i ∧ (T : Matrix (Fin n) (Fin n) K) *ᵥ a' i = a' i ∧
        (α i ᵥ* P) ᵥ* (T : Matrix (Fin n) (Fin n) K) = α i ᵥ* P ∧
        (α' i ᵥ* P) ᵥ* (T : Matrix (Fin n) (Fin n) K) = α' i ᵥ* P)

private theorem smul_vecMul' (b : K) (v : Fin n → K) (M : Matrix (Fin n) (Fin n) K) :
    (b • v) ᵥ* M = b • (v ᵥ* M) := by
  ext j
  simp only [Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem good_mul {S T : GL (Fin n) K} (hS : Good O P Λ1 Λ2 a a' α α' S)
    (hT : Good O P Λ1 Λ2 a a' α α' T) : Good O P Λ1 Λ2 a a' α α' (S * T) := by
  unfold Good at hS hT ⊢
  obtain ⟨hS1, hS2, hS3⟩ := hS
  obtain ⟨hT1, hT2, hT3⟩ := hT
  have hmul : ((S * T : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (S : Matrix (Fin n) (Fin n) K) * (T : Matrix (Fin n) (Fin n) K) := Units.val_mul S T
  have hinv : (((S * T)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((T⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((S⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [_root_.mul_inv_rev]
    exact Units.val_mul _ _
  rw [hinv, hmul]
  refine ⟨fun x hx => ?_, fun β hβ => ?_, fun i => ?_⟩
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact ⟨(hS1 _ (hT1 x hx).1).1, (hT1 _ (hS1 x hx).2).2⟩
  · rw [← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul]
    obtain ⟨⟨β1, hβ1, e1⟩, -⟩ := hS2 β hβ
    obtain ⟨⟨β2, hβ2, e2⟩, -⟩ := hT2 β1 hβ1
    obtain ⟨-, ⟨γ1, hγ1, f1⟩⟩ := hT2 β hβ
    obtain ⟨-, ⟨γ2, hγ2, f2⟩⟩ := hS2 γ1 hγ1
    exact ⟨⟨β2, hβ2, by rw [e2, e1]⟩, ⟨γ2, hγ2, by rw [f2, f1]⟩⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hS3 i
    obtain ⟨k1, k2, k3, k4⟩ := hT3 i
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul,
      k1, k2, h1, h2, h3, h4, k3, k4]
    exact ⟨rfl, rfl, rfl, rfl⟩

variable {O P Λ1 Λ2 a a' α α'} in
theorem isAdmissible_rankOneGL (hP : ∀ β ∈ Λ2, ∀ x ∈ Λ1, pr P β x ∈ O) (w γ : Fin n → K) (c d : K)
    (h : c + d + c * d * ((γ ᵥ* P) ⬝ᵥ w) = 0) (hc : c ∈ O) (hd : d ∈ O) (hw : w ∈ Λ1) (hγ : γ ∈ Λ2)
    (hwα : ∀ i, pr P (α i) w = 0 ∧ pr P (α' i) w = 0) (hγa : ∀ i, pr P γ (a i) = 0 ∧ pr P γ (a' i) = 0) :
    Good O P Λ1 Λ2 a a' α α' (rankOneUnitGL w (γ ᵥ* P) c d h) := by
  unfold Good
  rw [coe_rankOneGL_inv, coe_rankOneGL]
  have hm : ∀ {u v : K}, u ∈ O → v ∈ O → u * v ∈ O := by
    intro u v hu hv
    first
    | exact mul_mem hu hv
    | exact O.mul_mem _ _ hu hv
    | exact O.toSubring.mul_mem hu hv
  have hO : ∀ x ∈ Λ1, (γ ᵥ* P) ⬝ᵥ x ∈ O := fun x hx => by
    rw [← pr_eq_vecMul]
    exact hP γ hγ x hx
  have hO' : ∀ β ∈ Λ2, (β ᵥ* P) ⬝ᵥ w ∈ O := fun β hβ => by
    rw [← pr_eq_vecMul]
    exact hP β hβ w hw
  have hvec : ∀ (e : K) (β : Fin n → K),
      (β + (e * ((β ᵥ* P) ⬝ᵥ w)) • γ) ᵥ* P = (β ᵥ* P) ᵥ* (1 + e • vecMulVec w (γ ᵥ* P)) := by
    intro e β
    rw [vecMul_one_add_smul_vecMulVec, Matrix.add_vecMul, smul_vecMul']
  refine ⟨fun x hx => ⟨?_, ?_⟩,
    fun β hβ => ⟨⟨β + (c * ((β ᵥ* P) ⬝ᵥ w)) • γ, ?_, hvec c β⟩,
      ⟨β + (d * ((β ᵥ* P) ⬝ᵥ w)) • γ, ?_, hvec d β⟩⟩, fun i => ?_⟩
  · rw [one_add_smul_vecMulVec_mulVec]
    exact Λ1.add_mem hx (smem O (hm hc (hO x hx)) hw)
  · rw [one_add_smul_vecMulVec_mulVec]
    exact Λ1.add_mem hx (smem O (hm hd (hO x hx)) hw)
  · exact Λ2.add_mem hβ (smem O (hm hc (hO' β hβ)) hγ)
  · exact Λ2.add_mem hβ (smem O (hm hd (hO' β hβ)) hγ)
  · have e1 : (γ ᵥ* P) ⬝ᵥ a i = 0 := by rw [← pr_eq_vecMul]; exact (hγa i).1
    have e2 : (γ ᵥ* P) ⬝ᵥ a' i = 0 := by rw [← pr_eq_vecMul]; exact (hγa i).2
    have e3 : (α i ᵥ* P) ⬝ᵥ w = 0 := by rw [← pr_eq_vecMul]; exact (hwα i).1
    have e4 : (α' i ᵥ* P) ⬝ᵥ w = 0 := by rw [← pr_eq_vecMul]; exact (hwα i).2
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [one_add_smul_vecMulVec_mulVec, e1, mul_zero, zero_smul, add_zero]
    · rw [one_add_smul_vecMulVec_mulVec, e2, mul_zero, zero_smul, add_zero]
    · rw [vecMul_one_add_smul_vecMulVec, e3, mul_zero, zero_smul, add_zero]
    · rw [vecMul_one_add_smul_vecMulVec, e4, mul_zero, zero_smul, add_zero]

end Good

end PI.UnitaryGroupMassFormula.ScXuExists
