import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ContractionDerivatives.ContractLeftMap

noncomputable section

open Matrix

namespace PositivityTheory.RgBcC.Cxb

open PositivityTheory.RgBcC

variable {n : ℕ}

abbrev ιE (n : ℕ) : (Md n → ℂ) →ₗ[ℂ] abelian₂ n := ExteriorAlgebra.ι ℂ

theorem fb_eq (A : Finset (Md n)) : ∃ w : Fin A.card → (Md n → ℂ), fb n A = ExteriorAlgebra.ιMulti ℂ A.card w :=
  ⟨_, by rw [fb, ExteriorAlgebra.basis_apply]⟩

theorem toLin'_smul_one (s : ℂ) : Matrix.toLin' (s • (1 : Matrix (Md n) (Md n) ℂ)) = s • LinearMap.id := by
  rw [map_smul, Matrix.toLin'_one]

theorem map_smul_ι (s : ℂ) (v : Md n → ℂ) :
    ExteriorAlgebra.map (Matrix.toLin' (s • (1 : Matrix (Md n) (Md n) ℂ))) (ιE n v) = s • ιE n v := by
  rw [toLin'_smul_one, ExteriorAlgebra.map_apply_ι]
  simp

theorem map_smul_prod (s : ℂ) (l : List (Md n → ℂ)) :
    ExteriorAlgebra.map (Matrix.toLin' (s • (1 : Matrix (Md n) (Md n) ℂ))) (l.map (ιE n)).prod =
      s ^ l.length • (l.map (ιE n)).prod := by
  induction l with
  | nil => simp
  | cons v l ih =>
    rw [List.map_cons, List.prod_cons, map_mul, map_smul_ι, ih, List.length_cons, smul_mul_smul_comm, pow_succ, mul_comm s]

def Pm (n : ℕ) (s : ℂ) : abelian₂ n →ₗ[ℂ] abelian₂ n :=
  ∑ m : Md n, LinearMap.mul ℂ (abelian₂ n) (ιE n (Pi.single m 1)) *
    (ExteriorAlgebra.map (Matrix.toLin' (s • (1 : Matrix (Md n) (Md n) ℂ)))).toLinearMap *
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (Md n → ℂ))) (dualOf (Pi.single m 1))

theorem ι_anticomm (a b : Md n → ℂ) : ιE n a * ιE n b = -(ιE n b * ιE n a) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap a b)

theorem Pm_apply (s : ℂ) (y : abelian₂ n) : Pm n s y = ∑ m : Md n, ιE n (Pi.single m 1) *
    ExteriorAlgebra.map (Matrix.toLin' (s • (1 : Matrix (Md n) (Md n) ℂ)))
      (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (Md n → ℂ))) (dualOf (Pi.single m 1)) y) := by
  simp only [Pm, LinearMap.sum_apply, Module.End.mul_apply, LinearMap.mul_apply', AlgHom.toLinearMap_apply]

theorem Pm_ι_mul (s : ℂ) (v : Md n → ℂ) (y : abelian₂ n) :
    Pm n s (ιE n v * y) = ιE n v * ExteriorAlgebra.map (Matrix.toLin' (s • (1 : Matrix (Md n) (Md n) ℂ))) y +
      s • (ιE n v * Pm n s y) := by
  have hv : ∑ m : Md n, v m • ιE n (Pi.single m 1) = ιE n v := by
    simp_rw [← LinearMap.map_smul, ← map_sum]
    congr 1
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hm : ∀ m : Md n, ιE n (Pi.single m 1) * ExteriorAlgebra.map (Matrix.toLin' (s • (1 : Matrix (Md n) (Md n) ℂ)))
      (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (Md n → ℂ))) (dualOf (Pi.single m 1)) (ιE n v * y)) =
      v m • (ιE n (Pi.single m 1) * ExteriorAlgebra.map (Matrix.toLin' (s • (1 : Matrix (Md n) (Md n) ℂ))) y) +
      s • (ιE n v * (ιE n (Pi.single m 1) * ExteriorAlgebra.map (Matrix.toLin' (s • (1 : Matrix (Md n) (Md n) ℂ)))
        (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (Md n → ℂ))) (dualOf (Pi.single m 1)) y))) := by
    intro m
    have hd : dualOf (Pi.single m 1) v = v m := by simp [dualOf]
    rw [CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul, map_mul, map_smul_ι, hd]
    rw [mul_sub, mul_smul_comm, smul_mul_assoc, mul_smul_comm, ← mul_assoc, ι_anticomm, neg_mul, mul_assoc,
      smul_neg, sub_neg_eq_add]
  rw [Pm_apply, Pm_apply, Finset.sum_congr rfl (fun m _ => hm m), Finset.sum_add_distrib]
  congr 1
  · simp_rw [← smul_mul_assoc]
    rw [← Finset.sum_mul, hv]
  · rw [Finset.mul_sum, Finset.smul_sum]

theorem ofFn_eq {k : ℕ} (w : Fin k → Md n → ℂ) :
    (List.ofFn fun i => ExteriorAlgebra.ι ℂ (w i)) = (List.ofFn w).map (ιE n) := by
  rw [List.map_ofFn]; rfl

theorem Pm_one (s : ℂ) : Pm n s 1 = 0 := by
  simp [Pm_apply, CliffordAlgebra.contractLeft_one]

theorem Pm_prod (s : ℂ) (l : List (Md n → ℂ)) :
    Pm n s (l.map (ιE n)).prod = ((l.length : ℂ) * s ^ (l.length - 1)) • (l.map (ιE n)).prod := by
  induction l with
  | nil => simp [Pm_one]
  | cons v l ih =>
    rw [List.map_cons, List.prod_cons, Pm_ι_mul, map_smul_prod, ih, mul_smul_comm, mul_smul_comm, smul_smul, ← add_smul]
    congr 1
    rw [List.length_cons]
    have hk : ∀ k : ℕ, s ^ k + s * ((k : ℂ) * s ^ (k - 1)) = ((k + 1 : ℕ) : ℂ) * s ^ (k + 1 - 1) := by
      intro k
      rcases k with _ | k
      · simp
      · simp only [Nat.add_sub_cancel]
        push_cast
        ring
    exact hk _

end PositivityTheory.RgBcC.Cxb

namespace PositivityTheory.RgBcC

open PositivityTheory.RgBcC.Cxb

theorem gamScal : GamScal := by
  intro n s
  ext B A
  rw [gamM_eq, matL, LinearMap.toMatrix_apply, Matrix.diagonal_apply]
  obtain ⟨w, hw⟩ := fb_eq (n := n) A
  have h : (ExteriorAlgebra.map (Matrix.toLin' (s • (1 : Matrix (Md n) (Md n) ℂ)))).toLinearMap (fb n A) =
      s ^ A.card • fb n A := by
    rw [AlgHom.toLinearMap_apply, hw, ExteriorAlgebra.ιMulti_apply, ofFn_eq, map_smul_prod, List.length_ofFn]
  rw [h, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
  by_cases e : A = B
  · subst e; simp
  · simp [e, Ne.symm e]

theorem number : Number := by
  intro n s
  have e : ∑ m : Md n, creL n (Pi.single m 1) * gamM (s • (1 : Matrix (Md n) (Md n) ℂ)) * annL n (Pi.single m 1) =
      matL n (Pm n s) := by
    rw [Pm, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [creL_eq, gamM_eq, annL_eq, ← matL_mul, ← matL_mul]
  rw [e]
  ext B A
  rw [matL, LinearMap.toMatrix_apply, Matrix.diagonal_apply]
  obtain ⟨w, hw⟩ := fb_eq (n := n) A
  have h : Pm n s (fb n A) = ((A.card : ℂ) * s ^ (A.card - 1)) • fb n A := by
    rw [hw, ExteriorAlgebra.ιMulti_apply, ofFn_eq, Pm_prod, List.length_ofFn]
  rw [h, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
  by_cases e : A = B
  · subst e; simp
  · simp [e, Ne.symm e]

end PositivityTheory.RgBcC
