import Formalism.NormUnitaryBounds.Statement

open MvPolynomial

noncomputable section

namespace Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange

variable {R : Type*} [CommRing R]

def extW {N N' : ℕ} (v : Fin N → ℕ) : Fin N' → ℕ :=
  fun j => if h : (j : ℕ) < N then v ⟨j, h⟩ else 0

lemma weight_mapDomain_castLE {N N' n : ℕ} (hN : N ≤ N') (d : (Fin N × Fin n) →₀ ℕ) :
    Finsupp.weight (blockWt N' n)
        (Finsupp.mapDomain (fun p : Fin N × Fin n => (Fin.castLE hN p.1, p.2)) d) =
      extW (Finsupp.weight (blockWt N n) d) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (by intro; simp)
    (by intros; simp [add_smul])]
  funext j
  simp only [extW, Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, blockWt, Pi.smul_apply,
    smul_eq_mul]
  split_ifs with h
  · refine Finset.sum_congr rfl fun p _ => ?_
    congr 1
    simp only [Pi.single_apply, Fin.ext_iff, Fin.val_castLE]
  · refine Finset.sum_eq_zero fun p _ => ?_
    have : j ≠ Fin.castLE hN p.1 := by
      intro e; apply h; rw [e]; simp
    simp [this]

lemma isWH_rename {N N' n : ℕ} (hN : N ≤ N') (ν : Fin N → ℕ) (F : MvPolynomial (Fin N × Fin n) R)
    (hF : F.IsWeightedHomogeneous (blockWt N n) ν) :
    (rename (fun p : Fin N × Fin n => (Fin.castLE hN p.1, p.2)) F).IsWeightedHomogeneous
      (blockWt N' n) (extW ν) := by
  induction hF using IsWeightedHomogeneous.induction_on with
  | zero => rw [map_zero]; exact isWeightedHomogeneous_zero R _ _
  | add p q hp hq ihp ihq => rw [map_add]; exact ihp.add ihq
  | monomial d r hr =>
    rw [rename_monomial]
    apply isWeightedHomogeneous_monomial
    rw [weight_mapDomain_castLE, hr]

lemma isWH_det (n : ℕ) :
    (detPoly R n).IsWeightedHomogeneous (blockWt n n) (fun _ => 1) := by
  classical
  rw [detPoly, Matrix.det_apply, ← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem ?_ _
  rw [mem_weightedHomogeneousSubmodule]
  have hsum : (∑ i, blockWt n n (σ i, i)) = fun _ => 1 := by
    funext j
    simp only [blockWt, Finset.sum_apply]
    rw [Equiv.sum_comp σ (fun i' => (Pi.single i' 1 : Fin n → ℕ) j)]
    simp [Pi.single_apply]
  rw [← hsum]
  exact IsWeightedHomogeneous.prod _ _ _ (fun i _ => isWeightedHomogeneous_X R _ _)

lemma mem_H_iff {N n : ℕ} (ν : Fin N → ℕ) (P : MvPolynomial (Fin N × Fin n) R) :
    P ∈ H R ν ↔ P.IsWeightedHomogeneous (blockWt N n) ν ∧
      ∀ i j : Fin N, i < j → shear R i j P = Polynomial.C P := by
  simp only [H, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule,
    IsScalarTower.toAlgHom_apply, Polynomial.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply]

lemma shear_det {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    shear R i j (detPoly R n) = Polynomial.C (detPoly R n) := by
  classical
  set A : Matrix (Fin n) (Fin n) (Polynomial (MvPolynomial (Fin n × Fin n) R)) :=
    (Polynomial.C (R := MvPolynomial (Fin n × Fin n) R)).mapMatrix
      (Matrix.of fun a b : Fin n => (X (a, b) : MvPolynomial (Fin n × Fin n) R)) with hA
  rw [detPoly, AlgHom.map_det]
  have : (shear R i j).mapMatrix
      (Matrix.of fun a b : Fin n => (X (a, b) : MvPolynomial (Fin n × Fin n) R)) =
      A.updateRow j (A j + (Polynomial.X : Polynomial (MvPolynomial (Fin n × Fin n) R)) • A i) := by
    ext a b
    by_cases h : a = j
    · subst h; simp [shear, hA, Matrix.updateRow_apply]
    · simp [shear, hA, Matrix.updateRow_apply, h]
  rw [this, Matrix.det_updateRow_add_smul_self _ hij.symm, hA, ← RingHom.map_det]

lemma shear_rename_lt {N N' n : ℕ} (hN : N ≤ N') (i j : Fin N') (hi : (i : ℕ) < N)
    (hj : (j : ℕ) < N) :
    (shear R i j).comp (rename (fun p : Fin N × Fin n => (Fin.castLE hN p.1, p.2))) =
      (Polynomial.mapAlgHom (rename (fun p : Fin N × Fin n => (Fin.castLE hN p.1, p.2)))).comp
        (shear R (⟨i, hi⟩ : Fin N) ⟨j, hj⟩) := by
  apply MvPolynomial.algHom_ext
  intro p
  have e1 : (Fin.castLE hN p.1 = j) ↔ (p.1 = ⟨j, hj⟩) := by simp [Fin.ext_iff]
  have e2 : Fin.castLE hN (⟨i, hi⟩ : Fin N) = i := by ext; simp
  simp [shear, Polynomial.coe_mapAlgHom, e1]
  split_ifs <;> simp

lemma shear_rename_ge {N N' n : ℕ} (hN : N ≤ N') (i j : Fin N') (hj : N ≤ (j : ℕ)) :
    (shear R i j).comp (rename (fun p : Fin N × Fin n => (Fin.castLE hN p.1, p.2))) =
      (IsScalarTower.toAlgHom R (MvPolynomial (Fin N' × Fin n) R)
        (Polynomial (MvPolynomial (Fin N' × Fin n) R))).comp
        (rename (fun p : Fin N × Fin n => (Fin.castLE hN p.1, p.2))) := by
  apply MvPolynomial.algHom_ext
  intro p
  have e1 : Fin.castLE hN p.1 ≠ j := by
    intro e; have := congrArg Fin.val e; simp at this; omega
  simp [shear, e1]

lemma shear_rename_inv {N N' n : ℕ} (hN : N ≤ N') (F : MvPolynomial (Fin N × Fin n) R)
    (hF : ∀ i j : Fin N, i < j → shear R i j F = Polynomial.C F) (i j : Fin N') (hij : i < j) :
    shear R i j (rename (fun p : Fin N × Fin n => (Fin.castLE hN p.1, p.2)) F) =
      Polynomial.C (rename (fun p : Fin N × Fin n => (Fin.castLE hN p.1, p.2)) F) := by
  by_cases hj : (j : ℕ) < N
  · have hi : (i : ℕ) < N := lt_trans hij hj
    have := AlgHom.congr_fun (shear_rename_lt (R := R) (n := n) hN i j hi hj) F
    simp only [AlgHom.comp_apply] at this
    rw [this, hF _ _ (Fin.mk_lt_mk.mpr hij), Polynomial.coe_mapAlgHom,
      Polynomial.map_C]
    rfl
  · have := AlgHom.congr_fun (shear_rename_ge (R := R) (n := n) hN i j (not_lt.mp hj)) F
    simpa [Polynomial.algebraMap_apply] using this

end Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange

open Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange in
theorem Formalism.NormUnitaryCountingLemmas.shear_hypothesis_two : Formalism.NormUnitaryCountingLemmas.H2 := by
  intro R _ N N' hN ν F hF w
  rw [mem_H_iff] at hF ⊢
  obtain ⟨hFw, hFs⟩ := hF
  constructor
  · have := (isWH_rename hN ν F hFw).mul ((isWH_det (R := R) N').pow w)
    convert this using 1
    funext j
    simp [extW]
  · intro i j hij
    rw [map_mul, map_pow, shear_det i j hij.ne, shear_rename_inv hN F hFs i j hij, ← map_pow,
      ← map_mul]
