import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent

noncomputable section

open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

section Columns

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

def colMat (c : n → Matrix n n A) (v : n → A) : Matrix n n A :=
  Matrix.of fun i j => (c j *ᵥ v) i

omit [DecidableEq n] in
theorem colMat_mulVec (c : n → Matrix n n A) (v a : n → A) :
    colMat c v *ᵥ a = (∑ j, a j • c j) *ᵥ v := by
  rw [Matrix.sum_mulVec]
  funext i
  simp only [Finset.sum_apply, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
  simp [colMat, Matrix.mulVec, dotProduct, mul_comm]

omit [DecidableEq n] in
theorem colMat_map {B : Type} [CommRing B] (f : A →+* B) (c : n → Matrix n n A) (v : n → A) :
    (colMat c v).map f = colMat (fun j => (c j).map f) (fun i => f (v i)) := by
  ext i j
  simp [colMat, Matrix.mulVec, dotProduct]

theorem eq_sum_of_commute_cols {c : n → Matrix n n A} {v : n → A} (hB : IsUnit (colMat c v))
    (hc : ∀ i j, c i * c j = c j * c i) {N : Matrix n n A} (hN : ∀ j, N * c j = c j * N) :
    ∃ a : n → A, ∑ j, a j • c j = N := by
  obtain ⟨a, ha⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hB (N *ᵥ v)
  refine ⟨a, Matrix.toLin'.injective (LinearMap.ext fun y => ?_)⟩
  obtain ⟨t, rfl⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hB y
  have ha' : (∑ j, a j • c j) *ᵥ v = N *ᵥ v := by rw [← colMat_mulVec]; exact ha
  have h1 : N * (∑ j, t j • c j) = (∑ j, t j • c j) * N := by
    simp [Finset.mul_sum, Finset.sum_mul, hN]
  have h2 : (∑ j, a j • c j) * (∑ j, t j • c j) = (∑ j, t j • c j) * (∑ j, a j • c j) :=
    Commute.sum_left _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ =>
      (Commute.smul_left (Commute.smul_right (hc i j) _) _)
  simp only [Matrix.toLin'_apply, colMat_mulVec, Matrix.mulVec_mulVec]
  rw [h1, h2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha']

theorem map_commute_of_mem_genAlg {B : Type} [CommRing B] (f : A →+* B) {M l : Matrix n n A}
    {N : Matrix n n B} (h : N * M.map f = M.map f * N) (hl : l ∈ genAlg M) :
    N * l.map f = l.map f * N := by
  unfold genAlg at hl
  induction hl using Algebra.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact h
  | algebraMap r =>
    have : (algebraMap A (Matrix n n A) r).map f = f r • (1 : Matrix n n B) := by
      ext i j; by_cases hij : i = j <;> simp [Matrix.algebraMap_matrix_apply, hij]
    rw [this]; simp
  | add x y _ _ hx hy => rw [Matrix.map_add _ (map_add f), Matrix.mul_add, Matrix.add_mul, hx, hy]
  | mul x y _ _ hx hy =>
    rw [Matrix.map_mul, ← Matrix.mul_assoc, hx, Matrix.mul_assoc, hy, Matrix.mul_assoc]

end Columns

theorem exists_sum_basis_tmul {F P A : Type} [Field F] [AddCommGroup P] [Module F P]
    [AddCommGroup A] [Module F A] {n : Type} [Fintype n] (b : Module.Basis n F P)
    (x : P ⊗[F] A) : ∃ a : n → A, ∑ j, b j ⊗ₜ[F] a j = x := by
  obtain ⟨c, hc⟩ := TensorProduct.eq_repr_basis_left b x
  exact ⟨c, by rw [← hc, Finsupp.sum_fintype]; simp⟩

theorem toMat_tmul_eq_smul {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type}
    [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J γ : Matrix n n E) (R : Type) [CommRing R]
    [Algebra F R] (l : plusAlg σ J γ) (a : E ⊗[F] R) :
    toMat σ J γ R (l ⊗ₜ a) = a • ((l : genAlg γ) : Matrix n n E).map (inclE (F := F) R) := by
  rw [Algebra.smul_def, Algebra.commutes]
  exact Algebra.TensorProduct.lift_tmul _ _ _ l a

theorem pointsCommutant : PointsCommutant := by
  intro F E _ _ _ _ n _ _ σ J γ _ hA hP R _ _
  obtain ⟨-, ⟨b⟩, hbij⟩ := hP
  obtain ⟨-, -, -, ⟨v, hv⟩, -⟩ := hA
  let c : n → Matrix n n E := fun j => ((b j : genAlg (γ : Matrix n n E)) : Matrix n n E)
  have hB : IsUnit (colMat c v) := by
    refine Matrix.mulVec_surjective_iff_isUnit.1 fun y => ?_
    obtain ⟨l, rfl⟩ := hv.2 y
    obtain ⟨x, rfl⟩ := hbij.2 l
    obtain ⟨a, rfl⟩ := exists_sum_basis_tmul b x
    refine ⟨a, ?_⟩
    rw [colMat_mulVec]
    congr 1
    rw [map_sum, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [plusTensor, Algebra.TensorProduct.productMap_apply_tmul, mul_comm]
    exact Algebra.smul_def (a j) (c j)
  let f : E →+* E ⊗[F] R := inclE (F := F) R
  have hB' : IsUnit (colMat (fun j => (c j).map f) (fun i => f (v i))) := by
    rw [← colMat_map]; exact hB.map f.mapMatrix
  have hsum : ∀ a : n → E ⊗[F] R, toMat σ J (γ : Matrix n n E) R (∑ j, b j ⊗ₜ[F] a j) =
      ∑ j, a j • (c j).map f := fun a => by
    rw [map_sum]; exact Finset.sum_congr rfl fun j _ => toMat_tmul_eq_smul _ _ _ _ _ _
  refine ⟨(injective_iff_map_eq_zero _).2 fun u hu => ?_, fun N => ⟨fun hN => ?_, ?_⟩⟩
  · obtain ⟨a, rfl⟩ := exists_sum_basis_tmul b u
    rw [hsum] at hu
    have : a = 0 := Matrix.mulVec_injective_of_isUnit hB'
      (by rw [colMat_mulVec, hu, Matrix.zero_mulVec, Matrix.mulVec_zero])
    simp [this]
  · obtain ⟨a, ha⟩ := eq_sum_of_commute_cols hB' (fun i j => by
      rw [← Matrix.map_mul, ← Matrix.map_mul]
      exact congrArg (fun l : genAlg (γ : Matrix n n E) => (l : Matrix n n E).map f)
        (mul_comm (b i : genAlg (γ : Matrix n n E)) (b j)))
      (fun j => map_commute_of_mem_genAlg f hN (b j : genAlg (γ : Matrix n n E)).2)
    exact ⟨_, (hsum a).trans ha⟩
  · rintro ⟨u, rfl⟩
    obtain ⟨a, rfl⟩ := exists_sum_basis_tmul b u
    rw [hsum]
    refine Commute.sum_left _ _ _ fun j _ => Commute.smul_left ?_ _
    exact (map_commute_of_mem_genAlg f rfl (b j : genAlg (γ : Matrix n n E)).2).symm

end GlobalTheory.RegSS
