import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordTieCompEquiv

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun

open AlgebraicGeometry CategoryTheory

variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {S : Type} {r : S → ℕ}

theorem genU_diag (s : S) (k : Fin (r s)) : genU Ω r s k k = 1 := by
  simp [genU]

theorem genU_above (s : S) (l k : Fin (r s)) (h : l < k) : genU Ω r s l k = 0 := by
  have h1 : ¬ k < l := not_lt.mpr h.le
  simp [genU, h1, h.ne]

theorem genU_below (s : S) (l k : Fin (r s)) (h : k < l) :
    genU Ω r s l k = algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r)
      (MvPolynomial.X ⟨s, ⟨(l, k), h⟩⟩) := by
  simp only [genU, dif_pos h]

theorem genU_det (s : S) : (genU Ω r s).det = 1 := by
  have hlow : (genU Ω r s).IsLowerTriangular := by
    intro i j hij
    exact genU_above s i j (by simpa using hij)
  rw [Matrix.det_of_isLowerTriangular _ hlow]
  exact Finset.prod_eq_one fun i _ => genU_diag s i

theorem genField_adjoin_eq_top :
    IntermediateField.adjoin Ω
      (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => genU Ω r q.1 q.2.1 q.2.2) = ⊤ := by
  set K := IntermediateField.adjoin Ω
    (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => genU Ω r q.1 q.2.1 q.2.2) with hK
  have hX : ∀ i : GenIx r,
      algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X i) ∈ K := by
    intro i
    obtain ⟨s, ⟨⟨l, k⟩, h⟩⟩ := i
    apply IntermediateField.subset_adjoin
    exact ⟨⟨s, (l, k)⟩, genU_below s l k h⟩
  have hP : ∀ p : MvPolynomial (GenIx r) Ω,
      algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) p ∈ K := by
    intro p
    refine MvPolynomial.induction_on
      (motive := fun p => algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) p ∈ K) p ?_ ?_ ?_
    · intro a
      have h1 := IsScalarTower.algebraMap_apply Ω (MvPolynomial (GenIx r) Ω) (GenField Ω r) a
      rw [MvPolynomial.algebraMap_eq] at h1
      rw [← h1]
      exact IntermediateField.algebraMap_mem K a
    · intro p q hp hq
      rw [map_add]
      exact add_mem hp hq
    · intro p n hp
      rw [map_mul]
      exact mul_mem hp (hX n)
  refine eq_top_iff.mpr fun z _ => ?_
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial (GenIx r) Ω) z
  exact div_mem (hP a) (hP b)

theorem linearIndependent_one_tmul {ι : Type} {v : ι → E} (hv : LinearIndependent Ω v) :
    LinearIndependent (GenField Ω r)
      fun k => TensorProduct.mk Ω (GenField Ω r) E 1 (v k) := by
  simpa only [TensorProduct.mk_apply] using
    Module.Flat.linearIndependent_one_tmul (S := GenField Ω r) hv

theorem genB_linearIndependent (c : ∀ s, Fin (r s) → E) (s : S)
    (h : LinearIndependent (GenField Ω r)
      fun k => TensorProduct.mk Ω (GenField Ω r) E 1 (c s k)) :
    LinearIndependent (GenField Ω r) (genB (Ω := Ω) c s) := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg
  have hz : ∀ l, ∑ k, genU Ω r s l k * g k = 0 := by
    refine h (fun l => ∑ k, genU Ω r s l k * g k) ?_
    rw [← hg]
    simp only [genB, Finset.smul_sum, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by rw [mul_comm]
  have hv : Matrix.mulVec (genU Ω r s) g = 0 := by
    ext l
    exact hz l
  have hU : IsUnit (genU Ω r s).det := by
    rw [genU_det]
    exact isUnit_one
  have hg0 : g = 0 := by
    calc g = Matrix.mulVec ((genU Ω r s)⁻¹ * genU Ω r s) g := by
          rw [Matrix.nonsing_inv_mul _ hU, Matrix.one_mulVec]
      _ = Matrix.mulVec (genU Ω r s)⁻¹ (Matrix.mulVec (genU Ω r s) g) := by rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [hv, Matrix.mulVec_zero]
  intro k
  simp [hg0]

theorem genB_isGenericFlag : ∀ (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (S : Type)
    (r : S → ℕ) (V : S → Submodule Ω E) (c : ∀ s, Fin (r s) → E),
    (∀ s, LinearIndependent Ω (c s) ∧ Submodule.span Ω (Set.range (c s)) = V s) →
    IsGenericFlag (Ω' := GenField Ω r) (TensorProduct.mk Ω (GenField Ω r) E 1).toAddMonoidHom V (genB c) 1 := by
  intro Ω hΩ E hE hEm S r V c hc
  unfold IsGenericFlag
  have hli : ∀ σ, LinearIndependent (GenField Ω r)
      fun k => TensorProduct.mk Ω (GenField Ω r) E 1 (c σ k) :=
    fun σ => linearIndependent_one_tmul (r := r) (hc σ).1
  refine ⟨c, genU Ω r, hc, ?_, fun σ => hli σ, fun σ => genB_linearIndependent c σ (hli σ),
    fun σ k => genU_diag σ k, fun σ l k h => genU_above σ l k h, fun σ i => rfl, ?_, Nat.one_pos, ?_⟩
  · intro a e
    simp only [LinearMap.toAddMonoidHom_coe, TensorProduct.mk_apply]
    rw [TensorProduct.tmul_smul, algebraMap_smul]
  · have hai : AlgebraicIndependent Ω (fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} =>
        algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q)) :=
      (MvPolynomial.algebraicIndependent_X (GenIx r) Ω).map'
        (f := IsScalarTower.toAlgHom Ω (MvPolynomial (GenIx r) Ω) (GenField Ω r))
        (IsFractionRing.injective (MvPolynomial (GenIx r) Ω) (GenField Ω r))
    have hfam : (fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} =>
        genU Ω r q.1 q.2.1.1 q.2.1.2) =
        fun q => algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q) :=
      funext fun q => genU_below q.1 q.2.1.1 q.2.1.2 q.2.2
    rw [hfam]
    exact hai
  · rw [genField_adjoin_eq_top]
    exact IntermediateField.finrank_top

end GlobalTheory.CompanionTheory.Ar.FlagBun
