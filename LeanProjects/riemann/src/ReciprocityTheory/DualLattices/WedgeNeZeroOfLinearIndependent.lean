import ReciprocityTheory.DualLattices.SmallLevelClassSet

noncomputable section

open Module Submodule

namespace ReciprocityTheory.PGsh

attribute [local instance] extModR

section Wedge

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem wedge_eq_det_smul_basis {k : ℕ} {W : Submodule K V} (bW : Basis (Fin k) K W) (w : Fin k → W) :
    ExteriorAlgebra.ιMulti K k (fun j => (w j : V)) =
      bW.det w • ExteriorAlgebra.ιMulti K k (fun j => (bW j : V)) := by
  let f := (ExteriorAlgebra.ιMulti K k).compLinearMap W.subtype
  have key : ∀ ψ : Module.Dual K (ExteriorAlgebra K V), ψ (f w) = ψ (bW.det w • f bW) := by
    intro ψ
    have h := AlternatingMap.eq_smul_basis_det bW (ψ.compAlternatingMap f)
    have := congrArg (fun g => g w) h
    simp only [LinearMap.compAlternatingMap_apply, AlternatingMap.smul_apply, smul_eq_mul] at this
    rw [this, map_smul, smul_eq_mul, mul_comm]
  have : f w - bW.det w • f bW = 0 := by
    rw [← Module.forall_dual_apply_eq_zero_iff K]
    intro ψ; rw [map_sub, key, sub_self]
  exact sub_eq_zero.mp this

theorem exists_wedge_eq_integral_smul {R : Type*} [CommRing R] [Algebra R K] [Module R V] [IsScalarTower R K V]
    {k : ℕ} {b w : Fin k → V} (hb : LinearIndependent K b)
    (hw : ∀ j, w j ∈ span R (Set.range b)) :
    ∃ r : R, ExteriorAlgebra.ιMulti K k w = algebraMap R K r • ExteriorAlgebra.ιMulti K k b := by
  have hw' : ∀ j, w j ∈ span K (Set.range b) := fun j => span_le_restrictScalars R K _ (hw j)
  choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun R).mp (hw j)
  let bW := Basis.span hb
  let w' : Fin k → span K (Set.range b) := fun j => ⟨w j, hw' j⟩
  have hw'eq : ∀ j, w' j = ∑ i, algebraMap R K (c j i) • bW i := by
    intro j; ext
    simp only [w', bW, Submodule.coe_sum, Submodule.coe_smul, Basis.span_apply, ← hc j]
    simp [algebraMap_smul]
  have hrepr : ∀ j i, bW.repr (w' j) i = algebraMap R K (c j i) := by
    intro j i
    rw [hw'eq j, map_sum]
    simp only [map_smul, Basis.repr_self, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
      Finsupp.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  refine ⟨(Matrix.of fun i j => c j i).det, ?_⟩
  have h1 := wedge_eq_det_smul_basis bW w'
  have hdet : bW.det w' = algebraMap R K (Matrix.of fun i j => c j i).det := by
    rw [Basis.det_apply, RingHom.map_det]
    congr 1; ext i j; simp [Basis.toMatrix_apply, hrepr]
  simpa [w', bW, Basis.span_apply, hdet] using h1

theorem wedge_ne_zero_of_linearIndependent {k : ℕ} {b : Fin k → V} (hb : LinearIndependent K b) :
    ExteriorAlgebra.ιMulti K k b ≠ 0 := by
  have h := (exteriorPower.ιMulti_family_linearIndependent_field (n := k) hb).ne_zero
    (Set.powersetCard.ofFinEmbEquiv (OrderIso.refl (Fin k)).toOrderEmbedding)
  intro h0; apply h
  apply Subtype.ext
  simpa [exteriorPower.ιMulti_family] using h0

variable {R : Type*} [CommRing R] [Algebra R K] [Module R V] [IsScalarTower R K V]

end Wedge

end ReciprocityTheory.PGsh
