import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory

theorem ambSpace_map_eq_sum {K : Type} [Field K] [NumberField K] [StarRing K] {σ : K →+* ℂ} (A : HLat K)
    {W : Type} [AddCommGroup W] [Module ℂ W] (j : A.V →ₛₗ[σ] W) (x : A.V) :
    j x = ∑ i, σ (A.b.repr x i) • j (A.b i) := by
  conv_lhs => rw [← A.b.sum_repr x]
  rw [map_sum]
  simp only [LinearMap.map_smulₛₗ]

private lemma exists_linearEquiv_euclidean_norm_eq_mulVec {ι W : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup W]
    [Module ℂ W] (bW : Module.Basis ι ℂ W) (N : Matrix ι ι ℂ) (hN : IsUnit N.det) :
    ∃ (n : ℕ) (g : W ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n)),
      ∀ w, ‖g w‖ = Real.sqrt (∑ i, ‖(N.mulVec (bW.equivFun w)) i‖ ^ 2) := by
  letI := Matrix.invertibleOfIsUnitDet N hN
  let e₂ : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ) := Matrix.toLinearEquiv' N this
  let e₃ : (ι → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ ι := (WithLp.linearEquiv 2 ℂ (ι → ℂ)).symm
  let e₄ : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (Fintype.card ι)) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Fintype.equivFin ι)
  refine ⟨Fintype.card ι, bW.equivFun.trans (e₂.trans (e₃.trans e₄.toLinearEquiv)), fun w => ?_⟩
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.norm_map, EuclideanSpace.norm_eq]
  rfl

theorem exists_equiv_normAt_eq_norm : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (A : HLat K) (W : Type) [AddCommGroup W] [Module ℂ W] (j : A.V →ₛₗ[σ] W), (∀ v, IsUnit (A.X v).det) → LinearIndependent ℂ (fun i => j (A.b i)) → Submodule.span ℂ (Set.range fun i => j (A.b i)) = ⊤ → ∃ (n : ℕ) (g : W ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n)), ∀ x, Formalism.HermitianLatticesTheory.normAt A.b A.X (InfinitePlace.mk σ) x = ‖g (j x)‖ := by
  intro K _ _ _ σ A W _ _ j hX hli hsp
  let bW : Module.Basis A.ι ℂ W := Module.Basis.mk hli (by rw [hsp])
  have hc : ∀ x, bW.equivFun (j x) = fun i => σ (A.b.repr x i) := by
    intro x
    have hx : j x = bW.equivFun.symm (fun i => σ (A.b.repr x i)) := by
      rw [Module.Basis.equivFun_symm_apply, ambSpace_map_eq_sum]
      simp [bW, Module.Basis.mk_apply]
    rw [hx, LinearEquiv.apply_symm_apply]
  have hU : IsUnit ((A.X (InfinitePlace.mk σ))⁻¹).det := Matrix.isUnit_nonsing_inv_det _ (hX _)
  have hv : ∀ x, Formalism.HermitianLatticesTheory.vecAt A.b (InfinitePlace.mk σ) x =
      fun i => (InfinitePlace.mk σ).embedding (A.b.repr x i) := fun x => rfl
  rcases InfinitePlace.embedding_mk_eq σ with h | h
  · obtain ⟨n, g, hg⟩ := exists_linearEquiv_euclidean_norm_eq_mulVec bW (A.X (InfinitePlace.mk σ))⁻¹ hU
    refine ⟨n, g, fun x => ?_⟩
    rw [hg, hc]
    simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, Formalism.HermitianLatticesTheory.fcoord, hv, h]
  · have hU' : IsUnit (((A.X (InfinitePlace.mk σ))⁻¹).map (starRingEnd ℂ)).det := by
      have e : (((A.X (InfinitePlace.mk σ))⁻¹).map (starRingEnd ℂ)).det =
          starRingEnd ℂ ((A.X (InfinitePlace.mk σ))⁻¹).det := (RingHom.map_det _ _).symm
      rw [e]
      exact hU.map _
    obtain ⟨n, g, hg⟩ := exists_linearEquiv_euclidean_norm_eq_mulVec bW (((A.X (InfinitePlace.mk σ))⁻¹).map (starRingEnd ℂ)) hU'
    refine ⟨n, g, fun x => ?_⟩
    rw [hg, hc]
    simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, Formalism.HermitianLatticesTheory.fcoord, hv, h]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [← Complex.norm_conj]
    congr 1
    simp [Matrix.mulVec, dotProduct, map_sum, ComplexEmbedding.conjugate_coe_eq]

end GlobalTheory
