import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModificationLineBundleGlobalSectionsDimPullEq

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open scoped TensorProduct

namespace GlobalTheory.GeomIntConst

theorem finrank_eq_one_of_isDomain_tensor {F L : Type} [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] [IsDomain (L ⊗[F] L)] : Module.finrank F L = 1 := by
  have hinj : Function.Injective (algebraMap L (L ⊗[F] L)) := (algebraMap L (L ⊗[F] L)).injective
  have hT : IsField (L ⊗[F] L) :=
    (Algebra.IsIntegral.isField_iff_isField hinj).1 (Field.toIsField L)
  let f : L ⊗[F] L →ₐ[L] L := Algebra.TensorProduct.lmul'' F
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h
    obtain ⟨y, hy⟩ := hT.mul_inv_cancel h
    have := congrArg f hy
    rw [map_mul, hx, zero_mul, map_one] at this
    exact zero_ne_one this
  have hs : Function.Surjective f := fun x => ⟨x ⊗ₜ 1, by
    show Algebra.TensorProduct.lmul'' F (x ⊗ₜ[F] (1 : L)) = x
    first
      | simp [Algebra.TensorProduct.lmul''_apply_tmul]
      | exact (Algebra.TensorProduct.lmul'_apply_tmul (R := F) x (1 : L)).trans (mul_one x)⟩
  have e := (LinearEquiv.ofBijective f.toLinearMap ⟨hf, hs⟩).finrank_eq
  rw [Module.finrank_baseChange, Module.finrank_self] at e
  exact e

theorem mem_range_constFn (F : Type) [Field F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F)
    [GeometricallyIntegral p] (b : Y.functionField)
    (hb : ∃ P : Polynomial F, P ≠ 0 ∧ P.eval₂ (GlobalTheory.Cartier.constFn p) b = 0) :
    b ∈ (GlobalTheory.Cartier.constFn p).range := by
  letI : Algebra F Y.functionField := (GlobalTheory.Cartier.constFn p).toAlgebra
  obtain ⟨P, hP, hPb⟩ := hb
  have hint : IsIntegral F b := (show IsAlgebraic F b from ⟨P, hP, hPb⟩).isIntegral
  obtain ⟨V, hV, s₀, hs₀⟩ := Y.presheaf.exists_germ_eq b
  obtain ⟨U, hU, hxU, hUV⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hV
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  let s : Γ(Y, U) := resG Y hUV s₀
  have hs : GlobalTheory.Cartier.fnOf U hxU s = b := by
    rw [GlobalTheory.Cartier.fnOf_resG]; exact hs₀
  letI : Algebra F Γ(Y, U) := (algX p U).toAlgebra
  have e : (GlobalTheory.Cartier.fnOf U hxU).comp (algebraMap F Γ(Y, U)) = algebraMap F Y.functionField :=
    GlobalTheory.Cartier.fnOf_comp_algX p U hxU
  have hm : Polynomial.aeval s (minpoly F b) = 0 := by
    apply GlobalTheory.Cartier.fnOf_injective U hxU
    rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂, e, hs, ← Polynomial.aeval_def,
      minpoly.aeval]
  haveI : Fact (Irreducible (minpoly F b)) := ⟨minpoly.irreducible hint⟩
  let φ : AdjoinRoot (minpoly F b) →ₐ[F] Γ(Y, U) := AdjoinRoot.liftAlgHom (minpoly F b) (Algebra.ofId F Γ(Y, U)) s
    (by rw [Polynomial.aeval_def] at hm; exact hm)
  have hφ : Function.Injective φ := φ.toRingHom.injective

  let g := Spec.map (CommRingCat.ofHom (algebraMap F (AdjoinRoot (minpoly F b))))
  have hg : hU.fromSpec ≫ p = Spec.map (CommRingCat.ofHom (algebraMap F Γ(Y, U))) := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top _) hU
      (show U ≤ p ⁻¹ᵁ ⊤ from le_top)
    rw [← h, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  have hYL : IsIntegral (pullback p g) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (IsPullback.of_hasPullback p g)
  have : Surjective g := ⟨fun x => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  have : Nonempty ((pullback hU.fromSpec (pullback.fst p g) : Scheme.{0})) := by
    obtain ⟨z, -⟩ : genericPoint Y ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hxU
    have hz : z ∈ Set.range (pullback.fst hU.fromSpec (pullback.fst p g)) := by
      rw [Scheme.Pullback.range_fst]; exact (pullback.fst p g).surjective _
    exact ⟨hz.choose⟩
  haveI := hU.isOpenImmersion_fromSpec
  have : IsIntegral (pullback hU.fromSpec (pullback.fst p g)) :=
    isIntegral_of_isOpenImmersion (pullback.snd hU.fromSpec (pullback.fst p g))
  have : IsIntegral (pullback (hU.fromSpec ≫ p) g) :=
    IsIntegral.of_isIso (pullbackRightPullbackFstIso p g hU.fromSpec).hom
  rw [hg] at this
  have : IsIntegral (Spec (.of (Γ(Y, U) ⊗[F] AdjoinRoot (minpoly F b)))) :=
    IsIntegral.of_isIso (pullbackSpecIso F Γ(Y, U) (AdjoinRoot (minpoly F b))).hom
  have : IsDomain (Γ(Y, U) ⊗[F] AdjoinRoot (minpoly F b)) :=
    (affine_isIntegral_iff (.of (Γ(Y, U) ⊗[F] AdjoinRoot (minpoly F b)))).mp this

  have hinj : Function.Injective (Algebra.TensorProduct.map φ
      (AlgHom.id F (AdjoinRoot (minpoly F b)))) :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := AdjoinRoot (minpoly F b))
      φ.toLinearMap hφ
  have : IsDomain (AdjoinRoot (minpoly F b) ⊗[F] AdjoinRoot (minpoly F b)) :=
    Function.Injective.isDomain (Algebra.TensorProduct.map φ
      (AlgHom.id F (AdjoinRoot (minpoly F b)))).toRingHom hinj
  have hm0 : minpoly F b ≠ 0 := minpoly.ne_zero hint
  have : FiniteDimensional F (AdjoinRoot (minpoly F b)) := (AdjoinRoot.powerBasis hm0).finite
  have h1 := finrank_eq_one_of_isDomain_tensor (F := F) (L := AdjoinRoot (minpoly F b))
  rw [(AdjoinRoot.powerBasis hm0).finrank, AdjoinRoot.powerBasis_dim] at h1
  exact minpoly.natDegree_eq_one_iff.1 h1

end GlobalTheory.GeomIntConst
