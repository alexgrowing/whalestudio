import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsThetaMeanSquareNorm
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSemiStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteAndFlatTorsion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHomExtensionSemiAbelianNormal
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpecMapFieldCancel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.CxPts GlobalTheory.Points
open scoped CategoryTheory.Obj
open GlobalTheory.MBLit GlobalTheory.MBModel

noncomputable section

namespace GlobalTheory.TorsRational

open Polynomial

theorem exists_ext_factor (K R : Type) [Field K] [CommRing R] [Algebra K R] [Module.Finite K R] :
    ∃ (K' : Type) (_ : Field K') (_ : Algebra K K'), Module.Finite K K' ∧
      ∀ (K'' Ω : Type) [Field K''] [Field Ω] [Algebra K' K''] [Algebra K K''] [IsScalarTower K K' K'']
        (σ : K'' →+* Ω) (φ : R →+* Ω), φ.comp (algebraMap K R) = σ.comp (algebraMap K K'') →
        ∃ φ'' : R →+* K'', σ.comp φ'' = φ := by
  classical
  let b := Module.finBasis K R
  let f : K[X] := ∏ i, minpoly K (b i)
  have hf0 : f ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ =>
    minpoly.ne_zero (Algebra.IsIntegral.isIntegral (b i))
  have hroot : ∀ r ∈ Set.range b, aeval r f = 0 := by
    rintro _ ⟨i, rfl⟩
    simp only [f, map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (minpoly.aeval K _)
  refine ⟨f.SplittingField, inferInstance, inferInstance, inferInstance, ?_⟩
  intro K'' Ω _ _ _ _ _ σ φ hφ
  have hs : (f.map (algebraMap K K'')).Splits := by
    rw [IsScalarTower.algebraMap_eq K f.SplittingField K'', ← Polynomial.map_map]
    exact (SplittingField.splits f).map _
  have hmem : ∀ r, φ r ∈ σ.range := by
    intro r
    have hr : r ∈ Submodule.span K (Set.range b) := b.span_eq ▸ Submodule.mem_top
    induction hr using Submodule.span_induction with
    | mem x hx =>
      refine hs.mem_range_of_isRoot (Polynomial.map_ne_zero hf0) ?_
      rw [Polynomial.map_map, ← hφ, Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.hom_eval₂,
        ← Polynomial.aeval_def, hroot x hx, map_zero]
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx =>
      rw [Algebra.smul_def, map_mul]
      refine mul_mem ⟨algebraMap K K'' c, ?_⟩ hx
      rw [← RingHom.comp_apply, ← hφ, RingHom.comp_apply]
  let e := RingEquiv.ofBijective σ.rangeRestrict
    ⟨fun a b h => σ.injective (congrArg Subtype.val h), σ.rangeRestrict_surjective⟩
  refine ⟨e.symm.toRingHom.comp (φ.codRestrict σ.range hmem), ?_⟩
  ext r
  exact congrArg Subtype.val (e.apply_symm_apply (φ.codRestrict σ.range hmem r))

theorem exists_ext_points (K : Type) [Field K] (T : Over (Sp K)) (hT : IsFinite T.hom) :
    ∃ (K' : Type) (_ : Field K') (_ : Algebra K K'), Module.Finite K K' ∧
      ∀ (K'' Ω : Type) [Field K''] [Field Ω] [Algebra K' K''] [Algebra K K''] [IsScalarTower K K' K'']
        (σ : K'' →+* Ω) (t : Sp Ω ⟶ T.left), t ≫ T.hom = spMap (σ.comp (algebraMap K K'')) →
        ∃ w : Sp K'' ⟶ T.left, spMap σ ≫ w = t := by
  haveI : IsAffine T.left := isAffine_of_isAffineHom T.hom
  obtain ⟨ρ, hρ⟩ := Spec.map_surjective (T.left.isoSpec.inv ≫ T.hom)
  letI : Algebra K Γ(T.left, ⊤) := ρ.hom.toAlgebra
  haveI : Module.Finite K Γ(T.left, ⊤) := by
    have : IsFinite (Spec.map ρ) := by rw [hρ]; infer_instance
    exact (IsFinite.SpecMap_iff ρ).1 this
  obtain ⟨K', _, _, hfin, H⟩ := exists_ext_factor K Γ(T.left, ⊤)
  refine ⟨K', _, _, hfin, fun K'' Ω _ _ _ _ _ σ t ht => ?_⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (t ≫ T.left.isoSpec.hom)
  have h1 : φ.hom.comp (algebraMap K Γ(T.left, ⊤)) = σ.comp (algebraMap K K'') := by
    have : Spec.map (ρ ≫ φ) = Spec.map (CommRingCat.ofHom (σ.comp (algebraMap K K''))) := by
      rw [Spec.map_comp, hφ, hρ, Category.assoc, Iso.hom_inv_id_assoc, ht]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
  obtain ⟨φ'', hφ''⟩ := H K'' Ω σ φ.hom h1
  refine ⟨Spec.map (CommRingCat.ofHom φ'') ≫ T.left.isoSpec.inv, ?_⟩
  have e : CommRingCat.ofHom φ'' ≫ CommRingCat.ofHom σ = φ := by
    ext r
    exact congrArg (fun g => g r) hφ''
  rw [← Category.assoc, spMap, ← Spec.map_comp, e, hφ, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end GlobalTheory.TorsRational
