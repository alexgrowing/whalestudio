import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

open scoped TensorProduct

namespace GlobalTheory

theorem exists_finite_ext_compat_of_finite :
    ∀ (k K k₁ : Type) [Field k] [Field K] [Field k₁] [Algebra k K] [Algebra k k₁] [FiniteDimensional k k₁], ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K') (e : k₁ →+* K'), e.comp (algebraMap k k₁) = (algebraMap K K').comp (algebraMap k K) := by
  intro k K k₁ _ _ _ _ _ _
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[k] k₁)
  letI : Field ((K ⊗[k] k₁) ⧸ m) := Ideal.Quotient.field m
  have hfin : FiniteDimensional K ((K ⊗[k] k₁) ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K m).toLinearMap
      (Ideal.Quotient.mkₐ_surjective K m)
  refine ⟨(K ⊗[k] k₁) ⧸ m, inferInstance, inferInstance, hfin,
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeRight : k₁ →ₐ[k] K ⊗[k] k₁).toRingHom, ?_⟩
  ext a
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    Algebra.TensorProduct.includeRight_apply, Ideal.Quotient.algebraMap_eq]
  rw [IsScalarTower.algebraMap_apply K (K ⊗[k] k₁) ((K ⊗[k] k₁) ⧸ m),
    Algebra.TensorProduct.algebraMap_apply]
  congr 1
  rw [← Algebra.TensorProduct.algebraMap_apply', ← Algebra.TensorProduct.algebraMap_apply]
  exact IsScalarTower.algebraMap_apply k K (K ⊗[k] k₁) a

end GlobalTheory
