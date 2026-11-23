import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteExtGeomIntegralLocalization

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory.TensorFields

theorem exists_finset_lift {k κ K : Type} [Field k] [Field κ] [Field K] [Algebra k κ] [Algebra k K]
    (x : κ ⊗[k] K) : ∃ S : Finset K, ∀ T : Finset K, S ⊆ T →
      ∃ x' : κ ⊗[k] (Algebra.adjoin k (T : Set K)),
        Algebra.TensorProduct.map (AlgHom.id k κ) (Algebra.adjoin k (T : Set K)).val x' = x := by
  classical
  obtain ⟨P, rfl⟩ := TensorProduct.exists_finset x
  refine ⟨P.image Prod.snd, fun T hT => ?_⟩
  refine ⟨∑ i ∈ P.attach, i.1.1 ⊗ₜ[k] (⟨i.1.2, Algebra.subset_adjoin
    (hT (Finset.mem_image_of_mem Prod.snd i.2))⟩ : Algebra.adjoin k (T : Set K)), ?_⟩
  rw [map_sum]
  simp only [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, Subalgebra.coe_val]
  exact Finset.sum_attach P (fun i => i.1 ⊗ₜ[k] i.2)

theorem isDomain_tensor_complex : ∀ (K κ : Type) [Field K] [Field κ] [Algebra ℂ K] [Algebra ℂ κ],
    IsDomain (K ⊗[ℂ] κ) := by
  classical
  intro K κ _ _ _ _
  suffices h : IsDomain (κ ⊗[ℂ] K) from (Algebra.TensorProduct.comm ℂ K κ).toMulEquiv.isDomain
  haveI : Nontrivial (κ ⊗[ℂ] K) := inferInstance
  refine @NoZeroDivisors.to_isDomain _ _ _ ⟨fun {x y} hxy => ?_⟩
  obtain ⟨S₁, h₁⟩ := exists_finset_lift (k := ℂ) x
  obtain ⟨S₂, h₂⟩ := exists_finset_lift (k := ℂ) y
  let A := Algebra.adjoin ℂ ((S₁ ∪ S₂ : Finset K) : Set K)
  obtain ⟨x', hx'⟩ := h₁ (S₁ ∪ S₂) Finset.subset_union_left
  obtain ⟨y', hy'⟩ := h₂ (S₁ ∪ S₂) Finset.subset_union_right
  haveI : Algebra.FiniteType ℂ A := ⟨(Subalgebra.fg_top _).mpr (Subalgebra.fg_adjoin_finset _)⟩
  haveI : IsDomain A := inferInstance
  haveI : IsDomain (κ ⊗[ℂ] A) := GlobalTheory.GeomComp.isDomain_tensor_of_isAlgClosed ℂ A κ
  let φ := Algebra.TensorProduct.map (AlgHom.id ℂ κ) A.val
  have hφ : Function.Injective φ :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := κ) A.val.toLinearMap Subtype.val_injective
  have h0 : x' * y' = 0 := hφ (by rw [map_mul, hx', hy', hxy, map_zero])
  rcases mul_eq_zero.mp h0 with h | h
  · left; rw [← hx', h, map_zero]
  · right; rw [← hy', h, map_zero]

end GlobalTheory.TensorFields
