import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem trace_map_eq_prod {s : ℕ} {W : Fin s → Type} [∀ a, AddCommGroup (W a)]
    [∀ a, Module ℂ (W a)] [∀ a, FiniteDimensional ℂ (W a)] (f : ∀ a, W a →ₗ[ℂ] W a) :
    LinearMap.trace ℂ (PiTensorProduct ℂ W) (PiTensorProduct.map f) =
      ∏ a, LinearMap.trace ℂ (W a) (f a) := by
  let b := fun a => Module.finBasis ℂ (W a)
  let B := Basis.piTensorProduct b
  rw [LinearMap.trace_eq_matrix_trace ℂ B]
  have hc : ∀ a, LinearMap.trace ℂ (W a) (f a) = ∑ j, (b a).repr (f a (b a j)) j := by
    intro a
    rw [LinearMap.trace_eq_matrix_trace ℂ (b a), Matrix.trace]
    simp only [Matrix.diag, LinearMap.toMatrix_apply]
  simp only [hc]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Matrix.trace]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.diag, LinearMap.toMatrix_apply, Basis.piTensorProduct_apply, PiTensorProduct.map_tprod,
    Basis.piTensorProduct_repr_tprod_apply]

theorem UpperTheory.Gal.InertialTypesAlt.tensTr :
    TensTr := by
  intro s Γ W _ _ _ _ κ
  refine ⟨Module.Finite.of_basis (Basis.piTensorProduct fun a => Module.finBasis ℂ (W a)), fun x => ?_⟩
  exact trace_map_eq_prod fun a => κ a (x a)
