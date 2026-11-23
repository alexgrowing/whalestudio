import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

noncomputable section

namespace GlobalTheory.PolyTensor

theorem curry_sum_mapDomain {ι β : Type} [Fintype ι] (v : ι → (β →₀ ℕ)) (τ : ι) :
    (∑ σ, Finsupp.mapDomain (fun x => (σ, x)) (v σ)).curry τ = v τ := by
  classical
  ext x
  rw [Finsupp.curry_apply, Finsupp.finset_sum_apply, Finset.sum_eq_single τ]
  · exact Finsupp.mapDomain_apply (fun a b h => (Prod.mk.inj h).2) (v τ) x
  · intro σ _ hσ
    apply Finsupp.mapDomain_notin_range
    rintro ⟨y, hy⟩
    exact hσ (congrArg Prod.fst hy)
  · intro h
    exact absurd (Finset.mem_univ τ) h

def expEquiv (ι σ : Type) [Fintype ι] : (ι → (σ →₀ ℕ)) ≃ (ι × σ →₀ ℕ) :=
  Equiv.ofBijective (fun v => ∑ τ, Finsupp.mapDomain (fun x => (τ, x)) (v τ)) <| by
    classical
    refine ⟨fun v w h => funext fun τ => ?_, fun m => ⟨fun τ => m.curry τ, ?_⟩⟩
    · rw [← curry_sum_mapDomain v τ, ← curry_sum_mapDomain w τ]
      exact congrArg (fun m : ι × σ →₀ ℕ => m.curry τ) h
    · ext ⟨τ, x⟩
      have := DFunLike.congr_fun (curry_sum_mapDomain (fun τ => m.curry τ) τ) x
      simpa only [Finsupp.curry_apply] using this

theorem exists_piTensor_equiv : ∀ (ι σ : Type) [Fintype ι],
    ∃ e : (⨂[ℂ] _ : ι, MvPolynomial σ ℂ) ≃ₗ[ℂ] MvPolynomial (ι × σ) ℂ,
      ∀ f : ι → MvPolynomial σ ℂ,
        e (PiTensorProduct.tprod ℂ f) = ∏ τ, rename (Prod.mk τ) (f τ) := by
  intro ι σ _
  classical
  let bT := Basis.piTensorProduct (fun _ : ι => MvPolynomial.basisMonomials σ ℂ)
  let e : (⨂[ℂ] _ : ι, MvPolynomial σ ℂ) ≃ₗ[ℂ] MvPolynomial (ι × σ) ℂ :=
    bT.equiv (MvPolynomial.basisMonomials (ι × σ) ℂ) (expEquiv ι σ)

  have key : e.toLinearMap.compMultilinearMap (PiTensorProduct.tprod ℂ) =
      (MultilinearMap.mkPiAlgebra ℂ ι (MvPolynomial (ι × σ) ℂ)).compLinearMap
        (fun τ => (rename (Prod.mk τ) : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial (ι × σ) ℂ).toLinearMap) := by
    refine Module.Basis.ext_multilinear (fun _ => MvPolynomial.basisMonomials σ ℂ) fun v => ?_
    rw [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply, ← Basis.piTensorProduct_apply]
    change bT.equiv (MvPolynomial.basisMonomials (ι × σ) ℂ) (expEquiv ι σ) (bT v) = _
    rw [Module.Basis.equiv_apply]
    simp only [MvPolynomial.coe_basisMonomials, AlgHom.toLinearMap_apply,
      MvPolynomial.rename_monomial, expEquiv, Equiv.ofBijective_apply]
    exact MvPolynomial.monomial_sum_one _ _
  refine ⟨e, fun f => ?_⟩
  simpa using congrArg (fun F : MultilinearMap ℂ (fun _ : ι => MvPolynomial σ ℂ) _ => F f) key

end GlobalTheory.PolyTensor
