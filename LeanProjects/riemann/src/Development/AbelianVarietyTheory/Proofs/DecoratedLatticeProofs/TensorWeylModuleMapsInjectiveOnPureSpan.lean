import Mathlib
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalizedFockFormPureTensorProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TensorTypesRealPlacesEquivSpanWeylModules
open Formalism.BasicNotions Formalism.L2.Forms
open scoped TensorProduct

namespace GlobalTheory.TenInj

noncomputable def tenMap {ι : Type} [Fintype ι] {n : ℕ} {V : ι → Type} [∀ τ, AddCommGroup (V τ)] [∀ τ, Module ℂ (V τ)]
    (j : ∀ τ, V τ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ) :
    (⨂[ℂ] τ, V τ) →ₗ[ℂ] MvPolynomial (ι × Fin n × Fin n) ℂ :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι (MvPolynomial (ι × Fin n × Fin n) ℂ)).compLinearMap
    (fun τ => (MvPolynomial.rename (Prod.mk τ)).toLinearMap ∘ₗ j τ))

theorem tenMap_tprod {ι : Type} [Fintype ι] {n : ℕ} {V : ι → Type} [∀ τ, AddCommGroup (V τ)] [∀ τ, Module ℂ (V τ)]
    (j : ∀ τ, V τ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ) (x : ∀ τ, V τ) :
    tenMap j (PiTensorProduct.tprod ℂ x) = ten (fun τ => j τ (x τ)) := by
  unfold tenMap ten
  rw [PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]
  rfl

theorem nfAll_zero_left {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (q : MvPolynomial (ι × Fin n × Fin n) ℂ) : nfAll lam 0 q = 0 := by
  have h := GlobalTheory.TenTypes.nfAll_smul_left lam 0 0 q
  simpa using h

theorem main : ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (V : ι → Type) [∀ τ, AddCommGroup (V τ)] [∀ τ, Module ℂ (V τ)] (j : ∀ τ, V τ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ) (d : ι → ℕ) (b : ∀ τ, Module.Basis (Fin (d τ)) ℂ (V τ)), (∀ τ ξ, j τ ξ ∈ delSq ℂ n (lam τ)) → (∀ τ, ∀ p ∈ delSq ℂ n (lam τ), ∃ ξ, j τ ξ = p) → (∀ τ a a', normFock (lam τ) (j τ (b τ a)) (j τ (b τ a')) = if a = a' then 1 else 0) → ∃ Jt : (⨂[ℂ] τ, V τ) →ₗ[ℂ] MvPolynomial (ι × Fin n × Fin n) ℂ, Function.Injective Jt ∧ LinearMap.range Jt = CSpan lam ∧ ∀ x : (∀ τ, V τ), Jt (PiTensorProduct.tprod ℂ x) = ten (fun τ => j τ (x τ)) := by
  intro ι _ n lam V _ _ j d b hin hon hortho
  refine ⟨tenMap j, ?_, ?_, tenMap_tprod j⟩
  ·
    let B := Basis.piTensorProduct b
    have hB : ∀ i, B i = PiTensorProduct.tprod ℂ (fun τ => b τ (i τ)) := fun i => Basis.piTensorProduct_apply b i
    obtain ⟨hprod, -, -⟩ := GlobalTheory.FockTen.nfAll_ten ι n lam
    have hpair : ∀ i i', nfAll lam (tenMap j (B i)) (tenMap j (B i')) = if i = i' then 1 else 0 := by
      intro i i'
      rw [hB, hB, tenMap_tprod, tenMap_tprod, hprod]
      simp_rw [hortho]
      by_cases h : i = i'
      · subst h; simp
      · rw [if_neg h]
        obtain ⟨τ, hτ⟩ : ∃ τ, i τ ≠ i' τ := by
          by_contra hc; push_neg at hc; exact h (funext hc)
        exact Finset.prod_eq_zero (Finset.mem_univ τ) (if_neg hτ)
    have hcoord : ∀ i' x, nfAll lam (tenMap j x) (tenMap j (B i')) = B.coord i' x := by
      intro i'
      let L : (⨂[ℂ] τ, V τ) →ₗ[ℂ] ℂ :=
        { toFun := fun x => nfAll lam (tenMap j x) (tenMap j (B i'))
          map_add' := fun x y => by rw [map_add, GlobalTheory.TenTypes.nfAll_add_left]
          map_smul' := fun c x => by rw [map_smul, GlobalTheory.TenTypes.nfAll_smul_left]; rfl }
      have hL : L = B.coord i' := by
        refine B.ext fun i => ?_
        show nfAll lam (tenMap j (B i)) (tenMap j (B i')) = B.coord i' (B i)
        rw [hpair, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      intro x
      exact LinearMap.congr_fun hL x
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    refine B.ext_elem fun i' => ?_
    rw [map_zero, Finsupp.zero_apply, ← Module.Basis.coord_apply, ← hcoord, hx, nfAll_zero_left]
  ·
    rw [LinearMap.range_eq_map, ← PiTensorProduct.span_tprod_eq_top, Submodule.map_span]
    unfold CSpan
    congr 1
    ext p
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨fun τ => j τ (x τ), fun τ => hin τ _, tenMap_tprod j x⟩
    · rintro ⟨f, hf, rfl⟩
      choose ξ hξ using fun τ => hon τ (f τ) (hf τ)
      refine ⟨PiTensorProduct.tprod ℂ ξ, ⟨ξ, rfl⟩, ?_⟩
      rw [tenMap_tprod]
      congr 1
      funext τ
      exact hξ τ

end GlobalTheory.TenInj
