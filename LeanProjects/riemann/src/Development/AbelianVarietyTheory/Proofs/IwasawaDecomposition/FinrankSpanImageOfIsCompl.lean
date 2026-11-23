import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsExtendResidue
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsIsComplEigenSubOfValuationRing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DetCondTensorDefinite

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.EigenSplit GlobalTheory.HTLat GlobalTheory.TotalFrame GlobalTheory.FlagPts
open scoped TensorProduct

namespace GlobalTheory.RedRank

theorem finrank_span_image_of_isCompl {R S M M' : Type*} [CommRing R] [Nontrivial R] [Field S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] [Module S M'] [IsScalarTower R S M']
    {g : M →ₗ[R] M'} (hb : IsBaseChange S g) {P Q : Submodule R M} (hPQ : IsCompl P Q)
    [Module.Free R P] [Module.Finite R P] :
    Module.finrank S (Submodule.span S (g '' P)) = Module.finrank R P := by
  let φ : S ⊗[R] P →ₗ[S] M' := (g ∘ₗ P.subtype).liftBaseChange S
  let π := P.linearProjOfIsCompl Q hPQ
  have hφ : Function.Injective φ := by
    refine Function.LeftInverse.injective (g := (π.baseChange S) ∘ₗ hb.equiv.symm.toLinearMap) fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s y =>
      have h1 : hb.equiv.symm (g y) = (1 : S) ⊗ₜ[R] (y : M) := by
        rw [LinearEquiv.symm_apply_eq, IsBaseChange.equiv_tmul, one_smul]
      simp [φ, h1, π, TensorProduct.smul_tmul']
      exact congrArg (s ⊗ₜ[R] ·) (Submodule.linearProjOfIsCompl_apply_left hPQ y)
    | add x y hx hy => simp only [map_add, LinearMap.comp_apply] at hx hy ⊢; rw [hx, hy]
  have hr : LinearMap.range φ = Submodule.span S (g '' P) := by
    refine le_antisymm ?_ (Submodule.span_le.2 ?_)
    · rintro _ ⟨x, rfl⟩
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul s y => simpa [φ] using Submodule.smul_mem _ s (Submodule.subset_span (Set.mem_image_of_mem g y.2))
      | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    · rintro _ ⟨y, hy, rfl⟩
      exact LinearMap.mem_range.2 ⟨(1 : S) ⊗ₜ[R] (⟨y, hy⟩ : P), by simp [φ]⟩
  rw [← hr, LinearMap.finrank_range_of_inj hφ, Module.finrank_baseChange]

end GlobalTheory.RedRank

open GlobalTheory.EigenSplit in

theorem GlobalTheory.LocM.At.finrank_eigBar : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (p : ℕ) (ct : At S κ p),
    ∀ τ : PsiT D, Module.finrank ct.kbar (ct.eigBar τ) = N := by
  intro D A N j S κ p ct τ
  have := S.Dw.fin
  have := S.Dw.proj
  have : Module.Finite ℤ S.Dw.La := .trans (𝓞 D.host.E) _
  have : Module.Flat ℤ S.Dw.La := Module.Flat.trans ℤ (𝓞 D.host.E) S.Dw.La
  have : Module.Free ct.V₀ (ct.V₀ ⊗[ℤ] S.Dw.La) := Module.free_of_flat_of_isLocalRing
  let ρZ : 𝓞 D.host.E →+* Module.End ℤ S.Dw.La := Module.toModuleEnd ℤ S.Dw.La
  obtain ⟨Q, hQ⟩ := exists_isCompl_eigenSub_of_valuationRing (baseChangeAction ct.V₀ ρZ) (embV κ.c ct.W (embOf D τ))
  have := free_eigenSub_of_valuationRing (baseChangeAction ct.V₀ ρZ) (embV κ.c ct.W (embOf D τ))
  have := finite_eigenSub_of_valuationRing (baseChangeAction ct.V₀ ρZ) (embV κ.c ct.W (embOf D τ))
  have hg : ∀ x, ct.redLa x = extendTensor ℤ ct.V₀ ct.kbar S.Dw.La x := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact (map_zero _).symm
    | tmul r a => rfl
    | add x y hx hy => rw [map_add, hx, hy]; exact (map_add _ x y).symm
  have h0 : Module.finrank ct.kbar (ct.eigBar τ) =
      Module.finrank ct.V₀ (eigenSub (baseChangeAction ct.V₀ ρZ) (embV κ.c ct.W (embOf D τ))) := by
    rw [At.eigBar, show (ct.redLa : _ → _) = extendTensor ℤ ct.V₀ ct.kbar S.Dw.La from funext hg]
    exact GlobalTheory.RedRank.finrank_span_image_of_isCompl
      (P := eigenSub (baseChangeAction ct.V₀ ρZ) (embV κ.c ct.W (embOf D τ))) (isBaseChange_extendTensor ℤ ct.V₀ ct.kbar S.Dw.La) hQ
  letI : Algebra ct.V₀ ℂ := ((algebraMap κ.c.F ℂ).comp (algebraMap ct.V₀ κ.c.F)).toAlgebra
  have hσ : Function.Injective fun σ : D.host.E →+* ℂ => embV κ.c ct.W σ := fun σ σ' h =>
    IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 D.host.E))
      (RingHom.ext fun a => congrArg (fun f : 𝓞 D.host.E →+* ct.V₀ => (((f a : ct.V₀) : κ.c.F) : ℂ)) h)
  have h1 := finrank_eigenSub_of_charZero (E := D.host.E) (A := ct.V₀) (N := ct.V₀ ⊗[ℤ] S.Dw.La)
    (ρ := baseChangeAction ct.V₀ ρZ) (M := ℂ ⊗[ℤ] S.Dw.La)
    (ρ' := baseChangeAction (ℂ) ρZ)
    (f := extendTensor ℤ ct.V₀ (ℂ) S.Dw.La) (S := ℂ) hσ (NumberField.Embeddings.card D.host.E ℂ)
    (extendTensor_equivariant ct.V₀ (ℂ) ρZ) (isBaseChange_extendTensor ℤ ct.V₀ (ℂ) S.Dw.La) (embOf D τ)
  have h2 := GlobalTheory.TensorDet.finrank_eigenSub (O := ℤ) (M := S.Dw.La) (k := ℂ)
    ((algebraMap ct.V₀ (ℂ)).comp (embV κ.c ct.W (embOf D τ))) (RingHom.ext_int _ _)
  have h3 : GlobalTheory.TensorDet.rightAction (ℂ) ℤ (𝓞 D.host.E) S.Dw.La = baseChangeAction (ℂ) ρZ := by
    ext a : 1
    rw [GlobalTheory.TensorDet.rightAction_apply, baseChangeAction_apply]
    rfl
  rw [h3, h1, S.Dw.rank, S.rank_eq] at h2
  rw [h0, h2]
