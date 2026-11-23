import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.EigBoxE
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.RankInvTBox

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open UpperTheory.V.Z.J.D
open scoped Matrix TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Z.Desc.V0

section Abs

variable {G W W' : Type} [Group G] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

private theorem map_mem_isotypic_invariants {m : ℕ} (K₁ : Subgroup G) (τ₀ : K₁ →* GL (Fin m) ℂ)
    (ρ : Representation ℂ G W) (ρ' : Representation ℂ G W') (e : W →ₗ[ℂ] W')
    (h₁ : ∀ k ∈ K₁, ∀ x, e (ρ k x) = ρ' k (e x))
    {F : Fin m → W} (hF : F ∈ inv1 K₁ τ₀ ρ) : (fun i => e (F i)) ∈ inv1 K₁ τ₀ ρ' := by
  refine ⟨fun k i => ?_, fun k _ i => ?_⟩
  · have h := congrArg e (hF.1 k i)
    simp only [map_sum, map_smul, MonoidHom.comp_apply, MonoidHom.coe_fst, h₁ k.1 k.2] at h
    simpa only [MonoidHom.comp_apply, MonoidHom.coe_fst] using h
  · simp

private theorem rank_isotypic_invariants_eq {m : ℕ} (K₁ : Subgroup G) (τ₀ : K₁ →* GL (Fin m) ℂ)
    (ρ : Representation ℂ G W) (ρ' : Representation ℂ G W') (e : W ≃ₗ[ℂ] W')
    (h₁ : ∀ k ∈ K₁, ∀ x, e (ρ k x) = ρ' k (e x)) :
    Module.rank ℂ (inv1 K₁ τ₀ ρ) = Module.rank ℂ (inv1 K₁ τ₀ ρ') := by
  have s₁ : ∀ k ∈ K₁, ∀ x, e.symm (ρ' k x) = ρ k (e.symm x) := fun k hk x =>
    e.injective (by rw [h₁ k hk, e.apply_symm_apply, e.apply_symm_apply])
  let E : (Fin m → W) ≃ₗ[ℂ] (Fin m → W') := LinearEquiv.piCongrRight fun _ => e
  have hE : (inv1 K₁ τ₀ ρ).map (E : (Fin m → W) →ₗ[ℂ] (Fin m → W')) = inv1 K₁ τ₀ ρ' := by
    refine le_antisymm ?_ fun F hF => ?_
    · rintro _ ⟨F, hF, rfl⟩
      exact map_mem_isotypic_invariants K₁ τ₀ ρ ρ' e.toLinearMap h₁ hF
    · refine ⟨fun i => e.symm (F i), map_mem_isotypic_invariants K₁ τ₀ ρ' ρ e.symm.toLinearMap s₁ hF, ?_⟩
      funext i
      exact e.apply_symm_apply (F i)
  exact (LinearEquiv.ofSubmodules E _ _ hE).rank_eq

end Abs

section Fam

variable {I : Type} {Gi Wi Wi' : I → Type} [∀ i, Group (Gi i)]
  [∀ i, AddCommGroup (Wi i)] [∀ i, Module ℂ (Wi i)] [∀ i, AddCommGroup (Wi' i)] [∀ i, Module ℂ (Wi' i)]

private theorem congr_piRep (τ : ∀ i, Representation ℂ (Gi i) (Wi i)) (τ' : ∀ i, Representation ℂ (Gi i) (Wi' i))
    (a : ∀ i, Wi i ≃ₗ[ℂ] Wi' i) (g : ∀ i, Gi i) (h : ∀ i x, a i (τ i (g i) x) = τ' i (g i) (a i x))
    (x : ⨂[ℂ] i, Wi i) : PiTensorProduct.congr a (piRep τ g x) = piRep τ' g (PiTensorProduct.congr a x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    simp only [piRep, PiTensorProduct.congr, map_smul, MonoidHom.comp_apply, PiTensorProduct.mapMonoidHom_apply, LinearEquiv.ofLinear_apply, PiTensorProduct.map_tprod]
    exact congrArg (fun t => r • PiTensorProduct.tprod ℂ t) (funext fun i => h i (f i))
  | add x y hx hy => simp only [map_add, hx, hy]

end Fam

theorem invEq1 : InvEq1 := by
  intro l _ L Ω _ _ _ _ _ _ s n _ V _ c ι m τ₀ σ σ' C C' hu
  refine rank_isotypic_invariants_eq (KT n (wt s)) _ _ _ (PiTensorProduct.congr fun u => (hu u).some.toLinearEquiv) ?_
  intro g hg x
  refine congr_piRep _ _ _ g (fun u y => ?_) x
  exact LinearMap.congr_fun ((hu u).some.isIntertwining' ⟨g u, hg u (Set.mem_univ u)⟩) y

end UpperTheory.V.Z.Desc.V0
