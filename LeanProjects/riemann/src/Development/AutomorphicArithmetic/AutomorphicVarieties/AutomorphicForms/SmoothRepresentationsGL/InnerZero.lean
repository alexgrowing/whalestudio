import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb
import GroundTheory.AutomorphicForms.L2LocalComponents.Summand

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem exists_equiv_mod {M : Type} [AddCommGroup M] [Module ℂ M] (U U' D : Submodule ℂ M)
    (h : U ⊓ D = ⊥) (h' : U' ⊓ D = ⊥) (e : U ⊔ D = U' ⊔ D) :
    ∃ T : U ≃ₗ[ℂ] U', ∀ u, (T u).1 - u.1 ∈ D := by
  have inj : ∀ W : Submodule ℂ M, W ⊓ D = ⊥ → Function.Injective (D.mkQ ∘ₗ W.subtype) := fun W hW => by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    have hx' : x.1 ∈ W ⊓ D := ⟨x.2, (Submodule.Quotient.mk_eq_zero D).1 hx⟩
    rw [hW] at hx'
    exact Subtype.ext hx'
  have rg : ∀ W : Submodule ℂ M, LinearMap.range (D.mkQ ∘ₗ W.subtype) = (W ⊔ D).map D.mkQ := fun W => by
    rw [LinearMap.range_comp, Submodule.range_subtype, Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq]
  have er : LinearMap.range (D.mkQ ∘ₗ U.subtype) = LinearMap.range (D.mkQ ∘ₗ U'.subtype) := by
    rw [rg, rg, e]
  refine ⟨(LinearEquiv.ofInjective _ (inj U h)).trans
    ((LinearEquiv.ofEq _ _ er).trans (LinearEquiv.ofInjective _ (inj U' h')).symm), fun u => ?_⟩
  refine (Submodule.Quotient.eq D).1 ?_
  exact congrArg Subtype.val ((LinearEquiv.ofInjective _ (inj U' h')).apply_symm_apply
    (LinearEquiv.ofEq _ _ er (LinearEquiv.ofInjective _ (inj U h) u)))

private theorem iso_of_compl {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {n : ℕ} (π π' : CuspSub E n)
    (D : Submodule ℂ (TR.Sm E n)) (hD : TR.IsStable D) (h : π.V ⊓ D = ⊥) (h' : π'.V ⊓ D = ⊥)
    (hle : π'.V ≤ π.V ⊔ D) : π.Iso π' := by
  have hst : TR.IsStable (π.V ⊓ (π'.V ⊔ D)) := by
    rintro o φ ⟨h1, h2⟩
    refine ⟨π.stable o φ h1, ?_⟩
    obtain ⟨x, hx, d, hd, rfl⟩ := Submodule.mem_sup.1 h2
    rw [map_add]
    exact Submodule.add_mem_sup (π'.stable o x hx) (hD o d hd)
  have hge : π.V ≤ π'.V ⊔ D := by
    rcases π.irred _ inf_le_left hst with h0 | h0
    · refine absurd (eq_bot_iff.2 fun x hx => ?_) π'.ne_bot
      obtain ⟨u, hu, d, hd, rfl⟩ := Submodule.mem_sup.1 (hle hx)
      have hu' : u ∈ π.V ⊓ (π'.V ⊔ D) := ⟨hu, by
        have := Submodule.add_mem_sup hx (D.neg_mem hd)
        rwa [add_neg_cancel_right] at this⟩
      rw [h0, Submodule.mem_bot] at hu'
      rw [← h']
      refine ⟨hx, ?_⟩
      rw [hu', zero_add]
      exact hd
    · exact inf_eq_left.1 h0
  obtain ⟨T, hT⟩ := exists_equiv_mod π.V π'.V D h h'
    (le_antisymm (sup_le hge le_sup_right) (sup_le hle le_sup_right))
  refine ⟨T, fun o φ => Subtype.ext (sub_eq_zero.1 ?_)⟩
  rw [← Submodule.mem_bot ℂ, ← h']
  refine ⟨π'.V.sub_mem (T _).2 (π'.op o _).2, ?_⟩
  have h1 := D.sub_mem (hT (π.op o φ)) (hD o _ (hT φ))
  rw [map_sub, TR.CuspSub.op_val, sub_sub_sub_cancel_right] at h1
  exact h1

private theorem stab_orthRel {E : Type} [Field E] [NumberField E] {n : ℕ} {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (ι : cuspForms E n →ₗ[ℂ] H)
    (hρ : ∀ X, ∀ a ∈ centralCuspForms E n, ∀ c ∈ centralCuspForms E n,
      inner ℂ (ι ((gkModuleCusp E n).ρ X a)) (ι c) + inner ℂ (ι a) (ι ((gkModuleCusp E n).ρ X c)) = 0)
    (hσ : ∀ k, ∀ a ∈ centralCuspForms E n, ∀ c ∈ centralCuspForms E n,
      inner ℂ (ι ((gkModuleCusp E n).σ k a)) (ι ((gkModuleCusp E n).σ k c)) = inner ℂ (ι a) (ι c))
    (hτ : ∀ g, ∀ a ∈ centralCuspForms E n, ∀ c ∈ centralCuspForms E n,
      inner ℂ (ι (finRepCusp E n g a)) (ι (finRepCusp E n g c)) = inner ℂ (ι a) (ι c))
    {U : Submodule ℂ (cuspForms E n)} (hU : U ≤ centralCuspForms E n) (hs : Fb.Stab U) :
    Fb.Stab (orthRel ι (centralCuspForms E n) U) := by
  refine ⟨fun X φ hφ => ?_, fun k φ hφ => ?_, fun g φ hφ => ?_⟩
  · refine map_mem_orthRel (A' := fun y => -(gkModuleCusp E n).ρ X y) (Fb.stab_central.ρ X)
      (fun x hx y hy => ?_) (fun u hu => U.neg_mem (hs.ρ X u hu)) hφ
    rw [map_neg, inner_neg_left, neg_eq_iff_add_eq_zero]
    exact hρ X x (hU hx) y hy
  · refine map_mem_orthRel (A' := (gkModuleCusp E n).σ k⁻¹) (Fb.stab_central.σ k)
      (fun x hx y hy => ?_) (hs.σ k⁻¹) hφ
    rw [← hσ k _ (hU (hs.σ k⁻¹ x hx)) y hy, ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, Module.End.one_apply]
  · refine map_mem_orthRel (A' := finRepCusp E n g⁻¹) (Fb.stab_central.τ g)
      (fun x hx y hy => ?_) (hs.τ g⁻¹) hφ
    rw [← hτ g _ (hU (hs.τ g⁻¹ x hx)) y hy, ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, Module.End.one_apply]

private theorem carrier_le_of_not_iso {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {n : ℕ}
    (π π' : CuspSub E n) (hi : ¬ π.Iso π') (C : Submodule ℂ (cuspForms E n)) (hC : Fb.Stab C)
    (hinf : Fb.carrier π ⊓ C = ⊥) (hle : Fb.carrier π' ≤ Fb.carrier π ⊔ C) : Fb.carrier π' ≤ C := by
  have hst : TR.IsStable (π'.V ⊓ C.map (Fb.ofCusp E n)) := fun o x hx =>
    ⟨π'.stable o x hx.1, hC.map o x hx.2⟩
  rcases π'.irred _ inf_le_left hst with h0 | h0
  · refine absurd (iso_of_compl π π' _ hC.map ?_ h0 ?_) hi
    · rw [← Fb.map_carrier, ← Submodule.map_inf _ Fb.ofCusp_injective, hinf, Submodule.map_bot]
    · rw [← Fb.map_carrier, ← Fb.map_carrier, ← Submodule.map_sup]
      exact Submodule.map_mono hle
  · intro φ' hφ'
    obtain ⟨ψ, hψ, e⟩ := inf_eq_left.1 h0 (Fb.mem_carrier.1 hφ')
    obtain rfl := Fb.ofCusp_injective e
    exact hψ

theorem UpperTheory.V.Af.Smo.innerZero :
    UpperTheory.V.Af.Smo.InnerZero := by
  intro E _ _ _ n μ _ π π' hc hc' hi φ hφ φ' hφ'
  have l := Fb.carrier_le_central π hc
  have l' := Fb.carrier_le_central π' hc'
  have hs := Fb.stab_carrier π
  have hC := stab_orthRel (CuspidalSpectrum.cuspToL2 μ) (fun X a ha c hc => petersson_inner_lieAlgebra_skewAdjoint μ X ha hc)
    (fun k a ha c hc => petersson_inner_maximalCompact_invariant μ k ha hc) (fun g a ha c hc => petersson_inner_finiteAdelic_invariant μ g ha hc) l hs
  have hsup := CuspidalSpectrum.sup_orthRel_centralCuspForms μ _ l hs.ρ hs.τ
  have hinf := inf_orthRel_eq_bot (ι := CuspidalSpectrum.cuspToL2 μ) l fun a ha h0 =>
    CuspidalSpectrum.eq_zero_of_cuspVecL_eq_zero (μ := μ) ha h0
  exact (carrier_le_of_not_iso π π' hi _ hC hinf (l'.trans hsup.ge) hφ').2 φ hφ
