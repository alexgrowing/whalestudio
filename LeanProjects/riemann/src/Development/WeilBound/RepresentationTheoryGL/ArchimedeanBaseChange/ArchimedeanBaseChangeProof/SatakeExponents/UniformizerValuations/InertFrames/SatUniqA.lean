import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameInert
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BcParamEqOfSatUEq

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Inert

theorem satUniq : SatUniq := by
  intro E _ _ _ n w hw b b' ϖ ϖ' q q' σ α α' hb hb' hϖ hϖ' hU hU' hS hS'
  obtain ⟨p, σ₁, hp, hα, ⟨e1⟩⟩ := hS
  obtain ⟨p', σ₂, hp', hα', ⟨e2⟩⟩ := hS'
  have hq : q = q' := Nat.pow_left_injective two_ne_zero (hU.2.2.2.2.2.2.symm.trans hU'.2.2.2.2.2.2)
  subst hq
  have hb2 : cT (cj w) b.1 * b.1 = antiJ _ n := hb.2
  have hb'2 : cT (cj w) b'.1 * b'.1 = antiJ _ n := hb'.2
  have hkm : b⁻¹ * b' ∈ GU (cj w) n := by
    have hc : cT (cj w) (b⁻¹).1 * cT (cj w) b.1 = 1 := by rw [← cT_mul, Units.mul_inv, cT_one]
    have hd : b.1 * (b⁻¹).1 = 1 := Units.mul_inv b
    change _ * _ * _ = _
    calc cT (cj w) (b⁻¹ * b').1 * antiJ _ n * (b⁻¹ * b').1
        = cT (cj w) b'.1 * (cT (cj w) (b⁻¹).1 * cT (cj w) b.1) * (b.1 * (b⁻¹).1) * b'.1 := by
          rw [Units.val_mul, cT_mul, ← hb2]; simp only [Matrix.mul_assoc]
      _ = antiJ _ n := by rw [hc, hd, Matrix.mul_one, Matrix.mul_one, hb'2]
  let k : GU (cj w) n := ⟨b⁻¹ * b', hkm⟩
  have hcomm : ∀ u, p u * k = k * p' u := fun u => Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hp, hp']
    show b⁻¹ * u.1 * b * (b⁻¹ * b') = b⁻¹ * b' * (b'⁻¹ * u.1 * b')
    group)
  let L1 := e1.toLinearEquiv
  let L2 := e2.toLinearEquiv
  have h1 : ∀ g v, L1 (σ.ρ g v) = σ₁.ρ (p g) (L1 v) := fun g v => LinearMap.congr_fun (e1.isIntertwining' g) v
  have h2 : ∀ g v, L2 (σ.ρ g v) = σ₂.ρ (p' g) (L2 v) := fun g v => LinearMap.congr_fun (e2.isIntertwining' g) v
  let F : σ₁.V →ₗ[ℂ] σ₂.V := L2.toLinearMap ∘ₗ L1.symm.toLinearMap ∘ₗ σ₁.ρ k
  have hF : ∀ g y, F (σ₁.ρ g y) = σ₂.ρ g (F y) := by
    intro g y
    obtain ⟨u, rfl⟩ := p'.surjective g
    have e : ∀ z, L1.symm (σ₁.ρ (p u) z) = σ.ρ u (L1.symm z) := fun z => by
      apply L1.injective
      rw [h1, L1.apply_symm_apply, L1.apply_symm_apply]
    simp only [F, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← Module.End.mul_apply, ← map_mul, ← hcomm u, map_mul, Module.End.mul_apply, e, h2]
  have hkinj : Function.Injective (σ₁.ρ k) := fun a c h => by
    have h' := congrArg (σ₁.ρ k⁻¹) h
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, ← Module.End.mul_apply, ← map_mul,
      inv_mul_cancel, map_one] at h'
  have hFinj : Function.Injective F := L2.injective.comp (L1.symm.injective.comp hkinj)
  obtain ⟨x, hx⟩ := hα.exists_vec
  have hFx : F x ≠ 0 := fun h => hx.1 (hFinj (h.trans (map_zero F).symm))
  have h2x : GlobalTheory.LFun.IsSatVecU (ϖ : w.adicCompletion E) q σ₂.ρ (F x) α := hx.map hU F hF hFx
  have h3 : GlobalTheory.LFun.IsSatVecU (ϖ' : w.adicCompletion E) q σ₂.ρ (F x) α := h2x.of_unif hU hU'
  exact h3.unique hU' (hα'.2 _ h2x.2.1 hFx)

end PositivityTheory.Rg.BcB.F.Inert

end
