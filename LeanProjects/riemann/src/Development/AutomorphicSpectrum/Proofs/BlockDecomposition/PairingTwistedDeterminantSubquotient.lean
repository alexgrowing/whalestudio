import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspLinesIrr
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassTwistNeg
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc

noncomputable section

namespace GlobalTheory.CompanionTheory.DualQuot

theorem exists_subquotient_dual_nu : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n s : ℕ) (V' : Type) [AddCommGroup V'] [Module ℂ V'] (S : IrrRep (GL (Fin n) k))
    (A' : Representation ℂ (GL (Fin n) k) V'), IsSmooth A' → ∀ B : S.V →ₗ[ℂ] V' →ₗ[ℂ] ℂ,
    (∀ g w w', B (S.ρ g w) (A' g w') = ((detChar (Fin n) (absPow k (s : ℂ)) g : ℂˣ) : ℂ) * B w w') → B ≠ 0 →
    ∃ Q : IrrRep (GL (Fin n) k), IsSubquotient Q.ρ A' ∧
      IrrGL.of Q.ρ Q.smooth Q.irr = (dualCl (IrrGL.of S.ρ S.smooth S.irr)).nu (s : ℂ) := by
  intro k _ _ _ _ n s V' _ _ S A' hA' B hB hB0
  have hBZ := GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
  have hAd : GlobalTheory.Published.IrreducibleAdmissibleGL := fun k _ _ _ _ n V _ _ π => (hBZ k).1 (Fin n) V π
  have hχ : IsSmoothChar (absPow k (s : ℂ)) := isSmoothChar_absPow _
  have hχ' : IsSmoothChar (absPow k (-(s : ℂ))) := isSmoothChar_absPow _
  have hprod : ∀ g : GL (Fin n) k, ((detChar (Fin n) (absPow k (-(s : ℂ))) g : ℂˣ) : ℂ) *
      ((detChar (Fin n) (absPow k (s : ℂ)) g : ℂˣ) : ℂ) = 1 := by
    intro g
    rw [absPow_neg, detChar_apply, detChar_apply, MonoidHom.inv_apply]
    simp
  have hT := isSmooth_twist hA' hχ'.detChar
  have hBT : ∀ g a b, B (S.ρ g a) (twist A' (detChar (Fin n) (absPow k (-(s : ℂ)))) g b) = B a b := by
    intro g a b
    rw [twist_apply, map_smul, hB, smul_eq_mul, ← mul_assoc, hprod, one_mul]
  let f := GlobalTheory.InvPairing.pairMap S.ρ hT B hBT
  have hc := GlobalTheory.CompanionTheory.ZcDual.isIrreducible_contra hAd S.ρ S.smooth S.irr
  have hsurj : Function.Surjective f := by
    let R : Subrepresentation (contra S.ρ) :=
      { toSubmodule := LinearMap.range f.toLinearMap
        apply_mem_toSubmodule := fun g v hv => by
          obtain ⟨w, rfl⟩ := hv
          refine ⟨twist A' (detChar (Fin n) (absPow k (-(s : ℂ)))) g w, ?_⟩
          have := LinearMap.congr_fun (f.isIntertwining' g) w
          simpa only [LinearMap.comp_apply] using this }
    rcases hc.eq_bot_or_eq_top R with hR | hR
    · exfalso
      refine hB0 (GlobalTheory.InvPairing.eq_zero_of_pairMap S.ρ hT B hBT fun b => ?_)
      have : f b ∈ R.toSubmodule := ⟨b, rfl⟩
      rw [hR] at this
      exact (Submodule.mem_bot ℂ).1 this
    · intro l
      have : l ∈ R.toSubmodule := by rw [hR]; exact Submodule.mem_top
      obtain ⟨b, hb⟩ := this
      exact ⟨b, hb⟩
  let F : A'.IntertwiningMap (twist (contra S.ρ) (detChar (Fin n) (absPow k (s : ℂ)))) :=
    { toLinearMap := f.toLinearMap
      isIntertwining' := fun g => by
        refine LinearMap.ext fun w => ?_
        have h := LinearMap.congr_fun (f.isIntertwining' g) w
        simp only [LinearMap.comp_apply, twist_apply, map_smul] at h ⊢
        rw [← h, smul_smul, mul_comm, hprod, one_smul] }
  refine ⟨⟨_, twist (contra S.ρ) (detChar (Fin n) (absPow k (s : ℂ))),
    isSmooth_twist (isSmooth_contra _) hχ.detChar, isIrreducible_twist hc _⟩,
    IsSubquotient.of_surjective F hsurj, ?_⟩
  rw [GlobalTheory.CompanionTheory.ZcDual.dualCl_eq hAd, IrrGL.nu, IrrGL.tw_of]
  exact IrrGL.of_eq_of.2
    ⟨(twistEquiv (GlobalTheory.ContraRefl.contraEquiv (IrrGL.equivOf S.ρ S.smooth S.irr)) _).symm⟩

end GlobalTheory.CompanionTheory.DualQuot

end
