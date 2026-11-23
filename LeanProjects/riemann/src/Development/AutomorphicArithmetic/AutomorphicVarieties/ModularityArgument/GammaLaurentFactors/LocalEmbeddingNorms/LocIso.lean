import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.MatchIndOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationDetEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivOfISupRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatakeOfIsLocComp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.EigOfSat

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.LocGL UpperTheory.V.Z.Inf
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.GJStandardLCuspidal
open scoped Classical

namespace UpperTheory.V.Z.Gam

private theorem localEmbedding_eq {K : Type} [Field K] [NumberField K] {n : ℕ}
    (w : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) (w.adicCompletion K)) :
    AdelicGLn.localEmbedding w g = locGL K n w g := by
  refine Units.ext <| Matrix.ext fun a b => FiniteAdeleRing.ext K fun v => ?_
  change ((AdelicGLn.finiteRestrictedEquiv K n).symm _ : AdelicGLn.FiniteAdelicGL K n) a b v = _
  rw [AdelicGLn.finiteRestrictedEquiv_symm_apply, RestrictedProduct.coe_mulSingle_apply]
  by_cases h : v = w
  · subst h
    rw [Pi.mulSingle_eq_same]
    exact (congrArg (fun x : GL (Fin n) (v.adicCompletion K) => x a b) (pLoc_locGL v g)).symm
  · rw [Pi.mulSingle_eq_of_ne h]
    exact (congrArg (fun x : GL (Fin n) (v.adicCompletion K) => x a b) (pLoc_locGL_of_ne h g)).symm

end UpperTheory.V.Z.Gam

open UpperTheory.V UpperTheory.V.Z.Gam in
theorem UpperTheory.V.Z.Gam.locIso :
    UpperTheory.V.Z.Gam.LocIso := by
  intro K _ _ _ n σ h D v
  let τ : SmIrr (GL (Fin n) (v.adicCompletion K)) :=
    { V := D.finite.W v
      ρ := D.finite.π v
      smooth := (D.finite.isAdmissible v).1
      irred := D.finite.isIrreducible v }
  have hτ : σ.IsLocComp v τ := by
    obtain ⟨a, x, hx, ha, hx0, -⟩ := exists_pureTensor_spherical (Cm.toRep σ h) D
    refine ⟨(Cm.carrierEq σ).toLinearMap ∘ₗ Iv D a x hx v, fun e => ?_, fun g y => ?_⟩
    · have e' : Iv D a x hx v (x v) = 0 := (Cm.carrierEq σ).map_eq_zero_iff.1 (LinearMap.congr_fun e (x v))
      rw [Iv_self] at e'
      exact phi_ne D a x hx ha hx0 e'
    · refine ((congrArg (Cm.carrierEq σ) (Iv_int D a x hx v g y)).trans (Cm.carrierEq_τ σ _ _)).trans ?_
      rw [localEmbedding_eq]
      rfl
  refine ⟨?_, fun B hB => ?_⟩
  · rintro s ⟨σ', h1, h2⟩
    obtain ⟨e⟩ := LocUniq.isLocComp_unique σ v σ' τ h1 hτ
    exact h2.of_equiv e
  · obtain ⟨α, -, h'⟩ := GlobalTheory.LFun.SphComp.hasSatake_of_isLocComp σ ((CG.hasSat_mk σ v B).1 hB) hτ
    have h1 : GlobalTheory.LGrp.IsSpherical τ.ρ (GlobalTheory.SplitWeil.KO (v.adicCompletion K) (Fin n)) := h'.2.1
    have hsph : GlobalTheory.LGrp.IsSpherical τ.ρ (GlobalTheory.LFun.KGL v n) := by
      rwa [GlobalTheory.SmGL.SphCompletion.KO_completion v n] at h1
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hsph
    rw [(Af.Smo.sphDict K n v).1]
    exact (Submodule.ne_bot_iff _).2 ⟨x, fun k hk => GlobalTheory.LGrp.mem_fixed.1 hx k hk, hx0⟩
