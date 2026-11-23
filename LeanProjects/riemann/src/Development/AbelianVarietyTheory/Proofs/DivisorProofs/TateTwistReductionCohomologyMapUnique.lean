import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendScalarsUliftHomAdditive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendChainMapAlongQuasiIsoKInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafComplexSemilinearMapCompBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackPushforwardFunctorialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorThroughExtendScalarsZmodStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoExtendScalarsTateTwistAugmentationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendScalarsTateTwistResolutionHomExtAugmentatiStatement

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedUniq

theorem op_eq : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (i : ℤ) (ρ ρ' : SemiMap (res _ (tw Q i)) (res _ (tw q i))),
    (∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), ρ.app U 0 (resGen i ζ) = ρ'.app U 0 (resGen i ζ)) →
    ∀ (E : Spc) (n : ℤ) (x : Ht Q E n i), ρ.op.app E n x = ρ'.op.app E n x := by
  intro Q q _ hq i ρ ρ' h E n x
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_factor_through_extendScalars_zmod Q q hq _ _ ρ
  obtain ⟨u', hu'⟩ := GlobalTheory.T.exists_factor_through_extendScalars_zmod Q q hq _ _ ρ'
  have e1 := (GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective _ _ (extπ (ZMod.castHom hq (ZMod q)) (res _ (tw Q i))) ρ u hu).1 E n x
  have e2 := (GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective _ _ (extπ (ZMod.castHom hq (ZMod q)) (res _ (tw Q i))) ρ' u' hu').1 E n x
  have hε := GlobalTheory.T.extendScalars_tateTwistResolution_hom_ext_augmentation Q q hq i _ u u' (fun U ζ => by rw [← hu, ← hu', h])
  haveI := GlobalTheory.T.quasiIso_extendScalars_tateTwist_augmentation Q q hq i
  haveI : (res (ZMod q) (tw q i)).IsKInjective :=
    inferInstanceAs ((injectiveResolution (tw q i)).cochainComplex.IsKInjective)
  haveI : (res (ZMod q) (tw q i)).IsStrictlyGE 0 :=
    inferInstanceAs ((injectiveResolution (tw q i)).cochainComplex.IsStrictlyGE 0)
  obtain ⟨H⟩ := (GlobalTheory.T.extend_chainMap_along_quasiIso_kInjective (ZMod q) _ _ (res _ (tw q i)) (extAug (ZMod.castHom hq (ZMod q)) (tw Q i))).2 u u' hε
  have e3 := ((GlobalTheory.T.hypercohomologyPullbackPushforward_functorial (ZMod q)).2.2.2.2 u u' ⟨H⟩ ((chains (ZMod q)).obj E) n).2
  rw [e1, e2, e3]

end GlobalTheory.EtC.RedUniq

end
