import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertHeckeOperatorIndepOfInertDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCanonicalInertTensorCompletionEquivStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeTransformInvariantUnderFieldAutomorphismStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AntidiagTransportCompMemSphericalHeckeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedByUnitaryIntegralPointsOfLevelFixedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertHeckeOperatorThroughFrameEvalFinitePointsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open scoped TensorProduct

theorem GlobalTheory.InertHeckeTransfer.exists_lift_eigen : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n) (U : Submodule ℂ (UA L n → ℂ)), Dict F π U → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), NG.SatAt π Dv α → (∀ x : L, Dv.σw (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → ∀ (b : GL (Fin n) (w.adicCompletion L)), b ∈ GlobalTheory.LFun.KGL w n → Formalism.UG.cT Dv.σw b.val * b.val = Formalism.UG.antiJ (w.adicCompletion L) n → ∀ p : locU n w →* Formalism.UG.GU Dv.σw n, (∀ x, (p x).val = b⁻¹ * cLoc w x.val * b) → ∃ φ ∈ U, φ ≠ 0 ∧ (∀ x : locU n w, p x ∈ Formalism.UG.KU Dv.σw n → RU L n x.val φ = φ) ∧ ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n), GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) ((Formalism.UG.KU Dv.σw n).comap p) (fun x => h (p x)) φ = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α • φ := by
  intro L _ _ _ n F π U hD v w hw Dv α hα hs b hbK hbJ p hp
  obtain ⟨f, hfS, hf0, U0, hfixU0, hU0, heig⟩ := hα
  obtain ⟨g0, hg0⟩ : ∃ g0, f g0 ≠ 0 := Function.ne_iff.1 hf0
  obtain ⟨lam, hlam⟩ : ∃ lam : Module.Dual ℂ π.W, lam (f g0) ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hg0 ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hc)
  have hmem : (fun x => lam (f x)) ∈ U.map (LinearMap.funLeft ℂ ℂ F.j) := by
    rw [hD.2]
    exact Submodule.subset_span ⟨f, hfS, lam, rfl⟩
  obtain ⟨φ, hφU, hφ⟩ := hmem
  have hφ' : ∀ g, φ (F.j g) = lam (f g) := fun g => congrFun hφ g
  have hfU : ∀ g, ∀ κ ∈ U0, f (g * κ) = f g := fun g κ hκ => congrFun (hfixU0 κ hκ) g
  refine ⟨φ, hφU, fun h => hlam ?_, GlobalTheory.T.fixed_by_unitaryIntegralPoints_of_level_fixed L n F U hD.1 v w hw U0 hU0 Dv.σw b hbK p hp φ hφU
    (fun g κ hκ => by rw [hφ', hφ', hfU g κ hκ]), fun h hh => ?_⟩
  · rw [← hφ', h]; rfl
  obtain ⟨e, he1, he2, he3⟩ := GlobalTheory.T.exists_canonical_inert_tensor_completion_equiv L n F v w hw Dv hs
  have hbP : b ∈ (Formalism.UG.bc (n := Fin n) (Formalism.UG.intL (w.adicCompletion L)).subtype).range := hbK
  let D0 : InertDatum L n v w := ⟨e, Dv.σw, Dv.ϖ, b, he1, Dv.unram, he2, hbP, hbJ⟩
  have hloc : ∀ y, D0.loc y = b⁻¹ * cLoc w (F.j y) * b := by
    intro y
    show b⁻¹ * _ * b = _
    congr 2
    refine Units.ext (Matrix.ext fun s t => ?_)
    rw [F.loc]
    exact he3 _
  have hbi := hh.1
  have hh' := GlobalTheory.T.antidiagTransport_comp_mem_sphericalHecke (GlobalTheory.SatInd.gEquiv Dv D0) (GlobalTheory.SatInd.gEquiv_comm Dv D0) (GlobalTheory.SatInd.gEquiv_intL Dv D0) n h hh
  have heig0 : heckeFunI L n U0 D0 h f = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α • f := by
    rw [GlobalTheory.SatInd.heckeFunI_indepDatum L n v w Dv D0 U0 π.W h hbi f, heig _ hh',
      GlobalTheory.T.satakeTransform_invariant_under_field_automorphism (GlobalTheory.SatInd.gEquiv Dv D0) (GlobalTheory.SatInd.gEquiv_comm Dv D0) (GlobalTheory.SatInd.gEquiv_intL Dv D0) Dv.ϖ _ n (n / 2)
        Dv.unram (by omega) (by omega) h hbi α]
  have htr := GlobalTheory.T.inertHeckeOperator_through_frame_eval_finitePoints L n F v w hw D0 U0 hU0 b hbK p hp hloc h hh π.W f hfixU0 lam φ hφ'
  have hvecU : GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) ((Formalism.UG.KU Dv.σw n).comap p) (fun x => h (p x)) φ ∈ U := by
    unfold GlobalTheory.LFun.heckeVec
    by_cases hfin : (Function.support fun c : (locU n w) ⧸ ((Formalism.UG.KU Dv.σw n).comap p) =>
        h (p c.out) • ((RU L n).comp (locU n w).subtype) c.out φ).Finite
    · rw [finsum_eq_sum _ hfin]
      exact U.sum_mem fun c _ => U.smul_mem _ (hD.1.stable _ _ hφU)
    · rw [finsum_of_infinite_support hfin]
      exact U.zero_mem
  rw [← sub_eq_zero]
  refine GlobalTheory.DefiniteDense.eq_zero_of_finU L n _ (hD.1.aut _ (U.sub_mem hvecU (U.smul_mem _ hφU))) fun z hz => ?_
  obtain ⟨g, rfl⟩ := F.onto z hz
  rw [Pi.sub_apply, Pi.smul_apply, htr g, heig0, hφ', Pi.smul_apply, map_smul, smul_eq_mul, sub_self]

end
