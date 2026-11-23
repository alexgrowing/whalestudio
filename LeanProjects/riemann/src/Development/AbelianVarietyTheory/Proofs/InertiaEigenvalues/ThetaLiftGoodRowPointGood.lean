import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LabCompat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AtMOfParamRec
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.GoodLiftPoint

theorem good_of_lift : ∀ (D : D7), SumRepresentations.Conclusion42 D → ∀ (i : D.nd.Loc) (σ : D.what₂.FT) (P : D.naut.AV i) (x : D.nd.X i), D.nd.goodRow σ → thetaOf D.nd D.naut i σ P → D.naut.ptV i P = some x → x ∈ ZgoodN D.nd D.naut i ∧ AtM D.nd D.naut i σ := by
  intro D h42 i σ P x hg hth hpt
  have hne : D.what₂.isot (D.nd.j i) σ ≠ ⊥ := by
    intro h
    apply hth.1
    rw [h, Submodule.map_bot]
  obtain ⟨Sig, hW, hBC⟩ := (h42 i σ hne).2.1
  have hX : HasParamX D.nd D.naut i x Sig := ⟨P, hpt, hBC P hth⟩
  have hZ : x ∈ ZN D.nd D.naut i := by
    refine ⟨P, hpt, _, hBC P hth, ?_⟩
    unfold twistIso
    exact List.mem_map.2 ⟨muPart D.nd D.naut i, by simp, rfl⟩
  have hgood : x ∈ ZgoodN D.nd D.naut i :=
    ⟨hZ, Sig, hX, (GlobalTheory.LabelCompat.labCompat D i σ Sig hW).1 hg⟩
  exact ⟨hgood, GlobalTheory.LiftLeaf.atMOfParam D i x hgood Sig hX σ hW⟩

end GlobalTheory.GoodLiftPoint
