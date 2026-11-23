import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaEigenCompatibilityFirstStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaEigenCompatibilitySecondStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaEigenCompatibilityThirdStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaEigenCompatibilityFourthStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaEigenCompatibilityFifthStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaEigenCompatibilitySixthStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.EigStr.eigString_all : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Formalism.MainNotions.SumRepresentations.Conclusion41 D → Formalism.MainNotions.SumRepresentations.adm7 D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ i, GlobalTheory.NJoin.EigString X i := by
  intro hAF hL D P X hA h41 h7 htl i hμ j hj x hx f hf y hy
  show y ≠ 0 → _
  intro hy0 hh hops
  classical
  let s : GlobalTheory.DownLift.Sys D := fun Pp d =>
    if hc : ∃ c : ℂ, hh Pp (Finsupp.single d 1) y = c • y then hc.choose else 0
  have hs : GlobalTheory.DownLift.IsEigV X.R j (X.tupT (D.nd.mu i)) hh s y := by
    intro Pp d hG hLab
    have hc : ∃ c : ℂ, hh Pp (Finsupp.single d 1) y = c • y :=
      (GlobalTheory.LPositivity.split_or_inert D Pp).elim
        (fun h1 => GlobalTheory.T.theta_eigen_compatibility_first hAF hL D P X hA h41 h7 htl i hμ j hj x hx f hf y hy hy0 hh hops Pp hG h1 d hLab)
        (fun h1 => GlobalTheory.T.theta_eigen_compatibility_second hAF hL D P X hA h41 h7 htl i hμ j hj x hx f hf y hy hy0 hh hops Pp hG h1 d hLab)
    simp only [s, dif_pos hc]
    exact hc.choose_spec
  let B : GlobalTheory.LFun.Fam D.host.E := fun w =>
    if hB : ∃ Bw, GlobalTheory.LFun.IsSysParam D.sp.cm.sig (Formalism.IndefR.Links.Vc D j).rank
        (rfl : w.under (𝓞 D.host.F) = _) (s w) Bw then hB.choose else 0
  have hB : GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl X.R (X.tupT (D.nd.mu i)))
      (Formalism.IndefR.Links.Vc D j).rank s B := by
    intro v hv w hw
    subst hw
    have hex : ∃ Bw, GlobalTheory.LFun.IsSysParam D.sp.cm.sig (Formalism.IndefR.Links.Vc D j).rank
        (rfl : w.under (𝓞 D.host.F) = _) (s w) Bw := by
      rcases GlobalTheory.LPositivity.split_or_inert D w with h1 | h1
      · exact GlobalTheory.T.theta_eigen_compatibility_third hAF hL D P X hA h41 h7 htl i hμ j hj x hx f hf y hy hy0 hh hops s hs w hv h1
      · exact GlobalTheory.T.theta_eigen_compatibility_fourth hAF hL D P X hA h41 h7 htl i hμ j hj x hx f hf y hy hy0 hh hops s hs w hv h1
    show GlobalTheory.LFun.IsSysParam D.sp.cm.sig _ _ (s w) (B w)
    simp only [B, dif_pos hex]
    exact hex.choose_spec
  refine ⟨s, ⟨B, hB, fun w hw => ?_⟩, hs⟩
  rcases GlobalTheory.LPositivity.split_or_inert D w with h1 | h1
  · exact GlobalTheory.T.theta_eigen_compatibility_fifth hAF hL D P X hA h41 h7 htl i hμ j hj x hx f hf y hy hy0 hh hops s B hs hB w hw h1
  · exact GlobalTheory.T.theta_eigen_compatibility_sixth hAF hL D P X hA h41 h7 htl i hμ j hj x hx f hf y hy hy0 hh hops s B hs hB w hw h1
