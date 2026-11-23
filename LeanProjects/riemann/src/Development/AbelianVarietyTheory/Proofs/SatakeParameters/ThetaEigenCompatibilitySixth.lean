import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaEigenCompatibilitySeventhStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatakeMultisetAtInertPlacesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodPlaceSplitConditionStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EigStrInert

theorem strInert : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Formalism.MainNotions.SumRepresentations.Conclusion41 D → Formalism.MainNotions.SumRepresentations.adm7 D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ x ∈ ZgoodN D.nd D.naut i, ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ eigC D.nd D.naut i x → ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → y ≠ 0 → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ (s : GlobalTheory.DownLift.Sys D) (B : GlobalTheory.LFun.Fam D.host.E), GlobalTheory.DownLift.IsEigV X.R j (X.tupT (D.nd.mu i)) h s y → GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl X.R (X.tupT (D.nd.mu i))) (Formalism.IndefR.Links.Vc D j).rank s B → ∀ w : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → Formalism.UG.IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w → ∃ B' : Multiset ℂ, (B w).map (fun a : ℂˣ => (a : ℂ)) = B' + GlobalTheory.DownLift.str (Ideal.absNorm w.asIdeal) (GlobalTheory.DownLift.valV X.R j (X.tupT (D.nd.mu i)) w : ℂ) D.R.t ∧ ∀ a ∈ B', ‖a‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2) := by
  intro hA hL D P X hAg hconds hadm htie i hμ j hj x hx f hf y hy hy0 h hh s B hE hB w hw hinert
  obtain ⟨P', hP', hw2⟩ := GlobalTheory.T.exists_point_inert_place hA hL D P X hAg hconds hadm htie i x hx
  obtain ⟨B'', c, hc, heq, hnorm⟩ := hw2 w hinert
  have h1 := GlobalTheory.T.theta_eigen_compatibility_seventh hA hL D P X hAg hconds hadm htie i hμ j hj x hx f hf y hy hy0 h hh s B hE hB w hw hinert P' hP'
  have h2 := GlobalTheory.T.good_place_split_condition hA hL D P X hAg hconds hadm htie i hμ j hj w hw hinert c hc
  refine ⟨B'', by rw [h1, heq, h2], fun a ha => ?_⟩
  rw [hnorm a ha]
  apply Real.one_le_rpow
  · have : Ideal.absNorm w.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  · have : 1 ≤ D.R.r := by
      simp only [Formalism.BasicNotions.Ranks.r]; have := D.R.two_le_m; omega
    have h' : (1 : ℝ) ≤ D.R.r := by exact_mod_cast this
    linarith

end GlobalTheory.EigStrInert
