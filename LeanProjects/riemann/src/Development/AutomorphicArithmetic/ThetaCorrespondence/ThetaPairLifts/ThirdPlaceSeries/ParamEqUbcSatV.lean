import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaEigenCompatibilitySeventh
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeFunIEigCStatement
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.StrInert
end GlobalTheory.StrInert
theorem GlobalTheory.StrInert.param_eq_ubc_satV_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ x ∈ ZgoodN D.nd D.naut i, ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ eigC D.nd D.naut i x → ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → y ≠ 0 → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ (s : GlobalTheory.DownLift.Sys D) (B : GlobalTheory.LFun.Fam D.host.E), GlobalTheory.DownLift.IsEigV X.R j (X.tupT (D.nd.mu i)) h s y → GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl X.R (X.tupT (D.nd.mu i))) (Formalism.IndefR.Links.Vc D j).rank s B → ∀ w : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → Formalism.UG.IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w → ∀ P', D.naut.ptV i P' = some x → (B w).map (fun a : ℂˣ => (a : ℂ)) = ubc D.R.nV (D.naut.satV i P' w) := by
  intro hA hL D P X hX h41 h7 htie i hμ j hj x hx f hf y hy hy0 h hh s B hs hB w hw hin P' hP'
  have hv := GlobalTheory.StrInert.not_mem_badPl X.R (X.tupT (D.nd.mu i)) w hw hin
  have hns := GlobalTheory.StrInert.not_isSplitPl_of_inert D w hin
  obtain ⟨P₀, hP₀, α₀, hsat, hev⟩ := _root_.GlobalTheory.T.theta_eigen_compatibility_ninth_alt hA hL D P X hX h41 h7 htie i hμ j hj x hx f hf y hy hy0 h hh s hs w hw hin
  have hBw := hB _ hv w rfl
  rcases hBw with ⟨hsp, -⟩ | ⟨-, τ, ϖ, α, hU, hτ, hBeq, hc⟩
  · exact absurd hsp (GlobalTheory.LFun.not_isSplit_of_isInertAt hin)
  have hrank : (Formalism.IndefR.Links.Vc D j).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) j.2
  have key : (B w).map (fun a : ℂˣ => (a : ℂ)) = ubc (Formalism.IndefR.Links.Vc D j).rank (D.naut.satV i P₀ w) := by
    rw [hBeq, hsat]
    exact GlobalTheory.T.unramifiedBaseChange_eq_of_satake_eq _ ϖ τ _ _ hU α α₀ fun d t' hd ht' => (hc d t' hd ht').symm.trans (hev τ ϖ hU hτ d t' hd ht')
  rw [key, hrank]
  have h2 := ((h41 i).2.1 P₀ P' (by rw [hP₀]; exact Option.some_ne_none x) (hP₀.trans hP'.symm)).2 w
  exact (h2 (fun hS => hns (D.nd.SQ_split i w (Or.inl hS))) (fun hQ => hns (D.nd.SQ_split i w (Or.inr hQ)))).2 hns
end
