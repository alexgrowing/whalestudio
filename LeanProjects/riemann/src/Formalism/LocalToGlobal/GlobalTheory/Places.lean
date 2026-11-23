import Formalism.SharpRestriction.GlobalSchurBounds.LinkPk

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Places

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory

def PlaceConditionsFamily : Prop :=
  ∀ {eps : ℝ} (Fm : FamP eps) (crystallineComparison : ℝ), product_first_zeroth_parts.ConclusionOnFamily Fm crystallineComparison → SettingEventually Fm → TuSize Fm → J.MuRank Fm →
    LinkG Fm → LinkMu Fm → Lnk.PlacesF Fm

def SlopeBoundOfMuRank : Prop :=
  ∀ {eps : ℝ} (Fm : FamP eps) (crystallineComparison : ℝ), product_first_zeroth_parts.ConclusionOnFamily Fm crystallineComparison → SettingEventually Fm → TuSize Fm → J.MuRank Fm →
    LinkG Fm → LinkMu Fm → LocalQuadraticParts.SlopeLemmaFamily Fm

def LevelPrimeSettingFamily : Prop := ∀ {eps : ℝ} (Fm : FamP eps), TuSize Fm → SettingEventually Fm

def SlopeLemmaLinkForm : Prop :=
  ∀ {eps : ℝ} (Fm : FamP eps) (Cabs CH C0 crystallineComparison : ℝ), 0 < C0 → product_first_zeroth_parts.ConclusionOnFamily Fm crystallineComparison → TuSize Fm →
    ChosenE Fm C0 CH → GlobalTheoremInputs Fm Cabs CH C0 → LocalQuadraticParts.SlopeLemmaFamily Fm

end Formalism.L2.GlobalTheoryTheory.Places

end
