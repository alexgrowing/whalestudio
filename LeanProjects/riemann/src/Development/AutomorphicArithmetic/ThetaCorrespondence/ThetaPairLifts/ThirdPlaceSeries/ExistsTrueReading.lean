import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTrueReadingWithLaws
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Laws
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadAtExistsM
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MRecLawsH
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecUnit
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AlIsRecrecLaws
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.TrueReading
open GlobalTheory.WeilDeligne GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem exists_true_reading_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D),
    (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) →
    ∃ S : Reading P.T, _root_.GlobalTheory.NPin.IsFaithfulReading P S ∧ _root_.GlobalTheory.SplitRead.LawsAlt S ∧ SuppLaws S := by
  intro hAF hL D P hR
  classical
  haveI := GlobalTheory.CuspRep.host_isCMField D.host
  have hex : ∀ w : PlE D.host, IsSplitPl D.host w → ∃ s : SplitPlace D.host.E, s.w = w := by
    intro w hw
    obtain ⟨w', hw'⟩ := GlobalTheory.ToricFactor.exists_isConjPl w
    obtain ⟨s, -, hs, -⟩ :=
      GlobalTheory.SplitConjPlace.splitEx_all D w' (GlobalTheory.ConjugatePlaceSplitting.isSplitPl_of_isConjPl hw hw')
    exact ⟨s, GlobalTheory.ToricFactor.isConjPl_unique hs (GlobalTheory.ToricFactor.isConjPl_symm hw')⟩
  have key : ∀ i (w : PlE D.host), IsSplitPl D.host w → ∃ X : ReadAt P.T i w, X.rc = _root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D w ∧
      ∀ (s : SplitPlace D.host.E), s.w = w → ∀ Y : ReadAt P.T i s.w, HEq Y X →
        (∀ σ, D.what₂.isot (D.nd.j i) σ ≠ ⊥ → IsLocS (P.rep σ).S s (Y.row σ).toIrrRep) ∧
        (∀ Q, IsLocS (n := D.R.nV) (P.H.av.S i Q) s (Y.rep Q).toIrrRep) ∧
        (∀ j : Fin D.R.m, j.1 + 1 = D.nd.j i → IsComp (P.tp.tup (D.nd.mu i) j) s.w Y.mu) ∧
        IsComp P.cf.eta s.w Y.eta := by
    intro i w hw
    obtain ⟨s₀, rfl⟩ := hex w hw
    obtain ⟨X, h1, h2⟩ := _root_.GlobalTheory.TrueReading.readAt_exists_m_alt hAF hL D P hR i s₀
    refine ⟨X, h1, fun s hs Y hY => ?_⟩
    obtain rfl := GlobalTheory.SplitUniq.splitPlace_eq_of_w_eq D.host.E s s₀ hs
    obtain rfl := eq_of_heq hY
    exact h2
  choose S hS using key
  refine ⟨S, ⟨fun i w hw => (hS i w hw).1, fun i s hw σ hσ => ((hS i s.w hw).2 s rfl _ HEq.rfl).1 σ hσ,
    fun i s hw Q => ((hS i s.w hw).2 s rfl _ HEq.rfl).2.1 Q,
    fun i w hw j hj => ?_, fun i w hw => ?_⟩, fun i w hw => ?_, fun i w hw => ?_⟩
  · obtain ⟨s, rfl⟩ := hex w hw
    exact ((hS i s.w hw).2 s rfl _ HEq.rfl).2.2.1 j hj
  · obtain ⟨s, rfl⟩ := hex w hw
    exact ((hS i s.w hw).2 s rfl _ HEq.rfl).2.2.2
  · rw [(hS i w hw).1]
    exact (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w)).recLaws
  · rw [(hS i w hw).1]
    exact _root_.UpperTheory.Zero.LLC.IsRecT.recSupp (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w))
end GlobalTheory.TrueReading
end
