import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesDisjointIdempotents
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColJoinSOfSTiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.PkPlaces
theorem pk_places_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → (∃ e : AE D, IsIdemSum e ((_root_.GlobalTheory.Fam.pk_z W).Pg ∪ ∅)) ∧ ∀ t, Disjoint (_root_.GlobalTheory.Fam.pk_z W).Pg ((_root_.GlobalTheory.Fam.pk_z W).Q t) ∧ (∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, ∀ PP' ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, PP.under (𝓞 D.host.F) ≠ PP'.under (𝓞 D.host.F)) ∧ (∃ e : AE D, IsIdemSum e ((_root_.GlobalTheory.Fam.pk_z W).Pg ∪ (_root_.GlobalTheory.Fam.pk_z W).Q t)) ∧ ∃ e : AE D, IsIdemSum e (∅ ∪ (_root_.GlobalTheory.Fam.pk_z W).Q t) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW
  have hl : (_root_.GlobalTheory.Fam.pk_z W).toLevCh.Is W.P.A3.A.μ0 := hW.bot.hyp.2.2.2.1.lev
  have hQQ : ∀ t, ∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, ∀ PP' ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, ¬ Lev.IsConjPl PP PP' :=
    fun t PP h PP' h' => ((hl.Q_pl t) PP h).2 PP' h'
  have hnc : ∀ t, ∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∪ (_root_.GlobalTheory.Fam.pk_z W).Q t, ∀ PP' ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∪ (_root_.GlobalTheory.Fam.pk_z W).Q t, ¬ Lev.IsConjPl PP PP' := by
    intro t PP h PP' h' hc
    have ha := (GlobalTheory.StepLifts.places_apart _ hl t).1
    rcases Finset.mem_union.1 h with h | h
    · exact ha PP h PP' (Finset.mem_union.1 h') hc
    · rcases Finset.mem_union.1 h' with h' | h'
      · refine ha PP' h' PP (Or.inr h) ?_
        rw [GlobalTheory.GoodPrimes.isConjPl_iff] at hc ⊢
        rw [hc, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]
      · exact hQQ t PP h PP' h' hc
  refine ⟨?_, fun t => ⟨(GlobalTheory.StepLifts.places_apart _ hl t).2, ?_, ?_, ?_⟩⟩
  · rw [Finset.union_empty]
    exact GlobalTheory.CentralShift.exists_idemSum _ fun PP h PP' h' =>
      (GlobalTheory.StepLifts.places_apart _ hl W.P.A3.A.μ0).1 PP h PP' (Or.inl h')
  · intro PP h PP' h' e
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq e.symm with e' | e'
    · exact Finset.disjoint_left.1 (GlobalTheory.StepLifts.places_apart _ hl t).2 h (e' ▸ h')
    · exact (GlobalTheory.StepLifts.places_apart _ hl t).1 PP h PP' (Or.inr h') (GlobalTheory.GoodPrimes.isConjPl_iff.2 e')
  · exact GlobalTheory.CentralShift.exists_idemSum _ (hnc t)
  · rw [Finset.empty_union]
    exact GlobalTheory.CentralShift.exists_idemSum _ (hQQ t)
end GlobalTheory.PkPlaces
end
