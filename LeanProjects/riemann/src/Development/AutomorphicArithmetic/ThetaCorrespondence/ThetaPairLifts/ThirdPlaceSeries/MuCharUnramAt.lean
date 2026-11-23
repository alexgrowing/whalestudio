import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharacterUnramifiedAwayLevel
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
namespace GlobalTheory.MuUnrOff
theorem mu_charUnramAt_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (t : W.P.T) (n : ℕ) (x : HeightOneSpectrum (𝓞 D.host.F)), 1 ≤ n → n ≤ D.R.m → (∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, PP.under (𝓞 D.host.F) ≠ x) → (∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, PP.under (𝓞 D.host.F) ≠ x) → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t n) x := by
  intro D L hT Gi Gl Kc Yd cX ex W hP t n x h1 h2 hPg hQ
  have hL := hP.bot.hyp.2.2.2.1.lev
  refine GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w hw => ?_
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  have hj : j < D.R.m := by omega
  show GlobalTheory.LFun.UnrAt ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu0 (j + 1) * (_root_.GlobalTheory.Fam.pk_z W).toLevCh.xi t) w
  refine GlobalTheory.LFun.UnrAt.mul ?_ ?_
  · refine (GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.mu0 ⟨j, hj⟩) w).2 (((_root_.GlobalTheory.Fam.pk_z W).toLevCh.C.isMu0 ⟨j, hj⟩).unr w fun k hk => ?_)
    rcases GlobalTheory.ConjOverQuad.div_or_conj_div D (_root_.GlobalTheory.Fam.pk_z W).toLevCh.C.P k w hk with h | ⟨w', h, hc⟩
    · exact hPg w ((hL.Pg w).2 ⟨k, h⟩) hw
    · refine hPg w' ((hL.Pg w').2 ⟨k, h⟩) (Eq.trans ?_ hw)
      ext a
      show algebraMap _ _ a ∈ w'.asIdeal ↔ algebraMap _ _ a ∈ w.asIdeal
      rw [hc, Formalism.L2.Col.mem_conjIdeal]
      have : Formalism.L2.Col.cO D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) = algebraMap _ _ a := by
        apply RingOfIntegers.ext
        exact (D.sp.cm.fixed _).2 ⟨a, rfl⟩
      rw [this]
  · refine (GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.xi t) w).2 ?_
    by_contra hu
    rcases (hL.Q_ram t w).1 hu with h | ⟨P', hP', hc⟩
    · exact hQ w h hw
    · exact hQ P' hP' ((GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc).trans hw)
end GlobalTheory.MuUnrOff
end
