import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThickLetterWordLatticeSurjectionHypotheses
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HodgeTateJumpsAtModulesForSign
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.LiftingConditionOfWindows
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.RecS

theorem setting_of_wordBase : ∀ {D : D7} (L : SizeData₂ D) (HW : HWOf D.loc) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL) (Wd : NWord (RecS.nLet i w hw)), D.nd.l i ≠ 2 → RecS.WordBase L HW i r ρ π w hw Cx hG Wd → RecS.ThickLetterWordLatticeSurjectionHypotheses HW i r ρ π w hw Cx hG Wd := by
  intro D L HW i r ρ π w hw Cx hG Wd hl hB _ft T₁ T₂ F h1 h2 hF
  obtain ⟨ht1c, ht1w, ht1l⟩ := hB.t1 T₁ h1
  obtain ⟨ht2c, ht2low⟩ := hB.t2 T₂ h2
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨ht1c, ht2c, hF⟩, hB.small.1.2.2.2.2.2, ?_, fun a => ht2low _ft a, ?_, ht1l⟩
  · intro x y hxy
    have hv : ((algebraMap ↥(Loc.K0 (D.nbr i w hw).Kw) ↥(D.nbr i w hw).Kw.1 x : ↥(D.nbr i w hw).Kw.1) : Loc.Om (D.nd.l i)) =
        ((algebraMap ↥(Loc.K0 (D.nbr i w hw).Kw) ↥(D.nbr i w hw).Kw.1 y : ↥(D.nbr i w hw).Kw.1) : Loc.Om (D.nd.l i)) := by rw [hxy]
    exact Subtype.ext hv
  · intro y
    exact ⟨⟨y.1, show y.1 ∈ Loc.K0 (D.nbr i w hw).Kw from ⟨y.2, hB.unram y.2⟩⟩, Subtype.ext rfl⟩
  · exact (HW _).W_s _ 1 _ hG
  · rw [(D.loc _).PD_p]; exact hl
  · intro a
    have hw' := ht1w a
    have e : Wd.win a = (if Wd.up a then
        Set.Icc (Wd.sz a : ℤ) ((Wd.sz a : ℤ) + Wd.S) ∪ Set.Icc (-(Wd.η : ℤ)) Wd.η
      else Set.Icc (-(Wd.sz a : ℤ) - Wd.S) (-(Wd.sz a : ℤ)) ∪ Set.Icc (-(Wd.η : ℤ)) Wd.η) := by
      unfold NWord.win
      cases h : Wd.up a <;> ext u <;> simp [abs_le]
    rw [← e]; exact hw'
  · intro a ha
    rcases hB.num.thick_or a with h | h
    · exact absurd h ha
    · exact h

end GlobalTheory.HTW.RecS
