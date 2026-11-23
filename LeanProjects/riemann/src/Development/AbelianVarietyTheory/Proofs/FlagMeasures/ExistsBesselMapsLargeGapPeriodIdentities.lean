import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPtRepTrDat
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.SBridge
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.JEqOrbInt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TorusNormaliserBessel
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryTorusScaleBesselCharacter
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalizedBesselMapsAnyScalePieriConstantsStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselGapExistsFunctionalStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsQuotientMeasureBesselPeriodSubgroupUnitary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieIsHaarOnUnipotentRadical
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselPeriodPositivity
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocInOfUniqOfDecLow
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp
noncomputable section

namespace GlobalTheory.AmpTKGap

variable {k r : ℕ}

theorem side_bessel (hH : GlobalTheory.GapIn.Hyp) (L : LocBessel k r) (h : ℝ) (hgap : GapAtLeast L.ε L.lam h)
    (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h) (hc : L.c ≠ 0) (hκ0 : 0 < L.κN) (hκt : L.κN ≠ ⊤)
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp))
    (u : Fin k → ℝ) (μW : Measure (Mt k r)) (hz : inWb k r z) (hT : 0 < Tz k r z) (hπ : IsHCTypeW k r z u π)
    (hW : IsHaarOn (UWset k r z) μW) :
    ∃ l : L.Hs → Wp, (∀ x ∈ (GlobalTheory.AmpTK.rep L).sm, ∀ v ∈ (GlobalTheory.AmpTK.rep L).TK,
      Formalism.FourierDecayAlt.ThreeDimData.be z L.c π L.σ μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x)) ∧ GlobalTheory.AmpTK.SmCW L l := by
  haveI := FiniteDimensional.complete ℂ Wp
  obtain ⟨μG, hG⟩ := GlobalTheory.SnMass.Inhab.exists_isHaarOn k r
  have hN := GlobalTheory.haarLie_isHaarOn_Nset k r L.κN hκ0 hκt.lt_top
  obtain ⟨νq, hq⟩ := GlobalTheory.exists_isQuotMeas_bessel_subgroup k r z μW L.μN μG hz hT hW hN hG
  obtain ⟨U, hS⟩ := GlobalTheory.AmpNormal.sideG_of hκt.lt_top hz hT hπ hW hG hq
  obtain ⟨t, ht, htN, htz, -⟩ := GlobalTheory.TorusScale.exists_torus_scale k r L.c hc
  obtain ⟨-, htc, hψ⟩ := htz z hz
  have hR : Formalism.MainNotions.S.IsURepOn (GG k r) (GlobalTheory.AmpTK.rep L).σ := GlobalTheory.Amp.LocalInputs.urep_of_ds L.hσ
  obtain ⟨hS', hB⟩ := GlobalTheory.T.isBesselMap_conj_iff_and_besselFn_eq_rankOne hH k r Wp z π U L.c μW L.μN μG νq t ht htN htc hψ hS
  obtain ⟨-, hbe⟩ := hB (GlobalTheory.AmpTK.rep L) hR
  have hDG : (GlobalTheory.AmpTK.rep L).IsDG L.ε L.lam := ⟨L.hlam, L.hσ, h, hgap, hok⟩
  obtain ⟨l₁, hl₁⟩ := Gp91.GlobalTheory.T.bessel_gap_exists_functional hH.1 k r L.ε L.lam h (GlobalTheory.AmpTK.rep L) Wp z π U μW _ μG _ hDG hgap hok hS'
  have hti := GlobalTheory.BesselMove.inv_mem ht
  refine ⟨fun v => l₁ ((GlobalTheory.AmpTK.rep L).σ t⁻¹ v), fun x hx v hv => hbe l₁ hl₁ x hx v hv, ?_, ?_, ?_⟩
  · intro v hv w hw
    show l₁ ((GlobalTheory.AmpTK.rep L).σ t⁻¹ (v + w)) = _
    rw [map_add]
    exact hl₁.1.1 _ (GlobalTheory.BesselMove.sig_sm hR hti hv) _ (GlobalTheory.BesselMove.sig_sm hR hti hw)
  · intro a v hv
    show l₁ ((GlobalTheory.AmpTK.rep L).σ t⁻¹ (a • v)) = _
    rw [map_smul]
    exact hl₁.1.2.1 _ _ (GlobalTheory.BesselMove.sig_sm hR hti hv)
  · exact GlobalTheory.SmMapAct.cw_comp (GlobalTheory.BesselMove.smMap_sigma hR hti) hl₁.1.2.2.2

theorem exists_besselTK : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (h : ℝ),
    Formalism.QuantumDeterminants.GapAtLeast L.ε L.lam h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → L.c ≠ 0 → 0 < L.κN → L.κN ≠ ⊤ →
    ∃ (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq), GlobalTheory.AmpTK.BeTK L l l' ∧ GlobalTheory.AmpTK.SmCW L l ∧ GlobalTheory.AmpTK.SmCW L l' := by
  intro hH k r L h hgap hok hc hκ0 hκt
  obtain ⟨l, hl, hsl⟩ := side_bessel hH L h hgap hok hc hκ0 hκt L.z L.π L.u L.μW L.hz.1 L.hz.2 L.hπ L.hμW.1
  obtain ⟨l', hl', hsl'⟩ := side_bessel hH L h hgap hok hc hκ0 hκt L.z' L.π' L.u' L.μW' L.hz'.1 L.hz'.2 L.hπ' L.hμW'.1
  exact ⟨l, l', ⟨hl, hl'⟩, hsl, hsl'⟩

end GlobalTheory.AmpTKGap
