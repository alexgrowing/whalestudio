import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdaptedNormalFormGivesRealNormalFormStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticeTermAdaptedNormalFormStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryHostFieldArithmeticConditionsProofStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianStabiliserCovolumeLeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerDilationWeightsDualIsotropicVector
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormStabilizerMeasureEqAnyNormalForm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFundConjAndMeasure
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagToFrameOfNonzeroLevelIsotropicEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPtsEqImage
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFundImage

noncomputable section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals

namespace GlobalTheory.TypeAsm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem covTC_holds : CovTC := by
  intro D large₂ X Y u C hStd t N hAd μ K hμ hK
  obtain ⟨hCM, hPl, hvI, hv1, -, hcard, -, -, -, hnorm, hrk, hg2, -⟩ := GlobalTheory.T.unitaryHostFieldArithmeticConditions D large₂ hStd
  have hTerm := GlobalTheory.T.rowLattice_term_adaptedNormalForm D large₂ X Y u hStd t N hAd
  obtain ⟨β, n₁, g, n₂, hF⟩ := GlobalTheory.T.adaptedNormalForm_gives_real_normal_form D large₂ X Y u C hStd t N hAd
  have hι : Nonempty D.what₂.Tau := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.E) := inferInstance
    exact ⟨(hPl.2 w).choose⟩
  obtain ⟨τ0⟩ := id hι

  have hμeq : ∀ τ, μ τ = (GlobalTheory.Amp.lebR0 D.R.k D.R.rS N.j β).map (Formalism.QuantumDeterminants.conjM (n₂ τ)⁻¹) ∧
      SigmaFinite (GlobalTheory.Amp.lebR0 D.R.k D.R.rS N.j β) := fun τ => by
    obtain ⟨h1, h2, hinv, hFr⟩ := hF τ
    obtain ⟨-, -, -, -, ⟨c, hc⟩, -⟩ := hFr
    have hm := hμ τ
    rw [hinv] at hm
    exact GlobalTheory.Amp.StabHaar.normalFormStabilizerMeasure_eq_any_normalForm _ _ _ N.j_le _ _ _ _ _ β c _ h1 h2 hc hm
  haveI : SigmaFinite (GlobalTheory.Amp.lebR0 D.R.k D.R.rS N.j β) := (hμeq τ0).2

  have hrat := GlobalTheory.TypeAsm.gam_iff_nLam D large₂ X Y u hStd t N hAd
  have hGiso : ∀ n ∈ (N.Gam t.lam : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V)), n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    fun n hn => ((hrat n).1 hn).1.1.1
  have hpts : GlobalTheory.DegVol.realPts (phiV C) (N.Gam t.lam : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V)) = trI C '' ROinf t := by
    rw [GlobalTheory.TypeAsm.RatIsomReal.realPts_eq_image D X C _ hGiso]
    congr 1
    ext y
    constructor
    · rintro ⟨x, n, hx, rfl, hn⟩
      obtain ⟨h1, h2⟩ := (hrat n).1 hn
      exact ⟨x, n, hx, rfl, h1, h2⟩
    · rintro ⟨x, n, hx, rfl, h1, h2⟩
      exact ⟨x, n, hx, rfl, (hrat n).2 ⟨h1, h2⟩⟩
  have hfund0 := GlobalTheory.CovFund.isFund_image D X Y u C t K hK
  rw [← hpts] at hfund0
  have hRP : GlobalTheory.DegVol.RP D.R.k D.R.rS (fun τ => (gamT C t τ)⁻¹) =
      GlobalTheory.DegVol.RP D.R.k D.R.rS (fun τ => n₁ τ * g τ * n₂ τ) := by
    congr 1; funext τ; exact (hF τ).2.2.1
  rw [hRP] at hfund0

  have hunit : ∀ τ, n₁ τ ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS ∧ n₂ τ ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS ∧ IsUnit (g τ).det :=
    fun τ => ⟨(hF τ).1, (hF τ).2.1, GlobalTheory.Amp.StabHaar.unit_of_GG (hF τ).2.2.2.2.2.2.2.1.choose_spec.1⟩
  obtain ⟨hFund, hvol⟩ := GlobalTheory.DegVol.UnipConj.isFund_conj_and_measure D.host.E (VS D).V D.R.k D.R.rS D.what₂.Tau
    (phiV C) (N.Gam t.lam : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V)) n₁ g n₂ (trI C '' K)
    (GlobalTheory.Amp.lebR0 D.R.k D.R.rS N.j β) inferInstance hunit hfund0
  have hF' : ∀ τ, GlobalTheory.DegVol.IsFrameOf N D.R.k (embS D τ) (2 * Formalism.HermitianLatticesTheory.vInv D.host.E) β
      (fun y => n₂ τ *ᵥ phiV C τ y) (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u τ) (g τ) := fun τ => by
    rw [hvI]; exact (hF τ).2.2.2
  have hle := GlobalTheory.T.hermitian_stabiliser_covolume_le D.host.E (VS D).V (HV D) hCM D.R.rS N D.R.k D.what₂.Tau (embS D) β
    (fun τ y => n₂ τ *ᵥ phiV C τ y) (fun τ => zB X (C.Qi τ) u τ) (fun τ => zB X (C.Qi τ) u τ) g hPl hrk hF'
    (by rw [hAd.1, hnorm, hvI, hcard]) (by rw [hvI]; exact hv1) (gS D) t.lam _ (by omega) hTerm hFund
  have hμpi : Measure.pi μ = Measure.pi fun τ => (GlobalTheory.Amp.lebR0 D.R.k D.R.rS N.j β).map (Formalism.QuantumDeterminants.conjM (n₂ τ)⁻¹) := by
    congr 1; funext τ; exact (hμeq τ).1
  rw [hμpi, hvol]
  refine hle.trans (le_of_eq ?_)
  rw [hvI, hcard]
  rfl

end GlobalTheory.TypeAsm
