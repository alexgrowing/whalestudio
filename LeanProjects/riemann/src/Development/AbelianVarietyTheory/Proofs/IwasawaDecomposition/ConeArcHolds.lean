import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPAdicArcBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PowerSeriesArcAbelianLocus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliPartOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelPointsEqOfSameDegenerationData
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AdmissibleBasePowerSeriesSpanX
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcPhiDivisorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcIntegralStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArcAdmissibleBaseStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArcBaseUniformizerStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.ConeArc

theorem coneArc : ConeArcSt := by
  intro E _ _ _ H D h1 Xo l c hg X ψ k DX htame hpol
  obtain ⟨-, hPI⟩ := GlobalTheory.partI_closed
  obtain ⟨Ys, hYs, -⟩ := hPI E H D h1 Xo
  rw [arcChart_iff]
  intro O' _ _ _ b ϖ a hbase
  obtain ⟨p, W, hp, hW, bV, b', hbV, rfl⟩ := GlobalTheory.ArcBaseFactor.factor E H l c O' b ϖ hbase
  have hN4 := ((hYs p W hp hW).2 ⟨l, c, hg p hp⟩).2.2
  rw [arcChart_iff] at hN4
  obtain ⟨χ₀, hχ₀, hsp₀⟩ := hN4 O' b' ϖ (GlobalTheory.PolArc.moveV bV hbV b' a) hbase
  have hc₀ := (hχ₀ χ₀).1 rfl
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.PolArc.generic_factors_open E H D l (Xo l) c W _ O' b' χ₀ hc₀.1 hc₀.2.1
  obtain ⟨χ, hχ⟩ := GlobalTheory.T.pullback_model_arc_phi_divisor E H D l (Xo l) c p W hp hW X _ bV hbV ψ k DX htame.1 hpol O' b' ϖ a χ₀ hbase hc₀ x₀ hx₀
  have hc := GlobalTheory.T.pullback_model_arc_integral E H D l (Xo l) c p W hp hW X _ bV hbV O' b' ϖ a χ₀ hbase hc₀ x₀ hx₀ χ hχ
  refine ⟨χ, fun χ' => ⟨?_, fun h => ?_⟩, fun hirr y' ev hy' hgen hdata hev hevX =>
    GlobalTheory.T.arc_base_uniformizer E H D l (Xo l) c W X _ bV hbV O' b' ϖ a χ₀ hbase hc₀ hsp₀ x₀ hx₀ χ hχ hirr y' ev hy' hgen hdata hev hevX⟩
  · rintro rfl
    exact hc
  · have hϖ : ϖ ≠ 0 := by
      rcases hbase with ⟨-, rfl⟩ | ⟨-, hi, -⟩
      · exact one_ne_zero
      · exact hi.ne_zero
    have hR : AdmBase (PowerSeries O') (Ideal.span {PowerSeries.X}) := by
      rcases hbase with ⟨hf, -⟩ | ⟨hd, -, -⟩
      · letI := hf.toField
        exact GlobalTheory.ArcPull.admissibleBase_powerSeries_span_X O'
      · exact GlobalTheory.ArcPull.admissibleBase_powerSeries_span_X O'
    haveI hloc : IsLocalRing (PowerSeries O') := by
      rcases hbase with ⟨hf, -⟩ | ⟨hd, -, -⟩
      · letI := hf.toField
        infer_instance
      · infer_instance
    have : CharZero (PowerSeries O') := charZero_of_injective_ringHom (PowerSeries.C_injective (R := O'))
    have hI : Ideal.span {(PowerSeries.X : PowerSeries O')} ≠ ⊤ := by
      rw [Ne, Ideal.span_singleton_eq_top]
      exact PowerSeries.X_prime.not_unit
    have hgen : ∀ χ₁ : Sp (PowerSeries O') ⟶ X.X, IsArcChart X a ϖ χ₁ →
        Set.range (Out.jK (PowerSeries O') ≫ χ₁) ⊆ Set.range X.j := by
      rintro χ₁ h₁ _ ⟨z, rfl⟩
      rw [Scheme.Hom.comp_apply]
      refine h₁.2.2.1 _ ?_
      have hz : (Out.jK (PowerSeries O') z).asIdeal = ⊥ := by
        have hz' : z.asIdeal = ⊥ := by haveI := z.isPrime; exact Ideal.eq_bot_of_prime _
        change Ideal.comap (algebraMap (PowerSeries O') (FractionRing (PowerSeries O'))) z.asIdeal = ⊥
        rw [hz']
        exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective _ _)
      rw [hz, Ideal.mem_bot]
      refine mul_ne_zero (fun h => hϖ ?_) PowerSeries.X_ne_zero
      simpa using congrArg (fun q : PowerSeries O' => PowerSeries.coeff 0 q) h
    exact GlobalTheory.T.arc_admissible_base E H D l (Xo l) c X O' (b'.comp bV) a (PowerSeries O') _ PowerSeries.C PowerSeries.X hR hI
      PowerSeries.C_injective χ' χ (hgen χ' h) (hgen χ hc) h.1 hc.1 h.2.2.2 hc.2.2.2

end GlobalTheory.ConeArc
