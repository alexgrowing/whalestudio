import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishingStatement
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CuspSquareIntegrableIffUnfolded
import Development.AbelianVarietyTheory.Proofs.HeightProofs.VolPairExAndFinVol
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagQuotientIntegralEqUniversalConstMulStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

noncomputable section
namespace GlobalTheory.LevGeo

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem adelicProb_mul_volFund : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (x0 : ∀ k, Frame ((U σ).X k).Ψ D.R.r) (FF : ∀ k, Set (ReciprocityTheory.L2DbarEstimates.V (nd ((U σ).X k)))), (∀ k, IsOrth ((U σ).X k) (x0 k) ∧ IsFundSet ((U σ).X k) (x0 k) (FF k)) → (∑ k, muF ((U σ).X k) (x0 k) (FF k)) ≠ 0 ∧ (∑ k, muF ((U σ).X k) (x0 k) (FF k)) ≠ ⊤ ∧ ∀ Φ : ∀ k, Frame ((U σ).X k).Ψ D.R.r → ℝ≥0∞, (∀ k, Measurable (Φ k)) → (∀ k, ∀ γ ∈ ((U σ).X k).Γ, ∀ x ∈ ((U σ).X k).dom, Φ k (lact γ x) = Φ k x) → (∀ k, ∀ b ∈ Bor ((U σ).X k).Ψ D.R.r, ∀ x ∈ ((U σ).X k).dom, Φ k (rmul x b) = Φ k x) → (∫⁻ q, Φ (dict σ q.out).1 (dict σ q.out).2 ∂(muQ1 (D.sp.W j))) * ∑ k, muF ((U σ).X k) (x0 k) (FF k) = ∑ k, ∫⁻ z in FF k, Φ k (cpt ((U σ).X k) (x0 k) z) ∂(muF ((U σ).X k) (x0 k)) := by
  intro D j H Dw l Xo c U dict hL σ hσ x0 FF hFF
  obtain ⟨hP, hV⟩ := GlobalTheory.FinalJoin2.volPairEx_and_finVol D (D.sp.W j) (D.sp.W_sig j)
  have hvp := Formalism.L2.Pj.volPair_isVolPair (D.sp.W j) hP
  haveI : (Formalism.L2.Pj.volPair (D.sp.W j)).1.IsHaarMeasure := hvp.1.1
  have h0 : (Formalism.L2.Pj.volPair (D.sp.W j)).1 (Formalism.L2.Pj.volPair (D.sp.W j)).2 ≠ 0 :=
    Formalism.L2.Pj.muQ_univ (D.sp.W j) ▸ hV.1
  have h1 : (Formalism.L2.Pj.volPair (D.sp.W j)).1 (Formalism.L2.Pj.volPair (D.sp.W j)).2 ≠ ⊤ :=
    Formalism.L2.Pj.muQ_univ (D.sp.W j) ▸ hV.2
  obtain ⟨Kf, th, hr, hK, hth, hd, hu⟩ := hL.dictU σ hσ
  have hU := hL.unf σ hσ
  have hΨ : ∀ k k', ((U σ).X k).Ψ = ((U σ).X k').Ψ ∧ ((U σ).X k).p0 = ((U σ).X k').p0 := fun k k' =>
    ⟨Finset.ext fun τ => ((hU.2.1 k).2 τ).trans ((hU.2.1 k').2 τ).symm, (hU.2.1 k).1.trans (hU.2.1 k').1.symm⟩
  have hM : 0 < l.M := by have := l.three_le; omega
  obtain ⟨κ, hκ0, hκ1, hI⟩ := GlobalTheory.PeterssonCompare.lintegral_adelic (D.sp.W j) (U σ).X (dict σ) hM hth hd hK hu hΨ
    _ hvp.2 h0 h1
  set k0 := (dict σ 1).1
  obtain ⟨κ2, h20, h21, hH⟩ := GlobalTheory.T.flagQuotientIntegral_eq_universal_const_mul D.R.r Dw.q ((U σ).X k0).Ψ.card
  have hQ : ∀ k (F : Frame ((U σ).X k).Ψ D.R.r → ℝ≥0∞), Measurable F →
      (∀ γ ∈ ((U σ).X k).Γ, ∀ x ∈ ((U σ).X k).dom, F (lact γ x) = F x) →
      (∀ b ∈ Bor ((U σ).X k).Ψ D.R.r, ∀ x ∈ ((U σ).X k).dom, F (rmul x b) = F x) →
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.quotInt ((U σ).X k) F = κ2 * ∫⁻ z in FF k, F (cpt ((U σ).X k) (x0 k) z) ∂(muF ((U σ).X k) (x0 k)) :=
    fun k F hF hΓ hB => hH D.host.E ((U σ).X k) (hU.2.1 k).1 (by rw [(hΨ k k0).1]) (x0 k) (FF k) F (hFF k).1 (hFF k).2
      hF hΓ hB
  have key : ∀ F : ∀ k, Frame ((U σ).X k).Ψ D.R.r → ℝ≥0∞, (∀ k, Measurable (F k)) →
      (∀ k, ∀ γ ∈ ((U σ).X k).Γ, ∀ x ∈ ((U σ).X k).dom, F k (lact γ x) = F k x) →
      (∀ k, ∀ b ∈ Bor ((U σ).X k).Ψ D.R.r, ∀ x ∈ ((U σ).X k).dom, F k (rmul x b) = F k x) →
      ∫⁻ q, F (dict σ q.out).1 (dict σ q.out).2 ∂(muQ1 (D.sp.W j)) =
        ((Formalism.L2.Pj.volPair (D.sp.W j)).1 (Formalism.L2.Pj.volPair (D.sp.W j)).2)⁻¹ *
          (κ * ∑ k, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.quotInt ((U σ).X k) (F k)) := by
    intro F hF hΓ hB
    obtain ⟨h2, h3⟩ := hI F hF hΓ hB
    have hout : ∀ g, F (dict σ (Formalism.L2.Pj.autMk (D.sp.W j) g).out).1 (dict σ (Formalism.L2.Pj.autMk (D.sp.W j) g).out).2 =
        F (dict σ g).1 (dict σ g).2 := by
      intro g
      have h4 : g * (Formalism.L2.Pj.autMk (D.sp.W j) g).out⁻¹ ∈ GQ (D.sp.W j) :=
        QuotientGroup.rightRel_apply.1 (Quotient.mk_out g)
      obtain ⟨γ, hγ, e⟩ := hd.1 _ h4 (Formalism.L2.Pj.autMk (D.sp.W j) g).out
      rw [inv_mul_cancel_right] at e
      rw [e]
      exact (hΓ _ γ hγ _ (hd.2.2.2.1 _)).symm
    have hq : Measurable fun q : Formalism.L2.Pj.AutQ (D.sp.W j) => F (dict σ q.out).1 (dict σ q.out).2 := by
      rw [measurable_from_quotient]
      have : ((fun q : Formalism.L2.Pj.AutQ (D.sp.W j) => F (dict σ q.out).1 (dict σ q.out).2) ∘ Quotient.mk'') =
          fun g => F (dict σ g).1 (dict σ g).2 := funext hout
      rw [this]
      exact h2
    have h5 : ∫⁻ q, F (dict σ q.out).1 (dict σ q.out).2 ∂(Formalism.L2.Pj.muQ (D.sp.W j)) =
        κ * ∑ k, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.quotInt ((U σ).X k) (F k) := by
      rw [Formalism.L2.Pj.muQ, lintegral_map hq (Formalism.L2.Pj.autMk_measurable (D.sp.W j))]
      simp only [hout]
      exact h3
    rw [Formalism.L2.Pj.muQ1, if_pos (show Formalism.L2.Pj.muQ (D.sp.W j) Set.univ ≠ 0 ∧ Formalism.L2.Pj.muQ (D.sp.W j) Set.univ ≠ ⊤
      from hV), lintegral_smul_measure, h5, Formalism.L2.Pj.muQ_univ, smul_eq_mul]
  have e1 := key (fun _ _ => 1) (fun _ => measurable_const) (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
  rw [Finset.sum_congr rfl fun k _ => hQ k (fun _ => 1) measurable_const (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl),
    ← Finset.mul_sum] at e1
  simp only [setLIntegral_one, lintegral_const, measure_univ, mul_one, one_mul, Measure.restrict_apply_univ] at e1
  have hv0 : ((Formalism.L2.Pj.volPair (D.sp.W j)).1 (Formalism.L2.Pj.volPair (D.sp.W j)).2)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 h1
  refine ⟨fun hS => ?_, fun hS => ?_, fun Φ hΦ hΓ hB => ?_⟩
  · rw [hS, mul_zero, mul_zero, mul_zero] at e1
    exact one_ne_zero e1
  · rw [hS, ENNReal.mul_top h20, ENNReal.mul_top hκ0, ENNReal.mul_top hv0] at e1
    exact ENNReal.one_ne_top e1
  · rw [key Φ hΦ hΓ hB, Finset.sum_congr rfl fun k _ => hQ k (Φ k) (hΦ k) (hΓ k) (hB k), ← Finset.mul_sum]
    calc _ = (∑ k, ∫⁻ z in FF k, Φ k (cpt ((U σ).X k) (x0 k) z) ∂(muF ((U σ).X k) (x0 k))) *
          (((Formalism.L2.Pj.volPair (D.sp.W j)).1 (Formalism.L2.Pj.volPair (D.sp.W j)).2)⁻¹ *
            (κ * (κ2 * ∑ k, muF ((U σ).X k) (x0 k) (FF k)))) := by ring
      _ = _ := by rw [← e1, mul_one]

end GlobalTheory.LevGeo
