import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftEqAnisotropicPart
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.RowCosets
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Iwa
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousQuaternaryQuadraticForm
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ContinuousPrN
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.MeasurableAl
import Development.AutomorphicArithmetic.UnipotentInvariants.IntegralTsumRowSectionEqZeroOfConstantTermEqZero
import Development.AutomorphicArithmetic.UnipotentInvariants.ExistsEquivRowSelectionUnitsIsotropicVectors
import Development.AutomorphicArithmetic.UnipotentInvariants.ExistsUnipotentInvariantSetUniqueRowScaling

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

private theorem om_L {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {D : Dat ℚ E} (W : Weil D) (g : G1 ℚ) (ph : S4 ℚ)
    {h : GL (Fin 2) (A E)} (hn : nu ℚ h = 1) (v : V4 ℚ) :
    (W.Om g (W.L h ph)).1 v = (W.Om g ph).1 (D.act h⁻¹ v) := by
  have hc := W.comm h g
  rw [hn, M.cD_one] at hc
  have h1 : W.Om g (W.L h ph) = W.L h (W.Om g ph) := (congrArg (fun T => T ph) hc).symm
  rw [h1, W.L_apply, hn, M.ab_one]
  simp

private theorem rat_gl {E : Type} [Field E] [NumberField E] (γ : Matrix.SpecialLinearGroup (Fin 2) E) :
    gl (ratS E γ) = ratGL E 2 (Matrix.SpecialLinearGroup.toGL γ) := by
  apply Units.ext; rfl

end UpperTheory.ConvolutionTheory.RankTwoDescent

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.rank1 :
    DecE → Maj → Orb1 → Rank1 := by
  intro hD hM hO E _ _ _ D W M₀ N P ph hph φ hφ g y hy
  obtain ⟨hLf, hcus, -⟩ := hD E P φ hφ
  obtain ⟨b0, a0, k0, hk0, hg⟩ := M.iwa ℚ g
  obtain ⟨B, hB⟩ := hM E D W M₀ N P ph hph φ hφ {y} isCompact_singleton (by simpa using hy) (ab a0) (M.ab_pos a0) 0
  have hb : ∀ h : G1 E, Summable (fun ξ : Fin 4 → ℚ => ‖(W.Om g (W.L (gl h * y) ph)).1 (rp ξ)‖) ∧
      (∑' ξ : Fin 4 → ℚ, ‖(W.Om g (W.L (gl h * y) ph)).1 (rp ξ)‖) * ‖φ.1 (gl h * y)‖ ≤ B * ab a0 ^ 2 := by
    intro h
    obtain ⟨h1, h2, -⟩ := hB b0 a0 k0 hk0 le_rfl h y rfl
    rw [hg]
    exact ⟨h1, h2⟩
  obtain ⟨⟨σ, hσ⟩, -⟩ := M.rowCosets E
  obtain ⟨T, hTm, hTn, hTs⟩ := UpperTheory.exists_unipotentInvariant_set_unique_row_scaling torCo E
  have glm : ∀ a b : G1 E, gl (a * b) = gl a * gl b := fun a b => map_mul Matrix.SpecialLinearGroup.toGL a b
  have hnu : ∀ x : G1 E, nu ℚ (gl x * y) = 1 := fun x => by rw [nu_mul, nu_gl, hy, one_mul]
  set F : G1 E → (Fin 4 → ℚ) → ℂ := fun x ξ => (W.Om g (W.L (gl x * y) ph)).1 (rp ξ) with hF
  have hFe : ∀ x ξ, F x ξ = (W.Om g ph).1 (D.act (gl x * y)⁻¹ (rp ξ)) := fun x ξ => om_L W g ph (hnu x) _
  have hFc : ∀ ξ, Continuous fun x => F x ξ := by
    intro ξ
    simp only [hFe]
    have h1 : Continuous fun x : G1 E => (gl x * y)⁻¹ := (M.continuous_gl.mul continuous_const).inv
    have h2 := D.continuous_act' h1 (continuous_const (y := rp ξ))
    exact ((W.cont (ph)).comp (continuous_const (y := g) |>.prodMk h2))
  have hinj : Function.Injective fun s : ℚˣ => (![0, (s : ℚ), 0, 0] : Fin 4 → ℚ) := by
    intro s s' h
    exact Units.ext (by simpa using congrFun h 1)
  have hsu : ∀ x, Summable fun s : ℚˣ => F x ![0, (s : ℚ), 0, 0] := fun x =>
    ((hb x).1.comp_injective hinj).of_norm
  set u : G1 E → ℂ := fun x => ∑' s : ℚˣ, F x ![0, (s : ℚ), 0, 0] with hu
  have hum : Measurable u := by
    refine measurable_of_tendsto_metrizable' (u := atTop) (f := fun (S : Finset ℚˣ) x => ∑ s ∈ S, F x ![0, (s : ℚ), 0, 0])
      (fun S => Finset.measurable_sum _ fun s _ => (hFc _).measurable) (tendsto_pi_nhds.2 fun x => (hsu x).hasSum)
  have hun : ∀ b x, u (nU b * x) = u x := by
    intro b x
    refine tsum_congr fun s => ?_
    have h5 := (hO E D).2.2.2.2 (-b) s
    have h6 : (gl (nU b))⁻¹ = gl (nU (-b)) := by rw [M.nU_neg]; exact (map_inv Matrix.SpecialLinearGroup.toGL (nU b)).symm
    rw [hFe, hFe, glm, mul_assoc, _root_.mul_inv_rev, Dat.act_mul, h6, h5]
  set Aa : G1 E → ℂ := T.indicator u with hA
  set c : G1 E → ℂ := fun x => φ.1 (gl x * y) with hc
  have hAm : Measurable Aa := hum.indicator hTm
  have hcm : Measurable c := (hLf.1.comp (M.continuous_gl.mul continuous_const)).measurable
  have hAn : ∀ b x, Aa (nU b * x) = Aa x := by
    intro b x
    by_cases hx : x ∈ T
    · rw [hA, Set.indicator_of_mem hx, Set.indicator_of_mem ((hTn b x).2 hx), hun]
    · rw [hA, Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx ((hTn b x).1 h))]
  have hcl : ∀ γ x, c (ratS E γ * x) = c x := by
    intro γ x
    change φ.1 (gl (ratS E γ * x) * y) = φ.1 (gl x * y)
    rw [glm, rat_gl, mul_assoc]
    exact hLf.2 _ _
  have h0 : ∀ x, ∫ b in fundamentalSet E, c (nU b * x) ∂(adeleMeasure E) = 0 := by
    intro x
    have := hcus (gl x * y)
    simpa only [hc, glm, mul_assoc] using this
  have hact : ∀ (x : G1 E) (γ : Matrix.SpecialLinearGroup (Fin 2) E) (ξ ξ' : Fin 4 → ℚ),
      rp ξ' = D.act (gl (ratS E γ))⁻¹ (rp ξ) → F (ratS E γ * x) ξ = F x ξ' := by
    intro x γ ξ ξ' h
    rw [hFe, hFe, h, glm, mul_assoc, _root_.mul_inv_rev, Dat.act_mul]
  have hSel : ∀ x, ∃ e : ↥{r' : {r : Fin 2 → E // r ≠ 0} | ratS E (σ r') * x ∈ T} × ℚˣ ≃ ↥{ξ : Fin 4 → ℚ | ξ ≠ 0 ∧ qr D.δ ξ = 0},
      ∀ r s, rp (e (r, s)).1 = D.act (gl (ratS E (σ r.1)))⁻¹ (rp ![0, (s : ℚ), 0, 0]) :=
    fun x => UpperTheory.exists_equiv_rowSelection_units_isotropicVectors D σ _ hO hσ (hTs σ hσ x)
  have hind : ∀ x r, Aa (ratS E (σ r) * x) =
      Set.indicator {r' : {r : Fin 2 → E // r ≠ 0} | ratS E (σ r') * x ∈ T} (fun r => u (ratS E (σ r) * x)) r := by
    intro x r
    by_cases h : ratS E (σ r) * x ∈ T
    · rw [hA, Set.indicator_of_mem h, Set.indicator_of_mem (show r ∈ {r' : {r : Fin 2 → E // r ≠ 0} | ratS E (σ r') * x ∈ T} from h)]
    · rw [hA, Set.indicator_of_notMem h, Set.indicator_of_notMem (show r ∉ {r' : {r : Fin 2 → E // r ≠ 0} | ratS E (σ r') * x ∈ T} from h)]
  have hTh : ∀ x, ThOn {ξ | ξ ≠ 0 ∧ qr D.δ ξ = 0} (W.Om g (W.L (gl x * y) ph)).1 = ∑' r, Aa (ratS E (σ r) * x) := by
    intro x
    obtain ⟨e, he⟩ := hSel x
    have hs0 : Summable fun ξ : ↥{ξ : Fin 4 → ℚ | ξ ≠ 0 ∧ qr D.δ ξ = 0} => F x ξ.1 :=
      ((hb x).1.comp_injective Subtype.val_injective).of_norm
    have hs : Summable fun p => F x (e p).1 := e.summable_iff.2 hs0
    change ∑' ξ : ↥{ξ : Fin 4 → ℚ | ξ ≠ 0 ∧ qr D.δ ξ = 0}, F x ξ.1 = _
    rw [← e.tsum_eq (fun ξ => F x ξ.1), hs.tsum_prod]
    simp_rw [hind]
    rw [← tsum_subtype]
    refine tsum_congr fun r => tsum_congr fun s => ?_
    exact (hact x (σ r.1) _ _ (he r s)).symm
  have hbd : ∀ x, ∑' r, ‖Aa (ratS E (σ r) * x) * c x‖ₑ ≤ ENNReal.ofReal (B * ab a0 ^ 2) := by
    intro x
    obtain ⟨e, he⟩ := hSel x
    have h1 : ∑' r, ‖Aa (ratS E (σ r) * x)‖ₑ ≤ ∑' ξ : Fin 4 → ℚ, ‖F x ξ‖ₑ := by
      calc ∑' r, ‖Aa (ratS E (σ r) * x)‖ₑ
          = ∑' r, Set.indicator {r' : {r : Fin 2 → E // r ≠ 0} | ratS E (σ r') * x ∈ T} (fun r => ‖u (ratS E (σ r) * x)‖ₑ) r := by
            refine tsum_congr fun r => ?_
            rw [hind]
            by_cases h : r ∈ {r' : {r : Fin 2 → E // r ≠ 0} | ratS E (σ r') * x ∈ T}
            · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
            · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, enorm_zero]
        _ = ∑' r : ↥{r' : {r : Fin 2 → E // r ≠ 0} | ratS E (σ r') * x ∈ T}, ‖u (ratS E (σ r.1) * x)‖ₑ :=
            (tsum_subtype _ (fun r => ‖u (ratS E (σ r) * x)‖ₑ)).symm
        _ ≤ ∑' r : ↥{r' : {r : Fin 2 → E // r ≠ 0} | ratS E (σ r') * x ∈ T}, ∑' s : ℚˣ, ‖F x (e (r, s)).1‖ₑ := by
            refine ENNReal.tsum_le_tsum fun r => enorm_tsum_le_tsum_enorm.trans_eq (tsum_congr fun s => ?_)
            rw [hact x (σ r.1) _ _ (he r s)]
        _ = ∑' p, ‖F x (e p).1‖ₑ := ENNReal.tsum_prod.symm
        _ = ∑' ξ : ↥{ξ : Fin 4 → ℚ | ξ ≠ 0 ∧ qr D.δ ξ = 0}, ‖F x ξ.1‖ₑ := e.tsum_eq fun ξ => ‖F x ξ.1‖ₑ
        _ ≤ ∑' ξ : Fin 4 → ℚ, ‖F x ξ‖ₑ := ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _
    have h2 : ∑' ξ : Fin 4 → ℚ, ‖F x ξ‖ₑ = ENNReal.ofReal (∑' ξ : Fin 4 → ℚ, ‖F x ξ‖) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hb x).1]
      exact tsum_congr fun ξ => (ofReal_norm_eq_enorm _).symm
    calc ∑' r, ‖Aa (ratS E (σ r) * x) * c x‖ₑ = (∑' r, ‖Aa (ratS E (σ r) * x)‖ₑ) * ‖c x‖ₑ := by
          simp only [enorm_mul]; exact ENNReal.tsum_mul_right
      _ ≤ ENNReal.ofReal (∑' ξ : Fin 4 → ℚ, ‖F x ξ‖) * ‖c x‖ₑ := by rw [← h2]; gcongr
      _ = ENNReal.ofReal ((∑' ξ : Fin 4 → ℚ, ‖F x ξ‖) * ‖c x‖) := by
          rw [ENNReal.ofReal_mul (tsum_nonneg fun _ => norm_nonneg _), ofReal_norm_eq_enorm]
      _ ≤ ENNReal.ofReal (B * ab a0 ^ 2) := ENNReal.ofReal_le_ofReal (hb x).2
  have hfin : (∫⁻ x in N.D, ∑' r, ‖Aa (ratS E (σ r) * x) * c x‖ₑ ∂N.μ) ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono hbd) ?_)
    rw [setLIntegral_const]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (volE E N)
  have hz := UpperTheory.integral_tsum_rowSection_eq_zero_of_constantTerm_eq_zero N σ Aa c hσ hAm hcm hAn hcl h0 hfin
  change ∫ h in N.D, ThOn {ξ | ξ ≠ 0 ∧ qr D.δ ξ = 0} (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y) ∂N.μ = 0
  rw [← hz]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  change ThOn {ξ | ξ ≠ 0 ∧ qr D.δ ξ = 0} (W.Om g (W.L (gl x * y) ph)).1 * c x = ∑' r, Aa (ratS E (σ r) * x) * c x
  rw [hTh, tsum_mul_right]
