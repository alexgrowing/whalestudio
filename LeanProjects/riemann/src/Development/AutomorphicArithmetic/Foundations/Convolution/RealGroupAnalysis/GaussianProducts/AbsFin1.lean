import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.HatMeas
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.AdelicWeightFourNonneg
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.BdInv
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ZetaFin
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.CuspZero
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.KkCpt

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.absFin1 :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ h : GL (Fin 2) (A E), ((nu F h : (A F)ˣ) : A F).1 = 1 → ∑' ξ, abelian₂ M (ux W f.1 φ h ξ) ≠ ⊤ := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ h hnu
  haveI := M.prob
  haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  obtain ⟨N, hN⟩ := UpperTheory.ConvolutionTheory.R2.G.zetaFin F
  obtain ⟨B', L, hB'0, hB'⟩ := UpperTheory.ConvolutionTheory.R2.G.majL F E D W φ hφ h hnu N
  have hC : IsCompact ((fun k : G1 F => gl k * dM (nu F h)) '' KK F) :=
    (UpperTheory.ConvolutionTheory.R2.M.kkCpt F).2.image (UpperTheory.ConvolutionTheory.R2.M.continuous_gl.mul continuous_const)
  obtain ⟨B, hB0, hB⟩ := UpperTheory.ConvolutionTheory.R2.G.bdInv F π f hf _ hC
  have hLf := (UpperTheory.ConvolutionTheory.R2.Pp.cuspZero F π f hf).1
  let w : IdeleGroup F → (Fin 2 → F) → ℝ := fun a ξ =>
    wt4 L N ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F) * rt (ξ 0), (a : A F) * rt (ξ 1)]
  have hw : ∀ ξ, Continuous fun a : IdeleGroup F => w a ξ := by
    intro ξ
    have h1 : Continuous (wt4 L N : V4 F → ℝ) :=
      continuous_finset_prod _ fun i _ =>
        (GlobalTheory.CompanionTheory.EpConvB.continuous_adeleWeight L N).comp (continuous_apply i)
    refine h1.comp (continuous_pi fun i => ?_)
    fin_cases i
    · exact continuous_const
    · exact Units.continuous_coe_inv
    · exact Units.continuous_val.mul continuous_const
    · exact Units.continuous_val.mul continuous_const
  have pw : ∀ (a : IdeleGroup F), ∀ k ∈ KK F, ∀ (b : A F) (ξ : Fin 2 → F),
      ‖ux W f.1 φ h ξ (nU b * (mD a * k))‖ ≤ B * B' * w a ξ := by
    intro a k hk b ξ
    rw [(UpperTheory.ConvolutionTheory.R2.G.uxAv F E D W f.1 hLf φ h ξ).2.2 b (mD a * k)]
    have hgl : ∀ x y : G1 F, gl (x * y) = gl x * gl y := fun x y => map_mul _ x y
    have e1 : gl (nU b * (mD a * k)) * dM (nu F h) = gl (nU b * mD a) * (gl k * dM (nu F h)) := by
      rw [← mul_assoc, hgl (nU b * mD a) k, mul_assoc]
    have h1 := (hB b a _ ⟨k, hk, rfl⟩).1
    rw [← e1] at h1
    have e2 : hat (W.Om (mD a * k) (W.L h φ)).1 (pt ξ) = ((W.η.1 a : ℂˣ) : ℂ) * ((ab a : ℝ) : ℂ) *
        hat (W.Om k (W.L h φ)).1 ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F) * rt (ξ 0), (a : A F) * rt (ξ 1)] := by
      rw [map_mul, Module.End.mul_apply, (UpperTheory.ConvolutionTheory.R2.hatSt F E D W).m]
      simp [pt]
    have hη : ‖((W.η.1 a : ℂˣ) : ℂ)‖ = 1 := by
      have h2 : ((W.η.1 a : ℂˣ) : ℂ) ^ 2 = 1 := by
        have := congrArg (fun u : ℂˣ => (u : ℂ)) (W.η_sq a)
        simpa using this
      have h3 : ‖((W.η.1 a : ℂˣ) : ℂ)‖ ^ 2 = 1 := by rw [← norm_pow, h2, norm_one]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h3
    have hab : 0 < ab a := UpperTheory.ConvolutionTheory.R2.M.ab_pos a
    have h4 : ‖hat (W.Om (mD a * k) (W.L h φ)).1 (pt ξ)‖ ≤ ab a * (B' * w a ξ) := by
      rw [e2, norm_mul, norm_mul, hη, one_mul, Complex.norm_real, Real.norm_of_nonneg hab.le]
      exact mul_le_mul_of_nonneg_left (hB' k hk _) hab.le
    calc _ ≤ (B * (ab a)⁻¹) * (ab a * (B' * w a ξ)) :=
          mul_le_mul h1 h4 (norm_nonneg _) (mul_nonneg hB0 (inv_pos.2 hab).le)
      _ = B * B' * w a ξ := by field_simp
  have hae : ∀ᵐ p ∂M.ν, p.2 ∈ KK F := by
    have h0 : ∀ᵐ k ∂M.κ, k ∈ KK F := by
      rw [ae_iff]
      exact M.supp
    exact Measure.quasiMeasurePreserving_snd.ae h0
  let G : (Fin 2 → F) → IdeleGroup F → ℝ≥0∞ := fun ξ a =>
    _root_.UpperTheory.ConvolutionTheory.R2.M.wt a * ENNReal.ofReal (w a ξ)
  have hG : ∀ ξ, Measurable (G ξ) := fun ξ =>
    _root_.UpperTheory.ConvolutionTheory.R2.M.measurable_wt.mul (hw ξ).measurable.ennreal_ofReal
  have key : ∀ ξ, abelian₂ M (ux W f.1 φ h ξ) ≤ ENNReal.ofReal (B * B') * ∫⁻ a, G ξ a ∂(ideleMeasure F) := by
    intro ξ
    have hm : Measurable fun p : IdeleGroup F × G1 F => G ξ p.1 := (hG ξ).comp measurable_fst
    have e : ∫⁻ p, G ξ p.1 ∂M.ν = ∫⁻ a, G ξ a ∂(ideleMeasure F) := by
      rw [Meas.ν, lintegral_prod _ hm.aemeasurable]
      simp
    rw [← e, ← lintegral_const_mul _ hm, abelian₂, _root_.UpperTheory.ConvolutionTheory.R2.M.J0]
    refine lintegral_mono_ae (hae.mono fun p hp => ?_)
    have hb : ∫⁻ b in fundamentalSet F, ‖ux W f.1 φ h ξ (nU b * (mD p.1 * p.2))‖ₑ ∂(adeleMeasure F) ≤
        ENNReal.ofReal (B * B') * ENNReal.ofReal (w p.1 ξ) := by
      have hw0 : 0 ≤ B * B' := mul_nonneg hB0 hB'0
      calc _ ≤ ∫⁻ _ in fundamentalSet F, ENNReal.ofReal (B * B' * w p.1 ξ) ∂(adeleMeasure F) := by
            refine lintegral_mono fun b => ?_
            rw [← ofReal_norm_eq_enorm]
            exact ENNReal.ofReal_le_ofReal (pw p.1 p.2 hp b ξ)
        _ = _ := by
            rw [setLIntegral_const, adeleMeasure_fundamentalSet, mul_one, ENNReal.ofReal_mul hw0]
    calc _ ≤ _root_.UpperTheory.ConvolutionTheory.R2.M.wt p.1 * (ENNReal.ofReal (B * B') * ENNReal.ofReal (w p.1 ξ)) := by
          gcongr
      _ = _ := by
          simp only [G]
          ring
  have hsum : ∑' ξ, ∫⁻ a, G ξ a ∂(ideleMeasure F) ≠ ⊤ := by
    rw [← lintegral_tsum fun ξ => (hG ξ).aemeasurable]
    have e : ∀ a, ∑' ξ, G ξ a = _root_.UpperTheory.ConvolutionTheory.R2.M.wt a * ∑' ξ, ENNReal.ofReal (w a ξ) :=
      fun a => ENNReal.tsum_mul_left
    simp_rw [e]
    exact hN L
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum key)
  rw [ENNReal.tsum_mul_left]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hsum
