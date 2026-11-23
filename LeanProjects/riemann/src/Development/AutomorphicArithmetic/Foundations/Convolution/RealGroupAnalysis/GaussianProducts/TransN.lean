import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.HatSt

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private theorem nu_nE {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (D : Dat F E) (u : Fin 2 → A F) (h : GL (Fin 2) (A E)) :
    nu F (nE D u * h) = nu F h := by
  have hd : Matrix.GeneralLinearGroup.det (nE D u) = 1 := by
    exact Units.ext (nU (D.mkE (u 0) (u 1))).2
  simp only [nu, map_mul, hd, one_mul]

private theorem cD_unit {F : Type} [Field F] [NumberField F] (g : G1 F) : cD (1 : (A F)ˣ) g = g := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cD]

private theorem om_L {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [IsTotallyComplex E] {D : Dat F E} (W : Weil D)
    (u : Fin 2 → A F) (h : GL (Fin 2) (A E)) (φ : S4 F) (g : G1 F) :
    W.Om g (W.L (nE D u * h) φ) = W.L (nE D u) (W.Om g (W.L h φ)) := by
  have hn : nu F (nE D u) = 1 := by
    have := nu_nE D u 1
    rw [mul_one] at this
    rw [this]
    simp [nu]
  have hc := W.comm (nE D u) g
  rw [hn, cD_unit] at hc
  rw [map_mul, Module.End.mul_apply]
  exact (LinearMap.congr_fun hc (W.L h φ)).symm

theorem UpperTheory.ConvolutionTheory.R2.G.transN :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (f : GL (Fin 2) (A F) → ℂ) (φ : S4 F) (h : GL (Fin 2) (A E)) (u : Fin 2 → A F), T0 W M f φ (nE D u * h) = T0 W M f φ h ∧
    ∀ ξ, Wx W M f φ (nE D u * h) ξ = chi D.δ ξ u * Wx W M f φ h ξ := by
  intro F E _ _ _ _ _ _ _ D W M f φ h u
  have hH : St.Hat W := hatSt F E D W
  have hnu := nu_nE D u h
  constructor
  · unfold T0
    refine setIntegral_congr_fun M.meas fun g _ => ?_
    have hrow : ThRow 0 0 (W.Om g (W.L (nE D u * h) φ)).1 = ThRow 0 0 (W.Om g (W.L h φ)).1 := by
      rw [om_L]
      unfold ThRow
      refine tsum_congr fun ξ => ?_
      have := hH.nE (u 0) (u 1) (W.Om g (W.L h φ)) 0 (rt (ξ 0)) (rt (ξ 1))
      simpa [nE, zero_mul, neg_zero, ψ] using this
    simp only [hnu, hrow]
  · intro ξ
    have hpt : ∀ g, wx W f φ (nE D u * h) ξ g = chi D.δ ξ u * wx W f φ h ξ g := by
      intro g
      unfold wx
      rw [hnu, om_L]
      have := hH.nE (u 0) (u 1) (W.Om g (W.L h φ)) 1 (rt (ξ 0)) (rt (ξ 1))
      have e : hat (W.L (nE D u) (W.Om g (W.L h φ))).1 (pt ξ) =
          chi D.δ ξ u * hat (W.Om g (W.L h φ)).1 (pt ξ) := by
        simpa only [one_mul, chi, pt, nE] using this
      rw [e]
      ring
    unfold Wx Meas.I0
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [iw, hpt]
    ring
