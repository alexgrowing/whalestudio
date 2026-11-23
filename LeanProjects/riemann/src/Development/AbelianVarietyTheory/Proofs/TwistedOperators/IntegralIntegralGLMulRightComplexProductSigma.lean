import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockTriangularOneAddMat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus

open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology
open scoped ENNReal

namespace GlobalTheory.SmGL.IndDual

section Real

open GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
  [MeasurableSpace k] [BorelSpace k]

theorem integral_KO_mul_right_real (μ : Measure (GL n k)) [μ.IsHaarMeasure] {f : GL n k → ℝ}
    (hf : Continuous f) (hlaw : ∀ (p : parab k e) x, f (p * x) = modulus k m (leviProj k e p) * f x)
    (g : GL n k) :
    ∫ x in (KO k n : Set (GL n k)), f (x * g) ∂μ = ∫ x in (KO k n : Set (GL n k)), f x ∂μ := by
  have h1 : IntegrableOn (fun x => f (x * g)) (KO k n : Set (GL n k)) μ :=
    (hf.comp (continuous_mul_const g)).continuousOn.integrableOn_compact isCompact_KO
  have h2 : IntegrableOn f (KO k n : Set (GL n k)) μ := hf.continuousOn.integrableOn_compact isCompact_KO
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part h1,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part h2,
    UnitInd.lintegral_KO_mul_right e μ (φ := fun x => ENNReal.ofReal (f x)) hf.measurable.ennreal_ofReal
      (fun p x => by rw [hlaw, ENNReal.ofReal_mul (modulus_pos k _).le]) g,
    UnitInd.lintegral_KO_mul_right e μ (φ := fun x => ENNReal.ofReal (-f x)) hf.neg.measurable.ennreal_ofReal
      (fun p x => by rw [hlaw, ← mul_neg, ENNReal.ofReal_mul (modulus_pos k _).le]) g]

theorem integral_integralGL_mul_right_complex_productSigma (μ : Measure (GL n k)) [μ.IsHaarMeasure] {F : GL n k → ℂ}
    (hF : Continuous F) (hlaw : ∀ (p : parab k e) x, F (p * x) = (modulus k m (leviProj k e p) : ℂ) * F x)
    (g : GL n k) :
    ∫ x in (KO k n : Set (GL n k)), F (x * g) ∂μ = ∫ x in (KO k n : Set (GL n k)), F x ∂μ := by
  have h1 : IntegrableOn (fun x => F (x * g)) (KO k n : Set (GL n k)) μ :=
    (hF.comp (continuous_mul_const g)).continuousOn.integrableOn_compact isCompact_KO
  have h2 : IntegrableOn F (KO k n : Set (GL n k)) μ := hF.continuousOn.integrableOn_compact isCompact_KO
  have hre := integral_KO_mul_right_real e μ (Complex.continuous_re.comp hF)
    (fun p x => by simp [hlaw]) g
  have him := integral_KO_mul_right_real e μ (Complex.continuous_im.comp hF)
    (fun p x => by simp [hlaw]) g
  refine Complex.ext ?_ ?_
  · exact ((integral_re h1).symm.trans hre).trans (integral_re h2)
  · exact ((integral_im h1).symm.trans him).trans (integral_im h2)

end Real

theorem integral_KO_mul_right : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) [MeasurableSpace (GL n k)] [BorelSpace (GL n k)] (μ : Measure (GL n k)) [μ.IsHaarMeasure] (F : GL n k → ℂ), Continuous F → (∀ (p : parab k e) (g : GL n k), F (p * g) = (modulus k m (leviProj k e p) : ℂ) * F g) → ∀ g : GL n k, ∫ x in (KO k n : Set (GL n k)), F (x * g) ∂μ = ∫ x in (KO k n : Set (GL n k)), F x ∂μ := by
  intro k _ _ _ _ α n m _ _ _ _ _ _ e M hM μ _ F hF hlaw g
  borelize k
  obtain rfl : M = Units.instMeasurableSpace :=
    hM.measurable_eq.trans (SplitFlip.borel_GL (k := k) (n := n)).measurable_eq.symm
  exact integral_integralGL_mul_right_complex_productSigma e μ hF hlaw g

end GlobalTheory.SmGL.IndDual
