import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.HatSt

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

namespace UpperTheory.ConvolutionTheory.R2.G.UnipotentAverage

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E]

private theorem hat_n {D : Dat F E} (W : Weil D) (Ψ : S4 F) (ξ : Fin 2 → F) (b : A F) (g : G1 F) :
    hat (W.Om (nU b * g) Ψ).1 (pt ξ) = ψ (rt (ξ 0 ^ 2 - D.δ * ξ 1 ^ 2) * b) * hat (W.Om g Ψ).1 (pt ξ) := by
  have hH := (_root_.UpperTheory.ConvolutionTheory.R2.hatSt F E D W).n b (W.Om g Ψ) (pt ξ)
  have e : W.Om (nU b * g) Ψ = W.Om (nU b) (W.Om g Ψ) := by rw [map_mul]; rfl
  have e1 : pt ξ 1 + b * pt ξ 0 = pt ξ 1 := by simp [pt]
  have e3 : b * (pt ξ 2 ^ 2 - rt D.δ * pt ξ 3 ^ 2) = rt (ξ 0 ^ 2 - D.δ * ξ 1 ^ 2) * b := by
    simp only [pt, rt, map_sub, map_mul, map_pow]
    simp
    ring
  rw [e, hH, e1, Function.update_eq_self, e3]

private theorem hat_meas {D : Dat F E} (W : Weil D) (Ψ : S4 F) (v : V4 F) :
    Measurable fun g : G1 F => hat (W.Om g Ψ).1 v := by
  have hc : Continuous fun p : G1 F × A F =>
      (W.Om p.1 Ψ).1 (Function.update v 1 p.2) * ψ (-(p.2 * v 1)) := by
    have h2 : Continuous fun s : A F => Function.update v 1 s := continuous_const.update 1 continuous_id
    have h1 : Continuous fun p : G1 F × A F => (p.1, Function.update v 1 p.2) :=
      continuous_fst.prodMk (h2.comp continuous_snd)
    have h3 : Continuous fun s : A F => ψ (-(s * v 1)) :=
      Pp.cont_ψ.comp ((continuous_id.mul continuous_const).neg)
    exact ((W.cont Ψ).comp h1).mul (h3.comp continuous_snd)
  exact (hc.stronglyMeasurable.integral_prod_right (ν := adeleMeasure F)).measurable

end UpperTheory.ConvolutionTheory.R2.G.UnipotentAverage

open UpperTheory.ConvolutionTheory.R2.G.UnipotentAverage in
theorem UpperTheory.ConvolutionTheory.R2.G.uxAv :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (f : GL (Fin 2) (A F) → ℂ), Pp.Lf f → ∀ φ h ξ, NInv (ux W f φ h ξ) ∧ av (ux W f φ h ξ) = wx W f φ h ξ ∧
    ∀ b g, ‖ux W f φ h ξ (nU b * g)‖ = ‖f (gl (nU b * g) * dM (nu F h))‖ * ‖hat (W.Om g (W.L h φ)).1 (pt ξ)‖ := by
  intro F E _ _ _ _ _ _ _ D W f hf φ h ξ
  have hgl : ∀ x y : G1 F, gl (x * y) = gl x * gl y := fun x y => map_mul _ x y
  have hux : ∀ b g, ux W f φ h ξ (nU b * g) =
      f (gl (nU b) * (gl g * dM (nu F h))) * ψ (rt (ξ 0 ^ 2 - D.δ * ξ 1 ^ 2) * b) *
        hat (W.Om g (W.L h φ)).1 (pt ξ) := by
    intro b g
    simp only [ux]
    rw [hat_n, hgl, mul_assoc (gl (nU b)), mul_assoc]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · have h1 : Continuous fun g : G1 F => f (gl g * dM (nu F h)) :=
      hf.1.comp (_root_.UpperTheory.ConvolutionTheory.R2.M.continuous_gl.mul continuous_const)
    exact h1.measurable.mul (hat_meas W _ _)
  · intro c g
    rw [hux]
    have e : rt (ξ 0 ^ 2 - D.δ * ξ 1 ^ 2) * rt c = rt ((ξ 0 ^ 2 - D.δ * ξ 1 ^ 2) * c) := (map_mul _ _ _).symm
    have e2 : f (gl (nU (rt c)) * (gl g * dM (nu F h))) = f (gl g * dM (nu F h)) := by
      obtain ⟨γ, hγ⟩ := Pp.rat_n c
      rw [← hγ, hf.2]
    rw [e, Pp.ψ_rt, mul_one, e2]
    rfl
  · funext g
    simp only [av, wx]
    rw [← integral_mul_const]
    exact integral_congr_ae (Eventually.of_forall fun b => hux b g)
  · intro b g
    simp only [ux]
    rw [hat_n, norm_mul, norm_mul, Pp.norm_ψ, one_mul]
