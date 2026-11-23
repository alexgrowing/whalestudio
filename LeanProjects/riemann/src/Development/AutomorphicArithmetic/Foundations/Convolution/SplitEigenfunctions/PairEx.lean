import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ProdBd
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.IILaws
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.DerCurve
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CoefZero
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.MeanZero
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.UnitsCpt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Stable
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SpanCont

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.V.Z.Bc
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.RankTwoDescent

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E]

private theorem bd_zero : Bd (fun _ : GL (Fin 2) (A E) => (0 : ℂ)) :=
  ⟨continuous_const, fun _ _ => rfl, fun _ _ => ⟨0, fun _ _ _ => by simp⟩⟩

private theorem ii_zero (N : MeasE E) : II N (fun _ => 0) = 0 := by
  simp [II, UI, mean]

private theorem ii_add (N : MeasE E) {Ψ Ψ' : GL (Fin 2) (A E) → ℂ} (h : Bd Ψ) (h' : Bd Ψ') :
    (II N fun x => Ψ x + Ψ' x) = II N Ψ + II N Ψ' := by
  simpa using (iiLaws E N Ψ h).1 Ψ' h' 1

private theorem ii_smul (N : MeasE E) {Ψ : GL (Fin 2) (A E) → ℂ} (h : Bd Ψ) (c : ℂ) :
    (II N fun x => c * Ψ x) = c * II N Ψ := by
  simpa [ii_zero] using (iiLaws E N _ bd_zero).1 Ψ h c

end SlopeTestRemainingChoices

end UpperTheory.ConvolutionTheory.RankTwoDescent

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.pairEx :
    PairEx := by
  intro E _ _ _ D W M N P hn π hπ
  have hb : ∀ (x : span W M π) (y : P.V), Bd fun g => x.1.1 g * y.1.1 g :=
    fun x y => (prodBd E D W M N P π x.1 x.2 y.1 y.2).1
  have hc : ∀ (x : span W M π) (y : P.V), PosC fun g => x.1.1 g * y.1.1 g :=
    fun x y => (prodBd E D W M N P π x.1 x.2 y.1 y.2).2 hπ hn
  have st : IsStable (span W M π) := UpperTheory.ConvolutionTheory.R2.stable ℚ E D W M π
  let B : span W M π →ₗ[ℂ] P.V →ₗ[ℂ] ℂ := LinearMap.mk₂ ℂ (fun x y => II N fun g => x.1.1 g * y.1.1 g)
    (fun x x' y => (congrArg (II N) (funext fun g => add_mul (x.1.1 g) (x'.1.1 g) (y.1.1 g))).trans
      (ii_add N (hb x y) (hb x' y)))
    (fun c x y => (congrArg (II N) (funext fun g => mul_assoc c (x.1.1 g) (y.1.1 g))).trans
      (ii_smul N (hb x y) c))
    (fun x y y' => (congrArg (II N) (funext fun g => mul_add (x.1.1 g) (y.1.1 g) (y'.1.1 g))).trans
      (ii_add N (hb x y) (hb x y')))
    (fun c x y => (congrArg (II N) (funext fun g => mul_left_comm (x.1.1 g) c (y.1.1 g))).trans
      (ii_smul N (hb x y) c))
  have hB : ∀ x y, B x y = II N fun g => x.1.1 g * y.1.1 g := fun _ _ => rfl
  refine ⟨B, ⟨st, P.stable, fun k x y => ?_, fun k x y => ?_, fun X x y => ?_⟩, hB, fun x hx => ?_⟩
  · exact (iiLaws E N _ (hb x y)).2 (hc x y) (finGL E 2 k)
  · exact (iiLaws E N _ (hb x y)).2 (hc x y) (infGL E 2 (Unitary.toUnits k))
  · exact iiLie E N x.1 y.1 X (hb x y) (hc x y) (hb ⟨_, st (.lie X) _ x.2⟩ y) (hb x ⟨_, P.stable (.lie X) _ y.2⟩)
  · refine LinearMap.ext fun y => ?_
    have hcx := UpperTheory.ConvolutionTheory.R2.H.spanCont ℚ E D W M π x.1 x.2
    have hk := killW E D x.1.1 hcx.1 hcx.2 hx
    have h0 : ∀ t : (A E)ˣ, (mean N fun g => x.1.1 (g * aE t) * y.1.1 (g * aE t)) = 0 := by
      intro t
      have e : ∫ h in N.D, y.1.1 (gl h * aE t) ∂N.μ = 0 := meanZero decE E D W M N P y.1 y.2 (aE t)
      show ∫ h in N.D, x.1.1 (gl h * aE t) * y.1.1 (gl h * aE t) ∂N.μ = 0
      simp only [hk]
      rw [integral_const_mul, e, mul_zero]
    show (II N fun g => x.1.1 g * y.1.1 g) = 0
    simp [II, UI, h0]
