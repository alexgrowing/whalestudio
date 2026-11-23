import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply

noncomputable section

namespace GlobalTheory.FockFamily

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

def blockB (J : (V × V) →ₗ[ℝ] (V × V)) : V →L[ℝ] V :=
  LinearMap.toContinuousLinearMap (LinearMap.fst ℝ V V ∘ₗ J ∘ₗ LinearMap.inr ℝ V V)

def blockD (J : (V × V) →ₗ[ℝ] (V × V)) : V →L[ℝ] V :=
  LinearMap.toContinuousLinearMap (LinearMap.snd ℝ V V ∘ₗ J ∘ₗ LinearMap.inr ℝ V V)

theorem blockB_apply (J : (V × V) →ₗ[ℝ] (V × V)) (q : V) : blockB J q = (J (0, q)).1 := rfl

theorem blockD_apply (J : (V × V) →ₗ[ℝ] (V × V)) (q : V) : blockD J q = (J (0, q)).2 := rfl

def fockForm (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : (V × V) →ₗ[ℝ] (V × V)) : V →ₗ[ℝ] V →ₗ[ℝ] ℂ :=
  LinearMap.mk₂ ℝ
    (fun x y => ((Real.pi * β x (Ring.inverse (blockB J) y) : ℝ) : ℂ) +
      (Real.pi : ℂ) * Complex.I * ((β x (blockD J (Ring.inverse (blockB J) y)) : ℝ) : ℂ))
    (fun x x' y => by simp only [map_add, LinearMap.add_apply]; push_cast; ring)
    (fun c x y => by simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Complex.real_smul]; push_cast; ring)
    (fun x y y' => by simp only [map_add]; push_cast; ring)
    (fun c x y => by simp only [map_smul, smul_eq_mul, Complex.real_smul]; push_cast; ring)

theorem fockForm_apply (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : (V × V) →ₗ[ℝ] (V × V)) (x y : V) :
    fockForm β J x y = ((Real.pi * β x (Ring.inverse (blockB J) y) : ℝ) : ℂ) +
      (Real.pi : ℂ) * Complex.I * ((β x (blockD J (Ring.inverse (blockB J) y)) : ℝ) : ℂ) := rfl

end GlobalTheory.FockFamily

end
