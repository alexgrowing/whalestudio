import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.HenselQuad
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.SecondConstantOfGaussSum
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HeightShare

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.PairingIndexBounds.Eq.J

open Formalism.MainNotions Formalism.L2.PairingIndexBounds.Eq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem star_sqrt_neg (x : D.host.E) (n : ℕ) (hn : 0 < n) (hx : x ^ 2 = -(n : D.host.E)) : star x = -x :=
  _root_.UpperTheory.Reformulated.B.HeightShare.star_sqrt_neg x n hn hx

theorem isIntegral_sqrt (x : D.host.E) (n : ℕ) (hx : x ^ 2 = -(n : D.host.E)) : IsIntegral ℤ x := by
  refine ⟨Polynomial.X ^ 2 + Polynomial.C (n : ℤ), Polynomial.monic_X_pow_add_C _ two_ne_zero, ?_⟩
  simp [hx]

theorem isIntegral_int (k : ℤ) : IsIntegral ℤ (k : D.host.E) := by
  have := isIntegral_algebraMap (R := ℤ) (A := D.host.E) (x := k)
  simpa using this

theorem negOneNorm (D : D7) : NegOneNorm D := by
  intro m hm
  obtain ⟨hq, hd, hq8, hd16, -⟩ := D.host.hyp
  have hqd : D.host.q ≠ D.host.d := by omega
  obtain ⟨α, β, γ, δ, s, h⟩ := Neg.rep_int D.host.q D.host.d hq hd hq8 hqd m hm
  have ha : (D.host.sqq : D.host.E) ^ 2 = -(D.host.q : D.host.E) :=
    D.host.sqq_sq
  have hb : (D.host.sqd : D.host.E) ^ 2 = -(D.host.d : D.host.E) :=
    D.host.sqd_sq
  obtain ⟨a, haa⟩ : ∃ a : D.host.E, a = D.host.sqq := ⟨_, rfl⟩
  obtain ⟨b, hbb⟩ : ∃ b : D.host.E, b = D.host.sqd := ⟨_, rfl⟩
  rw [← haa] at ha
  rw [← hbb] at hb
  have hsa := star_sqrt_neg a _ hq.pos ha
  have hsb := star_sqrt_neg b _ hd.pos hb
  have hint : IsIntegral ℤ (((α : D.host.E) + β * a) * ((γ : D.host.E) + δ * b)) :=
    ((isIntegral_int α).add ((isIntegral_int β).mul (isIntegral_sqrt a _ ha))).mul
      ((isIntegral_int γ).add ((isIntegral_int δ).mul (isIntegral_sqrt b _ hb)))
  refine ⟨⟨_, hint⟩, ⟨_, isIntegral_int s⟩, ?_, ?_⟩
  · show star (s : D.host.E) = (s : D.host.E)
    exact star_intCast s
  · show star (((α : D.host.E) + β * a) * ((γ : D.host.E) + δ * b)) * (((α : D.host.E) + β * a) * ((γ : D.host.E) + δ * b)) =
      -1 + (m : D.host.E) * (s : D.host.E)
    have hZ : ((α : D.host.E) ^ 2 + D.host.q * (β : D.host.E) ^ 2) * ((γ : D.host.E) ^ 2 + D.host.d * (δ : D.host.E) ^ 2) =
        -1 + (m : D.host.E) * (s : D.host.E) := by exact_mod_cast congrArg (Int.cast : ℤ → D.host.E) h
    rw [star_mul', star_add, star_add, star_mul', star_mul', star_intCast, star_intCast, star_intCast, star_intCast,
      hsa, hsb]
    linear_combination hZ + (-(β : D.host.E) ^ 2 * ((γ : D.host.E) ^ 2 - (δ : D.host.E) ^ 2 * b ^ 2)) * ha +
      (-((α : D.host.E) ^ 2 + D.host.q * (β : D.host.E) ^ 2) * (δ : D.host.E) ^ 2) * hb

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {B : Ker.Base D cc δ}

theorem eqP_of_paths (B : Ker.Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hδ0 : δ ≠ 0)
    (hS : B.StdOK) (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ)
    (hSq : SqP D B.tor) (hTL : Tr0L D B.tor) (hTR : Tr0R D B.tor) : B.EqP χ :=
  eqP_of_neg B hcc hδ hδ0 hS χ hχ hSq hTL hTR (negOneNorm D)

end Formalism.L2.PairingIndexBounds.Eq.J
