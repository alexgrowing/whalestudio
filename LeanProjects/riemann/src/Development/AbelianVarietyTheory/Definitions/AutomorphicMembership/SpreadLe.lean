import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Formalism.LocalRingCardinality.SpanPowerMembership.FmZeroHLatEmpty
import Development.AutomorphicArithmetic.WeightCongruences.ProdNegOneZpow

noncomputable section

namespace GlobalTheory.Mem

open Formalism.BasicNotions NumberField IsDedekindDomain

structure PreX (B : Pre) where
  piG : Fin 2 → 𝓞 B.host.E
  piG_K : ∀ i, (piG i : B.host.E) ∈ B.host.K
  piG_norm : ∀ i, (piG i : B.host.E) * B.host.conj (piG i : B.host.E) = (B.host.g i : B.host.E)
  piG_cong : ∀ i, ((B.host.QS * B.host.q * B.host.d : ℕ) : 𝓞 B.host.E) ∣ piG i - 1
  piT : B.Word → 𝓞 B.host.E
  piT_K : ∀ u, (piT u : B.host.E) ∈ B.host.K
  piT_norm : ∀ u, (piT u : B.host.E) * B.host.conj (piT u : B.host.E) = (B.T u : B.host.E)
  piT_cong : ∀ u, ((B.host.QS * B.host.q * B.host.d * (B.host.g 0 * B.host.g 1) ^ 2 : ℕ) : 𝓞 B.host.E) ∣ piT u - 1
  pde_split : (Ideal.primesOver (Ideal.span {(B.host.pde : ℤ)}) (𝓞 B.host.E)).ncard = Module.finrank ℚ B.host.E ∧
    (Ideal.primesOver (Ideal.span {(B.host.pde' : ℤ)}) (𝓞 B.host.E)).ncard = Module.finrank ℚ B.host.E
  ccK_top : B.host.ccK = ⊤
  e_even : ∀ j : Fin B.R.m, UpperTheory.MUQ (fun τ : Tau B.R => B.host.emb (τ : B.R.GG)) (fun τ => (B.hc τ).e j)

  hcW_inj : Function.Injective B.hcW

  a : ℝ
  g_big : ∀ i, 2 * B.R.f * B.R.k < B.host.g i - 1
  T_gt : ∀ u, 4 * a < (B.T u : ℝ)
  a_gt : ((2 * B.R.f * B.R.N B.R.m + 1 : ℕ) : ℝ) < 4 * a
  spread_le : ∀ u j, j ≤ B.R.m → ∀ τ, ((Formalism.BasicNotions.Examples₂.lamOf (B.hcW u τ) j).spread : ℝ) ≤ 2 * a

def Base.tauLL (B : Base) (τ : Tau B.R) : B.host.E →+* B.LL :=
  B.embE.comp (B.host.sigmaOf (τ : B.R.GG) : B.host.E →+* B.host.E)

end GlobalTheory.Mem

end
