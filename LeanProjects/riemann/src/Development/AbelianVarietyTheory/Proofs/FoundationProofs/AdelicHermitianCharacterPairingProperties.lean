import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActAApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RationalPointsIntegralPointsMembership

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil.GamAlg

theorem conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  rw [D.host.toHostAx.conjE_apply, D.host.toHostAx.conjE_apply]
  simp

theorem sgA_sgA (D : D7) (y : AE D) : sgA D (sgA D y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sgA, Formalism.UG.sigR, conj_conj]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem sum_eq_trace {R : Type} [CommRing R] (s : R →+* R) {a b : ℕ} (x y : Matrix (Fin a) (Fin b) R) :
    ∑ i, ∑ j, x i j * s (y i j) = Matrix.trace (x * (y.map s).transpose) := by
  simp [Matrix.trace, Matrix.mul_apply]

theorem trace_inv {R : Type} [CommRing R] (s : R →+* R) {a b : ℕ} (x y : Matrix (Fin a) (Fin b) R)
    (p : Matrix (Fin a) (Fin a) R) (q : Matrix (Fin b) (Fin b) R)
    (hp : (p.map s).transpose * p = 1) (hq : (q.map s).transpose * q = 1) :
    Matrix.trace (p * x * q * ((p * y * q).map s).transpose) = Matrix.trace (x * (y.map s).transpose) := by
  have hq' : q * (q.map s).transpose = 1 := mul_eq_one_comm.1 hq
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul]
  have h : p * x * q * ((q.map s).transpose * ((y.map s).transpose * (p.map s).transpose)) =
      p * (x * (q * (q.map s).transpose) * (y.map s).transpose * (p.map s).transpose) := by
    simp only [Matrix.mul_assoc]
  rw [h, hq', Matrix.mul_one, Matrix.trace_mul_comm, Matrix.mul_assoc, hp, Matrix.mul_one]

end GlobalTheory.FinWeil.GamAlg

open GlobalTheory.FinWeil.GamAlg GlobalTheory.NormSum.PtsMem in

theorem GlobalTheory.FinWeil.gamA_alg : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ ψ : AE D → ℂ, IsPsi D cc δ ψ → ∀ (N N' : ℕ), (∀ u ζ η, gamA ψ (actA D N N' u ζ) (actA D N N' u η) = gamA ψ ζ η) ∧ (∀ ζ : XA D N N', gamA ψ ζ ζ = 1) ∧ (∀ (r : 𝓞 D.host.E) (ζ η : XA D N N'), gamA ψ (r • ζ) η = gamA ψ ζ (sgO D r • η)) ∧ (∀ ζ η ξ : XA D N N', gamA ψ (ζ + η) ξ = gamA ψ ζ ξ * gamA ψ η ξ) ∧ (∀ ζ η ξ : XA D N N', gamA ψ ζ (η + ξ) = gamA ψ ζ η * gamA ψ ζ ξ) := by
  intro D _ cc δ _ ψ hψ N N'
  obtain ⟨hadd, -, -, hsg, -⟩ := hψ
  refine ⟨?_, fun ζ => ?_, fun r ζ η => ?_, fun ζ η ξ => ?_, fun ζ η ξ => ?_⟩
  · rintro ⟨g, g'⟩ ζ η
    unfold gamA
    rw [sum_eq_trace, sum_eq_trace, actA_apply, actA_apply,
      trace_inv _ _ _ _ _ ((mem_GA D _).1 g'.2) ((mem_GA D _).1 (inv_mem g.2))]
  · unfold gamA
    set t := ∑ i, ∑ j, ζ i j * sgA D (ζ i j) with ht
    have h1 : sgA D t = t := by
      simp only [ht, map_sum, map_mul, sgA_sgA]
      simp only [mul_comm]
    have h2 : t = inc D (1 / 2) * t + sgA D (inc D (1 / 2) * t) := by
      rw [map_mul, sgA_inc, h1, ← add_mul, ← map_add, map_div₀, map_one, map_ofNat, add_halves, map_one, one_mul]
    rw [h2]
    exact hsg _
  · unfold gamA
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.smul_apply, Matrix.smul_apply, smul_AE, smul_AE, map_mul, sgA_inc, coe_sgO, conj_conj]
    ring
  · unfold gamA
    rw [← hadd]
    simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib]
  · unfold gamA
    rw [← hadd]
    simp only [Matrix.add_apply, map_add, mul_add, Finset.sum_add_distrib]
