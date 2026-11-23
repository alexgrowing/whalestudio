import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LogMulDegFlBracketMul
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PowerSumHeightChangeModelStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LimitHeightConstantShiftStatement
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem power_sum_term_linked_tower : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (II : IntersectionSystem), IsIntersectionSystem II → T.Proportional → ∀ φ : ℕ → Equiv.Perm (Ψ ⊕ Ψ), LinkedTower T II φ → T.Prop6 II fun p τ n => (φ p ^ (n + 1)) (Sum.inl τ) := by
  intro Ψ _ _ N T II hII hprop φ hL
  intro B₀ B hB₀ hB c τ k hk1 hkN Q hQ
  obtain ⟨M, R, S, hS, hMc, hRc, hMPP, hRPP, hgeo, hch, hloc⟩ := hL B₀ B hB₀ hB c
  have hstep := GlobalTheory.T.limit_height_constant_shift Ψ N M R.model II hMc hRc (toA (pk τ k * Q))
    (∑ p ∈ S, Real.log (p : ℕ) * M.geoFun (toA (bracket T.j (φ p) p k τ * Q)))
    (fun t ht => GlobalTheory.T.power_sum_height_change_model Ψ N M R II hII S T.j φ hch hloc t ht τ k hk1 hkN Q hQ)
  rw [hMPP, hRPP] at hstep
  rw [hstep]
  congr 1
  have hSeq : S.map ⟨(fun p : Nat.Primes => (p : ℕ)), Nat.Primes.coe_nat_injective⟩ =
      (Finset.Ioc B₀ B).filter (fun p => p.Prime ∧ p ∉ T.bad) := by
    ext n
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_Ioc, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨p, hp, rfl⟩
      have h := (hS p).1 hp
      exact ⟨⟨h.1, h.2.1⟩, p.2, h.2.2⟩
    · rintro ⟨⟨h1, h2⟩, hpr, hbad⟩
      exact ⟨⟨n, hpr⟩, (hS _).2 ⟨h1, h2, hbad⟩, rfl⟩
  rw [← hSeq, Finset.sum_map, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  change _ = T.vol c * deltaTerm T.j (p : ℕ) τ (fun n => (φ (p : ℕ) ^ (n + 1)) (Sum.inl τ)) k Q
  rw [hgeo, hprop.2.1, ← log_mul_degFl_bracket_mul Ψ N T.j p k p.2.two_le hk1 (φ p) τ Q]
  ring

end GlobalTheory.CompanionTheory.Ar.Num
