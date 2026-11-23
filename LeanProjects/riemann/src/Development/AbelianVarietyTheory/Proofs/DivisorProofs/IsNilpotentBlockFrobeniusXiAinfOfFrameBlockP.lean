import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuDvdFrobXiSub
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WinLift

theorem isNil_V_blk_frob_xi :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (V : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)), (∀ i j, F.τ ∣ U i j - F.a (V i j)) → IsNil F.θ F.σ (U * blk d k (p : F.B) 1) → IsNil (WittVector.fontaineTheta O p) WittVector.frobenius (V * blk d k (WittVector.frobenius (xi ε)) 1) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F d k U V hUV hnil
  haveI : IsLocalRing O := ReciprocityTheory.PGsh.Ainf.O_local O hv
  apply isNil_of_map F.a (WittVector.fontaineTheta O p) F.θ WittVector.frobenius F.σ F.θ_a F.σ_a
  refine isNil_of_theta_eq p F.θ F.σ (Fact.out) F.σ_pow _ _ ?_ hnil
  intro i j
  have hU : F.θ (U i j) = F.θ (F.a (V i j)) := by
    obtain ⟨c, hc⟩ := hUV i j
    have h := congrArg F.θ hc
    rw [map_sub, map_mul, theta_tau F hv hε, zero_mul, sub_eq_zero] at h
    exact h
  simp only [blk, Matrix.mul_diagonal, Matrix.map_apply]
  rcases j with j | j
  · simp only [Sum.elim_inl, map_mul, map_natCast, hU, F.θ_a, theta_frob_xi hv hε]
  · simp only [Sum.elim_inr, map_mul, map_one, mul_one, hU]

end GlobalTheory.WinLift
