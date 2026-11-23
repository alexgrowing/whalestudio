import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuDvdFrobXiSub
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WinLift.NilF

theorem map_inv_transpose_blk {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (d k : ℕ)
    (M : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) R) (hM : IsUnit M) (a b : R) (i j : Fin d ⊕ Fin k) :
    f ((M.transpose⁻¹ * blk d k a b) i j) = (((M.map f).transpose)⁻¹ * blk d k (f a) (f b)) i j := by
  have hMt : IsUnit M.transpose := (Matrix.isUnit_iff_isUnit_det _).2
    (by rw [Matrix.det_transpose]; exact (Matrix.isUnit_iff_isUnit_det _).1 hM)
  have hb : (blk d k a b).map f = blk d k (f a) (f b) := by
    rw [blk, blk, Matrix.diagonal_map (map_zero f)]
    congr 1
    funext l
    rcases l with l | l <;> rfl
  have := congr_fun (congr_fun (Matrix.map_mul (f := f) (L := M.transpose⁻¹)
    (M := blk d k a b)) i) j
  rw [Matrix.map_apply] at this
  rw [this, ← map_inv_of_isUnit f _ hMt, Matrix.transpose_map, hb]

theorem isNil_frob : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (V : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)), IsUnit U → IsUnit V → (∀ i j, F.τ ∣ U i j - F.a (V i j)) → IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) → IsNil (WittVector.fontaineTheta O p) WittVector.frobenius (V.transpose⁻¹ * blk d k 1 (WittVector.frobenius (xi ε))) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F d k U V hU hV hUV hN
  haveI : IsLocalRing O := ReciprocityTheory.PGsh.Ainf.O_local O hv
  have hp : ¬IsUnit (p : O) := Fact.out
  have hθτ := theta_tau F hv hε
  have hUV' : U.map F.θ = V.map (WittVector.fontaineTheta O p) := by
    refine Matrix.ext fun i j => ?_
    obtain ⟨c, hc⟩ := hUV i j
    rw [Matrix.map_apply, Matrix.map_apply, ← F.θ_a, ← sub_eq_zero, ← map_sub, hc, map_mul, hθτ,
      zero_mul]
  refine isNil_of_map F.a (WittVector.fontaineTheta O p) F.θ WittVector.frobenius F.σ F.θ_a F.σ_a _ ?_
  refine isNil_of_theta_eq p F.θ F.σ hp F.σ_pow _ _ (fun i j => ?_) hN
  rw [Matrix.map_apply, F.θ_a, map_inv_transpose_blk F.θ d k U hU, map_inv_transpose_blk _ d k V hV,
    hUV', map_one, map_one, map_natCast, theta_frob_xi hv hε]

end GlobalTheory.WinLift.NilF
