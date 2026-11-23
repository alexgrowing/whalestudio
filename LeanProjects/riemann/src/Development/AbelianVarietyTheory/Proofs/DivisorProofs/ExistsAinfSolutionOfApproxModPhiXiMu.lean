import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuDvdFrobXiSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfFrobeniusSemilinearEquationExistsUniqueStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.WTop

theorem mulVec_add_mul {R ι : Type} [CommRing R] [Fintype ι] (N : Matrix ι ι R) (a b : ι → R) (s : R) (i : ι) :
    N.mulVec (fun j => a j + s * b j) i = N.mulVec a i + s * N.mulVec b i := by
  simp only [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

set_option maxHeartbeats 1000000 in

theorem main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (ι : Type) [Fintype ι] (N : Matrix ι ι (Ainf p O)) (v0 : ι → Ainf p O), IsNil (WittVector.fontaineTheta O p) WittVector.frobenius N → (∀ i, WittVector.frobenius (xi ε) * Sandwich.mu ε ∣ N.mulVec (fun j => WittVector.frobenius (v0 j)) i - WittVector.frobenius (xi ε) * v0 i) → ∃ w : ι → Ainf p O, (∀ i, Sandwich.mu ε ∣ w i - v0 i) ∧ ∀ i, WittVector.frobenius (xi ε) * w i = N.mulVec (fun j => WittVector.frobenius (w j)) i := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε ι _ N v0 hN h
  choose c hc using h
  obtain ⟨z, hz⟩ := (GlobalTheory.T.ainf_frobenius_semilinear_equation_existsUnique p C v O hv ε hε ι N hN).1 c
  refine ⟨fun i => v0 i + Sandwich.mu ε * z i, fun i => ⟨z i, by ring⟩, fun i => ?_⟩
  have hw : (fun j => WittVector.frobenius (v0 j + Sandwich.mu ε * z j)) =
      fun j => WittVector.frobenius (v0 j) +
        (WittVector.frobenius (xi ε) * Sandwich.mu ε) * WittVector.frobenius (z j) := by
    funext j
    rw [map_add, map_mul, GlobalTheory.WinLift.frob_mu]
  rw [hw, mulVec_add_mul]
  linear_combination (-1 : Ainf p O) * hc i + WittVector.frobenius (xi ε) * Sandwich.mu ε * hz i

end GlobalTheory.WTop
