import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.WitSys
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.PLatticeSaturatedAndCofinite
open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

theorem UpperTheory.exists_div_of_r_eq_smul_completedLattice :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (X : UpperTheory.Gal.W2.Wit.Sys D) (w : VQ D) (n : ℕ) (e : AfP p ⊗[ℚ] VQ D), w ∈ X.lat → 0 < n → n.Coprime p → e ∈ LaHat D → X.r w = n • e → ∃ u ∈ X.lat, w = n • u := by
  intro p _ D X w n e hw hn hc he hr
  have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hwu : w = n • ((n : ℚ)⁻¹ • w) := by
    rw [← Nat.cast_smul_eq_nsmul ℚ n, smul_smul, mul_inv_cancel₀ hn0, one_smul]
  have hru : X.r ((n : ℚ)⁻¹ • w) = e := by
    rw [map_smul, hr, ← Nat.cast_smul_eq_nsmul ℚ n, smul_smul, inv_mul_cancel₀ hn0, one_smul]
  refine ⟨(n : ℚ)⁻¹ • w, ⟨(UpperTheory.p_lattice_saturated_and_cofinite p D X.M X.hM).1 n _ hc ?_, ?_⟩, hwu⟩
  · rw [← hwu]; exact hw.1
  · rw [hru]; exact he
