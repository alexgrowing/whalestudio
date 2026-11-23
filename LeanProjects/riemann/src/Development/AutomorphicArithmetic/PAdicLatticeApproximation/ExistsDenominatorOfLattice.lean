import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.WitSys
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.PLatticeSaturatedAndCofinite
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsPPowSmulEqOfMemCompletedLattice
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsDenominatorRationalTensor
open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

private lemma exists_den_finset {p : ℕ} [Fact p.Prime] (D : Datum p) (s : Finset (VQ D)) :
    ∃ k : ℕ, 0 < k ∧ ∀ x ∈ s, ∃ a : D.La, k • x = (1 : ℚ) ⊗ₜ[ℤ] a :=
  _root_.UpperTheory.Reformulated.B.Qh61.exists_den_finset D s

private lemma exists_den_closure {p : ℕ} [Fact p.Prime] (D : Datum p) (s : Finset (VQ D)) :
    ∃ k : ℕ, 0 < k ∧ ∀ x ∈ AddSubgroup.closure (s : Set (VQ D)),
      ∃ a : D.La, k • x = (1 : ℚ) ⊗ₜ[ℤ] a := by
  obtain ⟨k, hk, hs⟩ := exists_den_finset D s
  refine ⟨k, hk, fun x hx => ?_⟩
  induction hx using AddSubgroup.closure_induction with
  | mem x hx => exact hs x hx
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [smul_add, ha, hb, TensorProduct.tmul_add]⟩
  | neg x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨-a, by rw [smul_neg, ha, TensorProduct.tmul_neg]⟩

theorem UpperTheory.exists_denominator_of_lattice :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (X : UpperTheory.Gal.W2.Wit.Sys D), ∃ d : ℕ, 0 < d ∧ ∀ w ∈ X.lat, ∃ a : D.La, d • w = (1 : ℚ) ⊗ₜ[ℤ] a := by
  intro p _ D X
  obtain ⟨-, s, -, hmem⟩ := X.hM
  obtain ⟨k, hk, hkc⟩ := exists_den_closure D s
  obtain ⟨j, hj, -, hjS⟩ := GlobalTheory.LKGeo.DenEnd.exists_coprime_nsmul_map_mem p D X.S
  refine ⟨k * j, Nat.mul_pos hk hj, fun w hw => ?_⟩
  obtain ⟨m, hm, hc⟩ := (hmem w).1 hw.1
  obtain ⟨a₁, ha₁⟩ := hkc _ hc
  have hST : X.S (X.r w) = (1 : AfP p) ⊗ₜ[ℚ] w := by
    have h := congrArg (fun f => f ((1 : AfP p) ⊗ₜ[ℚ] w)) X.ST
    simpa [UpperTheory.Gal.W2.Wit.Sys.r_apply] using h
  have hin : (1 : AfP p) ⊗ₜ[ℚ] (j • w) ∈ LaHat D := by
    have h := hjS _ hw.2
    rw [hST] at h
    rwa [TensorProduct.tmul_smul]
  obtain ⟨r, a₂, ha₂⟩ := UpperTheory.exists_p_pow_smul_eq_of_mem_completedLattice p D (j • w) hin
  have hcop : IsCoprime (m : ℤ) ((p ^ r : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_right r hm)
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨(u * j) • a₁ + (v * k) • a₂, ?_⟩
  have e₁ : ((k : ℤ) * m) • w = (1 : ℚ) ⊗ₜ[ℤ] a₁ := by
    rw [← ha₁, smul_smul, ← Nat.cast_mul, natCast_zsmul]
  have e₂ : (((p ^ r : ℕ) : ℤ) * j) • w = (1 : ℚ) ⊗ₜ[ℤ] a₂ := by
    rw [← ha₂, smul_smul, ← Nat.cast_mul, natCast_zsmul]
  rw [TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul, ← e₁, ← e₂,
    smul_smul, smul_smul, ← add_smul, ← natCast_zsmul]
  congr 1
  push_cast at huv ⊢
  linear_combination (-(k : ℤ) * j) * huv
