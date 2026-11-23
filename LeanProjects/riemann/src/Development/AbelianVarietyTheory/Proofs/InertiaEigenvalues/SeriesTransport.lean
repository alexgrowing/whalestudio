import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDiscExtensionTateElement

noncomputable section

namespace GlobalTheory.HWL.Cmp

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct Matrix

section Cz

variable {L : Type} [Field L]

theorem cz_neg (f : PowerSeries L) {k : ℤ} (hk : k < 0) : cz f k = 0 := by
  simp [cz, not_le.mpr hk]

theorem cz_nat (f : PowerSeries L) (k : ℕ) : cz f (k : ℤ) = PowerSeries.coeff k f := by
  simp [cz]

theorem cz_add (f g : PowerSeries L) (k : ℤ) : cz (f + g) k = cz f k + cz g k := by
  unfold cz; split_ifs <;> simp

theorem cz_sum {ι : Type} (s : Finset ι) (f : ι → PowerSeries L) (k : ℤ) :
    cz (∑ i ∈ s, f i) k = ∑ i ∈ s, cz (f i) k := by
  unfold cz; split_ifs <;> simp

theorem cz_C_mul (c : L) (f : PowerSeries L) (k : ℤ) : cz (PowerSeries.C c * f) k = c * cz f k := by
  unfold cz; split_ifs <;> simp

theorem cz_rescale (c : L) (f : PowerSeries L) (k : ℤ) :
    cz (PowerSeries.rescale c f) k = c ^ k * cz f k := by
  rcases lt_or_ge k 0 with h | h
  · simp [cz_neg _ h]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    simp [cz_nat, PowerSeries.coeff_rescale]

theorem cz_X_pow_mul (w : ℕ) (f : PowerSeries L) (k : ℤ) :
    cz (PowerSeries.X ^ w * f) (k + (w : ℤ)) = cz f k := by
  rcases lt_or_ge k 0 with h | h
  · rw [cz_neg _ h]
    rcases lt_or_ge (k + (w : ℤ)) 0 with h' | h'
    · exact cz_neg _ h'
    · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le h'
      rw [hm, cz_nat, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    rw [← Nat.cast_add, cz_nat, cz_nat, PowerSeries.coeff_X_pow_mul]

theorem cz_mul (g f : PowerSeries L) (k : ℤ) (N : ℕ) (hN : k < (N : ℤ)) :
    cz (g * f) k = ∑ i ∈ Finset.range N, PowerSeries.coeff i g * cz f (k - (i : ℤ)) := by
  rcases lt_or_ge k 0 with h | h
  · rw [cz_neg _ h]
    refine (Finset.sum_eq_zero fun i _ => ?_).symm
    rw [cz_neg _ (by omega), mul_zero]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    rw [cz_nat, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rw [← Finset.sum_subset (Finset.range_subset_range.mpr (show m + 1 ≤ N by omega))]
    · refine Finset.sum_congr rfl fun i hi => ?_
      have : i ≤ m := by simpa [Nat.lt_succ_iff] using hi
      rw [← Nat.cast_sub this, cz_nat]
    · intro i _ hi
      have : m < i := by simpa using hi
      rw [cz_neg _ (by omega), mul_zero]

theorem series_transport {M M' : Type} [AddCommGroup M] [Module L M] [AddCommGroup M'] [Module L M']
    {r r' : ℕ} (w w' : ℕ) (A : Fin r' → PowerSeries L) (Bs : Fin r → PowerSeries L) (κ : L) (hκ : κ ≠ 0)
    (g : PowerSeries L) (c : Fin r' → Fin r → L)
    (hA : ∀ j, (PowerSeries.C κ * PowerSeries.X) ^ w * A j =
      PowerSeries.X ^ w' * (g * ∑ p, PowerSeries.C (c j p) * PowerSeries.rescale κ (Bs p)))
    (h : M →ₗ[L] M') (D : Fin r → M) (D' : Fin r' → M') (hD : ∀ p, h (D p) = ∑ j, c j p • D' j) (k : ℤ) :
    ∑ j, cz (A j) (k + (w' : ℤ)) • D' j = ∑ᶠ i : ℕ, PowerSeries.coeff i g •
      (κ ^ (k - (i : ℤ)) • h (∑ p, cz (Bs p) (k - (i : ℤ) + (w : ℤ)) • D p)) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, k + (w : ℤ) < (N : ℤ) := ⟨(k + (w : ℤ)).toNat + 1, by omega⟩
  rw [finsum_eq_sum_of_support_subset (s := Finset.range N)]
  · have key : ∀ j, cz (A j) (k + (w' : ℤ)) = ∑ i ∈ Finset.range N, ∑ p, PowerSeries.coeff i g *
        (κ ^ (k - (i : ℤ)) * (cz (Bs p) (k - (i : ℤ) + (w : ℤ)) * c j p)) := by
      intro j
      have h1 := congrArg (fun f => cz f (k + (w : ℤ) + (w' : ℤ))) (hA j)
      rw [cz_X_pow_mul, mul_pow, ← map_pow, mul_assoc, cz_C_mul, add_right_comm, cz_X_pow_mul,
        cz_mul _ _ _ N hN] at h1
      apply mul_left_cancel₀ (pow_ne_zero w hκ)
      rw [h1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [cz_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [cz_C_mul, cz_rescale, show k + (w : ℤ) - (i : ℤ) = k - (i : ℤ) + (w : ℤ) by ring, zpow_add₀ hκ,
        zpow_natCast]
      ring
    simp only [key, Finset.sum_smul, map_sum, map_smul, hD, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
  · intro i hi
    by_contra hc
    apply hi
    have : N ≤ i := by simpa using hc
    have hz : ∀ p, cz (Bs p) (k - (i : ℤ) + (w : ℤ)) = 0 := fun p => cz_neg _ (by omega)
    simp [hz]

end Cz

theorem basis_transport {C S : Type} [CommRing C] [CommRing S] (J : C →+* S) (σ : C →+* C) (σS : S →+* S)
    (hJ : ∀ a, J (σ a) = σS (J a)) {M M' : Type} [AddCommGroup M] [Module S M] [AddCommGroup M'] [Module S M']
    (h : M →+ M') (hh : ∀ (a : S) m, h (a • m) = σS a • h m) (t q : C) (ht : IsUnit (J t)) (hq : IsUnit (J q))
    {r r' : ℕ} (w w' : ℕ) (bn d : Fin r → M) (bn' d' : Fin r' → M') (U : Fin r → Fin r → C)
    (U' : Fin r' → Fin r' → C) (H Cm : Fin r' → Fin r → C)
    (hd : ∀ j, J t ^ w • d j = ∑ i, J (U i j) • bn i) (hd' : ∀ j, J t ^ w' • d' j = ∑ i, J (U' i j) • bn' i)
    (hH : ∀ j, J q • h (bn j) = ∑ i, J (H i j) • bn' i)
    (hU : ∀ k p, t ^ w' * ∑ i, H k i * σ (U i p) = σ t ^ w * q * ∑ j, U' k j * Cm j p) (p : Fin r) :
    h (d p) = ∑ j, J (Cm j p) • d' j := by
  have hu : IsUnit (J t ^ w' * σS (J t) ^ w * J q) := ((ht.pow _).mul ((ht.map σS).pow _)).mul hq
  apply hu.smul_left_cancel.mp
  have e1 : (J t ^ w' * σS (J t) ^ w * J q) • h (d p) =
      ∑ k, J (t ^ w' * ∑ i, H k i * σ (U i p)) • bn' k := by
    have : (J t ^ w' * σS (J t) ^ w * J q) • h (d p) = J t ^ w' • J q • h (J t ^ w • d p) := by
      rw [hh, map_pow, smul_smul, smul_smul]
      congr 1
      ring
    rw [this, hd, map_sum, Finset.smul_sum, Finset.smul_sum]
    simp only [hh, smul_comm (J q), hH, Finset.smul_sum, smul_smul, map_mul, map_sum, map_pow, hJ,
      Finset.mul_sum, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    congr 1
    ring
  have e2 : (J t ^ w' * σS (J t) ^ w * J q) • ∑ j, J (Cm j p) • d' j =
      ∑ k, J (σ t ^ w * q * ∑ j, U' k j * Cm j p) • bn' k := by
    have : ∀ j, (J t ^ w' * σS (J t) ^ w * J q) • J (Cm j p) • d' j =
        (σS (J t) ^ w * J q * J (Cm j p)) • J t ^ w' • d' j := by
      intro j
      rw [smul_smul, smul_smul]
      congr 1
      ring
    rw [Finset.smul_sum]
    simp only [this, hd', Finset.smul_sum, smul_smul, map_mul, map_sum, map_pow, hJ,
      Finset.mul_sum, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    congr 1
    ring
  rw [e1, e2]
  simp only [hU]

theorem coord_transport {A : Type} [CommRing A] (σ : A →+* A) {r r' : ℕ} (U V : Matrix (Fin r) (Fin r) A)
    (U' V' : Matrix (Fin r') (Fin r') A) (H Cm : Matrix (Fin r') (Fin r) A) (q q' : A)
    (hq : ∀ a, q * a = 0 → a = 0) (hUV : U * V = 1) (hUV' : U' * V' = 1)
    (hU : H * U.map σ = q • (U' * Cm)) (c : Fin r → A) (c' : Fin r' → A)
    (hc : q • c' = q' • H *ᵥ (σ ∘ c)) : V' *ᵥ c' = q' • Cm *ᵥ (σ ∘ (V *ᵥ c)) := by
  have h1 : V' * H = q • (Cm * V.map σ) := by
    have h2 : U.map σ * V.map σ = 1 := by
      rw [← Matrix.map_mul, hUV, Matrix.map_one _ (map_zero σ) (map_one σ)]
    calc V' * H = V' * (H * U.map σ) * V.map σ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one]
      _ = q • (Cm * V.map σ) := by
          rw [hU, Matrix.mul_smul, ← Matrix.mul_assoc, mul_eq_one_comm.mp hUV', Matrix.one_mul, Matrix.smul_mul]
  have h3 : σ ∘ (V *ᵥ c) = V.map σ *ᵥ (σ ∘ c) := by
    funext i
    exact RingHom.map_mulVec σ V c i
  have h4 : q • (V' *ᵥ c') = q • (q' • Cm *ᵥ (σ ∘ (V *ᵥ c))) := by
    rw [← Matrix.mulVec_smul, hc, Matrix.mulVec_smul, Matrix.mulVec_mulVec, h1, h3, Matrix.mulVec_mulVec,
      Matrix.smul_mulVec, smul_comm]
  funext i
  have h5 := congrFun h4 i
  simp only [Pi.smul_apply, smul_eq_mul] at h5 ⊢
  exact sub_eq_zero.mp (hq _ (by rw [mul_sub, h5, sub_self]))

end GlobalTheory.HWL.Cmp
