import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.LatticeCountPrimeMonoLevel

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem dvd_pow_of_vLEO {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ}
    (hp0 : (p : O) ≠ 0) (hpm : ¬ IsUnit (p : O)) {z : O} (hz : z ≠ 0) {D : ℕ} (h : vLEO p z D) :
    z ∣ (p : O) ^ D := by
  classical
  unfold vLEO at h
  obtain ⟨q, hq, hqD⟩ := h
  unfold vO vK ordW at hq
  have hx0 : algebraMap O (KK O) z ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (KK O))).mpr hz
  rw [if_neg hx0] at hq
  dsimp only at hq
  have hspec := Classical.choose_spec (IsLocalization.surj (nonZeroDivisors O) (algebraMap O (KK O) z))
  generalize Classical.choose (IsLocalization.surj (nonZeroDivisors O) (algebraMap O (KK O) z)) = ab
    at hq hspec
  have h1 : ab.1 = z * (ab.2 : O) := by
    apply IsFractionRing.injective O (KK O)
    rw [map_mul]
    exact hspec.symm
  have hs0 : (ab.2 : O) ≠ 0 := nonZeroDivisors.coe_ne_zero ab.2
  have hzt : IsDiscreteValuationRing.addVal O z ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  have hst : IsDiscreteValuationRing.addVal O (ab.2 : O) ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  have hpt : IsDiscreteValuationRing.addVal O (p : O) ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  rw [h1, AddValuation.map_mul, ENat.toNat_add hzt hst] at hq
  simp only [Nat.cast_add, add_sub_cancel_right, WithTop.map_coe, WithTop.coe_inj] at hq
  have he1 : 1 ≤ ramE p O := by
    unfold ramE
    by_contra hlt
    have h0 : (IsDiscreteValuationRing.addVal O (p : O)).toNat = 0 := by omega
    have h0' : IsDiscreteValuationRing.addVal O (p : O) = 0 := by
      rcases ENat.toNat_eq_zero.mp h0 with h | h
      · exact h
      · exact absurd h hpt
    apply hpm
    apply isUnit_of_dvd_one
    rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, h0']
    exact zero_le
  have hepos : (0 : ℝ) < (ramE p O : ℝ) := by exact_mod_cast he1
  have hreal : ((IsDiscreteValuationRing.addVal O z).toNat : ℝ) ≤ (D : ℝ) * (ramE p O : ℝ) := by
    rw [← hq] at hqD
    push_cast at hqD
    rwa [div_le_iff₀ hepos] at hqD
  have hnat : (IsDiscreteValuationRing.addVal O z).toNat ≤ D * ramE p O := by exact_mod_cast hreal
  unfold ramE at hnat
  rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, AddValuation.map_pow, ← ENat.coe_toNat hzt,
    ← ENat.coe_toNat hpt, nsmul_eq_mul]
  exact_mod_cast hnat

theorem isUnit_det_of_one_add {O : Type*} [CommRing O] [IsLocalRing O] {M : ℕ} (P : Matrix (Fin M) (Fin M) O)
    (h : ∀ i l, P i l - (1 : Matrix (Fin M) (Fin M) O) i l ∈ IsLocalRing.maximalIdeal O) : IsUnit P.det := by
  have hmap : P.map (IsLocalRing.residue O) = 1 := by
    ext i l
    have h2 : IsLocalRing.residue O (P i l) =
        IsLocalRing.residue O ((1 : Matrix (Fin M) (Fin M) O) i l) := by
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
      exact h i l
    rw [Matrix.map_apply, h2, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply, hmap,
    Matrix.det_one]
  exact one_ne_zero

theorem goodRank_core {O Kf X : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup X] [Module O X]
    (π : O) (A : Submodule O X) {M : ℕ} (φ : Fin M → X → Kf) (D : ℕ)
    (hadd : ∀ i G G', φ i (G + G') = φ i G + φ i G') (hsmul : ∀ i (c : O) G, φ i (c • G) = algebraMap O Kf c * φ i G)
    (Y : Fin M → X) (hY : ∀ l, Y l ∈ A) (P : Matrix (Fin M) (Fin M) O) (zc zc' : Fin M → O)
    (hz : ∀ l, zc' l * zc l = π ^ D) (hφ : ∀ i l, φ i (Y l) = algebraMap O Kf (P i l * zc l))
    (hP : IsUnit P.det) : GoodRankK π A φ M D := by
  classical
  have hsum : ∀ i (G : Fin M → X), φ i (∑ l, G l) = ∑ l, φ i (G l) := fun i G =>
    map_sum (AddMonoidHom.mk' (φ i) (hadd i)) G Finset.univ
  let v : (Fin M → O) →ₗ[O] X :=
    { toFun := fun x => ∑ l, (zc' l * x l) • Y l
      map_add' := by
        intro x y
        simp only [Pi.add_apply, mul_add, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, smul_smul]
        congr 1
        ring }
  have hv : ∀ x, v x ∈ A := fun x => by
    show (∑ l, (zc' l * x l) • Y l) ∈ A
    exact A.sum_mem fun l _ => A.smul_mem _ (hY l)
  have key : ∀ x i, φ i (v x) = algebraMap O Kf (π ^ D * (P.mulVec x) i) := by
    intro x i
    show φ i (∑ l, (zc' l * x l) • Y l) = _
    rw [hsum]
    simp only [hsmul, hφ]
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← map_mul]
    congr 1
    rw [← hz l]
    ring
  refine ⟨LinearMap.codRestrict A v hv, P⁻¹, fun x j => ?_⟩
  have hx : x j = ∑ i, P⁻¹ j i * (P.mulVec x) i := by
    have h2 : P⁻¹.mulVec (P.mulVec x) = x := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hP, Matrix.one_mulVec]
    conv_lhs => rw [← h2]
    simp only [Matrix.mulVec, dotProduct]
  rw [hx, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.codRestrict_apply, key x i, ← map_mul]
  congr 1
  ring

end Formalism.MainNotions.flipOneThree.Pf

end
