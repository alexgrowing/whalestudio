import Mathlib

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.Ring

open Polynomial

variable {K : Type} [Field K]

theorem eq_X_mul_unit (s : PowerSeries K) (h0 : PowerSeries.constantCoeff s = 0)
    (h1 : PowerSeries.coeff 1 s ≠ 0) : ∃ u : PowerSeries K, IsUnit u ∧ s = PowerSeries.X * u := by
  obtain ⟨u, hu⟩ := PowerSeries.X_dvd_iff.mpr h0
  refine ⟨u, ?_, hu⟩
  have hc : PowerSeries.coeff 1 s = PowerSeries.constantCoeff u := by
    rw [hu]
    first
    | simp [PowerSeries.coeff_succ_X_mul]
    | exact PowerSeries.coeff_succ_X_mul 0 u
  rw [PowerSeries.isUnit_iff_constantCoeff]
  rw [hc] at h1
  exact isUnit_iff_ne_zero.mpr h1

private theorem algebraMap_powerSeries_self_eq_C {R : Type} [CommRing R] (a : R) :
    algebraMap R (PowerSeries R) a = PowerSeries.C a := by
  first
  | rfl
  | (rw [Algebra.algebraMap_eq_smul_one, PowerSeries.smul_eq_C_mul, mul_one])
  | simp [PowerSeries.algebraMap_apply']

private theorem constantCoeff_aeval_eq_eval_constantCoeff (y : PowerSeries K) (r : K[X]) :
    PowerSeries.constantCoeff (Polynomial.aeval y r) = r.eval (PowerSeries.constantCoeff y) := by
  refine Polynomial.induction_on' r (fun p q hp hq => ?_) (fun n a => ?_)
  · rw [map_add, map_add, hp, hq, Polynomial.eval_add]
  · rw [Polynomial.aeval_monomial, map_mul, map_pow, algebraMap_powerSeries_self_eq_C, PowerSeries.constantCoeff_C,
      Polynomial.eval_monomial]

theorem pow_dvd_of_order (r : K[X]) (c : K) (s : PowerSeries K)
    (h0 : PowerSeries.constantCoeff s = 0) (h1 : PowerSeries.coeff 1 s ≠ 0) (b : ℕ)
    (hb : (PowerSeries.X : PowerSeries K) ^ b ∣ Polynomial.aeval (PowerSeries.C c + s) r) :
    (Polynomial.X - Polynomial.C c) ^ b ∣ r := by
  obtain ⟨u, hu, hsu⟩ := eq_X_mul_unit s h0 h1
  have hsub : Polynomial.aeval (PowerSeries.C c + s) (Polynomial.X - Polynomial.C c) = s := by
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, algebraMap_powerSeries_self_eq_C, add_sub_cancel_left]
  induction b generalizing r with
  | zero => simp
  | succ b ih =>
    have hX : (PowerSeries.X : PowerSeries K) ∣ Polynomial.aeval (PowerSeries.C c + s) r :=
      (dvd_pow_self _ (Nat.succ_ne_zero b)).trans hb
    have hroot : r.IsRoot c := by
      rw [PowerSeries.X_dvd_iff, constantCoeff_aeval_eq_eval_constantCoeff, map_add, PowerSeries.constantCoeff_C, h0,
        add_zero] at hX
      exact hX
    obtain ⟨q, rfl⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
    rw [map_mul, hsub] at hb
    have hb' : (PowerSeries.X : PowerSeries K) * PowerSeries.X ^ b ∣
        PowerSeries.X * (u * Polynomial.aeval (PowerSeries.C c + s) q) := by
      rw [← mul_assoc, ← hsu, ← pow_succ']
      exact hb
    have hq : (PowerSeries.X : PowerSeries K) ^ b ∣ Polynomial.aeval (PowerSeries.C c + s) q :=
      hu.dvd_mul_left.mp ((mul_dvd_mul_iff_left PowerSeries.X_ne_zero).mp hb')
    rw [pow_succ']
    exact mul_dvd_mul_left _ (ih q hq)

theorem eq_zero_of_pow_dvd (r : K[X]) (cs : Finset K) (b : ℕ)
    (h : ∀ c ∈ cs, (Polynomial.X - Polynomial.C c) ^ b ∣ r) (hdeg : r.natDegree < cs.card * b) : r = 0 := by
  by_contra hr
  have hprod : (∏ c ∈ cs, (Polynomial.X - Polynomial.C c) ^ b) ∣ r := by
    refine Finset.prod_dvd_of_coprime ?_ h
    intro x _ y _ hxy
    exact (Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hxy).isUnit).pow
  have hdeg' : (∏ c ∈ cs, (Polynomial.X - Polynomial.C c) ^ b).natDegree = cs.card * b := by
    rw [Polynomial.natDegree_prod _ _ (fun c _ => pow_ne_zero _ (Polynomial.X_sub_C_ne_zero c))]
    simp [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_comm]
  have := Polynomial.natDegree_le_of_dvd hprod hr
  omega

theorem algHom_coe {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    (φ : PowerSeries O →ₐ[O] A) (r : O[X]) :
    φ (r : PowerSeries O) = Polynomial.aeval (φ PowerSeries.X) r := by
  refine Polynomial.induction_on r (fun a => ?_) (fun p q hp hq => ?_) (fun n a _ => ?_)
  · rw [Polynomial.coe_C, Polynomial.aeval_C, ← algebraMap_powerSeries_self_eq_C, φ.commutes]
  · rw [Polynomial.coe_add, map_add, map_add, hp, hq]
  · rw [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_C, Polynomial.coe_X, map_mul, map_pow,
      ← algebraMap_powerSeries_self_eq_C, φ.commutes, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]

private theorem aeval_map_algebraMap_eq_aeval {O : Type} [CommRing O] [Algebra O K] (y : PowerSeries K)
    (r : O[X]) : Polynomial.aeval y (r.map (algebraMap O K)) = Polynomial.aeval y r := by
  first
  | exact Polynomial.aeval_map_algebraMap K y r
  | (refine Polynomial.induction_on r (fun a => ?_) (fun p q hp hq => ?_) (fun n a _ => ?_)
     · simp [algebraMap_powerSeries_self_eq_C, PowerSeries.algebraMap_apply']
     · simp only [Polynomial.map_add, map_add, hp, hq]
     · simp [algebraMap_powerSeries_self_eq_C, PowerSeries.algebraMap_apply'])

theorem dvd_of_vanish {O : Type} [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Algebra O K]
    (hinj : Function.Injective (algebraMap O K)) f (N : ℕ)
    (hres : PowerSeries.map (IsLocalRing.residue O) f = PowerSeries.X ^ N)
    (Z : Finset K) (hZ : Z.card = N) (φ : K → (PowerSeries O →ₐ[O] PowerSeries K))
    (s : K → PowerSeries K) (hφX : ∀ c ∈ Z, φ c PowerSeries.X = PowerSeries.C c + s c)
    (hs0 : ∀ c ∈ Z, PowerSeries.constantCoeff (s c) = 0)
    (hs1 : ∀ c ∈ Z, PowerSeries.coeff 1 (s c) ≠ 0)
    (hf : ∀ c ∈ Z, PowerSeries.X ∣ φ c f) (b : ℕ) (g : PowerSeries O)
    (hg : ∀ c ∈ Z, PowerSeries.X ^ b ∣ φ c g) :
    ∃ h : PowerSeries O, g = f ^ b * h := by
  have hmap : PowerSeries.map (IsLocalRing.residue O) (f ^ b) = PowerSeries.X ^ (N * b) := by
    rw [map_pow, hres, ← pow_mul]
  have hne : PowerSeries.map (IsLocalRing.residue O) (f ^ b) ≠ 0 := by
    rw [hmap]; exact pow_ne_zero _ PowerSeries.X_ne_zero
  obtain ⟨q, r, hqr⟩ := PowerSeries.exists_isWeierstrassDivision g hne
  have hord : (PowerSeries.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)) (f ^ b)).order.toNat
      = N * b := by
    have hm : PowerSeries.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)) (f ^ b)
        = PowerSeries.X ^ (N * b) := hmap
    rw [hm, PowerSeries.order_X_pow]
    rfl
  have hdeg : r.degree < (N * b : ℕ) := by
    have := hqr.degree_lt
    rwa [hord] at this
  have hg_eq : g = f ^ b * q + (r : PowerSeries O) := hqr.eq_mul_add
  have hr : r = 0 := by
    by_contra hr0
    have hnat : r.natDegree < N * b := (Polynomial.natDegree_lt_iff_degree_lt hr0).mpr hdeg
    have hdvd : ∀ c ∈ Z, (Polynomial.X - Polynomial.C c) ^ b ∣ r.map (algebraMap O K) := by
      intro c hc
      apply pow_dvd_of_order _ c (s c) (hs0 c hc) (hs1 c hc) b
      have h1 : φ c g = (φ c f) ^ b * φ c q + Polynomial.aeval (PowerSeries.C c + s c) r := by
        rw [hg_eq, map_add, map_mul, map_pow, algHom_coe, hφX c hc]
      have h2 : (PowerSeries.X : PowerSeries K) ^ b ∣ (φ c f) ^ b * φ c q :=
        dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (hf c hc) b) _
      have h4 := hg c hc
      rw [h1] at h4
      rw [aeval_map_algebraMap_eq_aeval]
      exact (dvd_add_right h2).mp h4
    have hK : r.map (algebraMap O K) = 0 := by
      refine eq_zero_of_pow_dvd _ Z b hdvd ?_
      rw [hZ]
      exact lt_of_le_of_lt Polynomial.natDegree_map_le hnat
    exact hr0 (Polynomial.map_injective _ hinj (by rw [hK, Polynomial.map_zero]))
  exact ⟨q, by rw [hg_eq, hr, Polynomial.coe_zero, add_zero]⟩

end Formalism.MainNotions.RamifiedCoefficientChains.S9.Ring
