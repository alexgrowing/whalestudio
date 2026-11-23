import Mathlib

open IsLocalRing

set_option maxHeartbeats 400000 in
theorem UpperTheory.V.AlgebraTools.powerSeries_equiv_of_complete_dvr :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A]
      (p : ℕ) [Fact p.Prime] [CharP A p] [Finite (ResidueField A)] (t : A), Irreducible t →
      ∃ e : PowerSeries (ResidueField A) ≃+* A, e PowerSeries.X = t ∧
        ∀ c, residue A (e (PowerSeries.C c)) = c := by
  intro A _ _ _ _ p _ _ _ t ht
  classical
  haveI : Fintype (ResidueField A) := Fintype.ofFinite _
  have hH : ∀ x y : A, (∀ n : ℕ, x - y ∈ maximalIdeal A ^ n) → x = y := by
    intro x y h
    rw [IsHausdorff.eq_iff_smodEq (I := maximalIdeal A)]
    intro n
    rw [SModEq.sub_mem]
    simpa [Ideal.smul_eq_mul] using h n
  have hm : maximalIdeal A = Ideal.span {t} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer t).mp ht
  have htm : t ∈ maximalIdeal A := by
    rw [hm]
    exact Ideal.subset_span rfl
  have hpk : CharP (ResidueField A) p := by
    rw [CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)]
    rw [← map_natCast (residue A), CharP.cast_eq_zero, map_zero]
  have hder : ∀ (n : ℕ) (a : A), (n : A) = 0 →
      Polynomial.eval a (Polynomial.derivative (Polynomial.X ^ n - Polynomial.X : Polynomial A))
        = -1 := by
    intro n a hn
    rw [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_X]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_natCast, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one, hn,
      zero_mul, zero_sub]
  obtain ⟨nf, -, hq⟩ := FiniteField.card (ResidueField A) p
  set q := Fintype.card (ResidueField A) with hqdef
  have hq2 : 1 < q := Fintype.one_lt_card
  have hq0 : (q : A) = 0 := by
    rw [hq]
    push_cast
    simp [CharP.cast_eq_zero]
  have hU : ∀ x y : A, x ^ q = x → y ^ q = y → residue A x = residue A y → x = y := by
    intro x y hx hy hxy
    have hz : (x - y) ^ q = x - y := by
      rw [hq, sub_pow_char_pow, ← hq, hx, hy]
    have hzm : x - y ∈ maximalIdeal A := Ideal.Quotient.eq.mp hxy
    rw [← sub_eq_zero]
    have h1 : (x - y) * (1 - (x - y) ^ (q - 1)) = 0 := by
      rw [mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel hq2.le, hz, sub_self]
    have hu : IsUnit (1 - (x - y) ^ (q - 1)) := by
      apply IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
      exact (mem_maximalIdeal _).mp (Ideal.pow_mem_of_mem _ hzm _ (by omega))
    exact (mul_eq_zero.mp h1).resolve_right hu.ne_zero
  have hE : ∀ c : ResidueField A, ∃ x : A, x ^ q = x ∧ residue A x = c := by
    intro c
    obtain ⟨a₀, ha₀⟩ := IsLocalRing.residue_surjective c
    have hmon : (Polynomial.X ^ q - Polynomial.X : Polynomial A).Monic := by
      apply Polynomial.monic_X_pow_sub
      rw [Polynomial.degree_X]
      exact_mod_cast hq2
    have he1 : Polynomial.eval a₀ (Polynomial.X ^ q - Polynomial.X : Polynomial A)
        ∈ maximalIdeal A := by
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, ha₀, FiniteField.pow_card,
        sub_self]
    have he2 : IsUnit (Ideal.Quotient.mk (maximalIdeal A) (Polynomial.eval a₀
        (Polynomial.derivative (Polynomial.X ^ q - Polynomial.X : Polynomial A)))) := by
      rw [hder q a₀ hq0, map_neg, map_one]
      exact isUnit_one.neg
    obtain ⟨a, ha, ham⟩ := HenselianRing.is_henselian (I := maximalIdeal A)
      (Polynomial.X ^ q - Polynomial.X : Polynomial A) hmon a₀ he1 he2
    refine ⟨a, ?_, ?_⟩
    · have h' := ha
      simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X] at h'
      exact sub_eq_zero.mp h'
    · rw [← ha₀]
      exact Ideal.Quotient.eq.mpr ham
  choose s0 hs0 using hE
  have hsq : ∀ c, s0 c ^ q = s0 c := fun c => (hs0 c).1
  have hsr : ∀ c, residue A (s0 c) = c := fun c => (hs0 c).2
  have hq0' : q ≠ 0 := by omega
  let s : ResidueField A →+* A :=
    { toFun := s0
      map_one' := hU _ _ (hsq 1) (one_pow _) (by rw [hsr, map_one])
      map_mul' := fun a b => hU _ _ (hsq _) (by rw [mul_pow, hsq, hsq])
        (by rw [hsr, map_mul, hsr, hsr])
      map_zero' := hU _ _ (hsq 0) (zero_pow hq0') (by rw [hsr, map_zero])
      map_add' := fun a b => hU _ _ (hsq _) (by rw [hq, add_pow_char_pow, ← hq, hsq, hsq])
        (by rw [hsr, map_add, hsr, hsr]) }
  have hsr' : ∀ c, residue A (s c) = c := hsr
  have hev : ∀ n (f : PowerSeries (ResidueField A)),
      (PowerSeries.trunc n f).eval₂ s t =
        ∑ i ∈ Finset.range n, s (PowerSeries.coeff i f) * t ^ i := fun n f =>
    PowerSeries.eval₂_trunc_eq_sum_range t s n f
  have key : ∀ n (P Q : Polynomial (ResidueField A)), (∀ i < n, P.coeff i = Q.coeff i) →
      Ideal.Quotient.mk (maximalIdeal A ^ n) (P.eval₂ s t) =
        Ideal.Quotient.mk (maximalIdeal A ^ n) (Q.eval₂ s t) := by
    intro n P Q h
    rw [Ideal.Quotient.eq, ← Polynomial.eval₂_sub]
    obtain ⟨R, hR⟩ := (Polynomial.X_pow_dvd_iff (f := P - Q) (n := n)).mpr
      (fun d hd => by rw [Polynomial.coeff_sub, h d hd, sub_self])
    rw [hR, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow htm n)
  let g : (n : ℕ) → PowerSeries (ResidueField A) →+* A ⧸ maximalIdeal A ^ n := fun n =>
    { toFun := fun f => Ideal.Quotient.mk (maximalIdeal A ^ n) ((PowerSeries.trunc n f).eval₂ s t)
      map_one' := by
        rw [key n _ 1 (fun i hi => ?_), Polynomial.eval₂_one, map_one]
        simp [PowerSeries.coeff_trunc, hi, PowerSeries.coeff_one, Polynomial.coeff_one]
      map_mul' := fun f g' => by
        rw [← map_mul, ← Polynomial.eval₂_mul]
        apply key
        intro i hi
        rw [← PowerSeries.trunc_trunc_mul_trunc, PowerSeries.coeff_trunc, if_pos hi,
          ← Polynomial.coe_mul, Polynomial.coeff_coe]
      map_zero' := by simp [hev]
      map_add' := fun f g' => by simp [hev, add_mul, Finset.sum_add_distrib] }
  have hg : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow (maximalIdeal A) hle).comp (g n) = g m := by
    intro m n hle
    ext f
    show Ideal.Quotient.factorPow (maximalIdeal A) hle
        (Ideal.Quotient.mk _ ((PowerSeries.trunc n f).eval₂ s t)) =
      Ideal.Quotient.mk _ ((PowerSeries.trunc m f).eval₂ s t)
    rw [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
    apply key
    intro i hi
    simp [PowerSeries.coeff_trunc, hi, lt_of_lt_of_le hi hle]
  let e0 := IsAdicComplete.liftRingHom (maximalIdeal A) g hg
  have hme : ∀ n f, Ideal.Quotient.mk (maximalIdeal A ^ n) (e0 f) = g n f :=
    fun n f => IsAdicComplete.mk_liftRingHom (maximalIdeal A) g hg n f
  have hEq : ∀ n f, e0 f - (PowerSeries.trunc n f).eval₂ s t ∈ maximalIdeal A ^ n :=
    fun n f => Ideal.Quotient.eq.mp (hme n f)
  have hres : ∀ f, residue A (e0 f) = PowerSeries.constantCoeff f := by
    intro f
    have h1 := hEq 1 f
    rw [pow_one, hev, Finset.sum_range_one, pow_zero, mul_one] at h1
    have h2 : residue A (e0 f) = residue A (s (PowerSeries.coeff 0 f)) :=
      Ideal.Quotient.eq.mpr h1
    rw [h2, hsr', PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hmono : ∀ x : A, (∀ n, x ∈ maximalIdeal A ^ (n + 2)) → ∀ n, x ∈ maximalIdeal A ^ n :=
    fun x h n => Ideal.pow_le_pow_right (by omega) (h n)
  have hX : e0 PowerSeries.X = t := by
    apply hH
    apply hmono
    intro n
    have h1 := hEq (n + 2) PowerSeries.X
    have h2 : (PowerSeries.trunc (n + 2) PowerSeries.X).eval₂ s t = t := by
      rw [hev, Finset.sum_range_succ', Finset.sum_range_succ']
      simp [PowerSeries.coeff_X]
    rwa [h2] at h1
  have hinj : Function.Injective e0 := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    by_contra hne
    have hdec := PowerSeries.X_pow_order_mul_divXPowOrder (f := f)
    have hu : residue A (e0 (PowerSeries.divXPowOrder f)) ≠ 0 := by
      rw [hres]
      exact (PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff).not.mpr hne
    have hu' : e0 (PowerSeries.divXPowOrder f) ≠ 0 := fun h => hu (by rw [h, map_zero])
    rw [← hdec, map_mul, map_pow, hX] at hf
    exact mul_ne_zero (pow_ne_zero _ ht.ne_zero) hu' hf
  have hδ : ∀ x : A, ∃ y, y * t = x - s (residue A x) := by
    intro x
    rw [← Ideal.mem_span_singleton', ← hm, ← IsLocalRing.residue_eq_zero_iff, map_sub, hsr',
      sub_self]
  choose δ hδ using hδ
  have hsurj : Function.Surjective e0 := by
    intro x
    let F : PowerSeries (ResidueField A) := PowerSeries.mk fun n => residue A (δ^[n] x)
    have hc : ∀ n, x = (PowerSeries.trunc n F).eval₂ s t + t ^ n * δ^[n] x := by
      intro n
      induction n with
      | zero => simp [hev]
      | succ n ih =>
        rw [hev, Finset.sum_range_succ, ← hev, Function.iterate_succ_apply']
        have hcn : PowerSeries.coeff n F = residue A (δ^[n] x) := PowerSeries.coeff_mk _ _
        rw [hcn]
        linear_combination ih - t ^ n * hδ (δ^[n] x)
    refine ⟨F, hH _ _ fun n => ?_⟩
    have h1 := hEq n F
    have h2 : e0 F - x = (e0 F - (PowerSeries.trunc n F).eval₂ s t) - t ^ n * δ^[n] x := by
      linear_combination -(hc n)
    rw [h2]
    exact Ideal.sub_mem _ h1 (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow htm n))
  refine ⟨RingEquiv.ofBijective e0 ⟨hinj, hsurj⟩, hX, fun c => ?_⟩
  show residue A (e0 (PowerSeries.C c)) = c
  rw [hres, PowerSeries.constantCoeff_C]
