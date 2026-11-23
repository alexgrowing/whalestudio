import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.TCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusDensity.RootChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.AuChi
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem norm_algebraMap_padicInt_padicAlgCl {l : ℕ} [Fact l.Prime] (a : ℤ_[l]) :
    ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ = ‖a‖ := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), PadicAlgCl.norm_extends]
  rfl

private theorem norm_le_one_of_isIntegral_padicInt' {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 := by
  obtain ⟨p, hm, hp⟩ := hx
  by_contra h
  push_neg at h
  have hd0 : p.natDegree ≠ 0 := by
    intro h0
    have h1 := Polynomial.eq_one_of_monic_natDegree_zero hm h0
    subst h1
    simp at hp
  obtain ⟨m, hmdeg⟩ : ∃ m, p.natDegree = m + 1 := ⟨p.natDegree - 1, by omega⟩
  have hc : p.coeff (m + 1) = 1 := by
    rw [← hmdeg]
    exact Polynomial.Monic.coeff_natDegree hm
  rw [Polynomial.eval₂_eq_sum_range, hmdeg, Finset.sum_range_succ, hc, map_one, one_mul] at hp
  have hsum : ‖∑ i ∈ Finset.range (m + 1), (algebraMap ℤ_[l] (PadicAlgCl l)) (p.coeff i) * x ^ i‖
      ≤ ‖x‖ ^ m := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    rw [norm_mul, norm_pow]
    have h1 : ‖(algebraMap ℤ_[l] (PadicAlgCl l)) (p.coeff i)‖ ≤ 1 := by
      rw [norm_algebraMap_padicInt_padicAlgCl]
      exact PadicInt.norm_le_one _
    have h2 : ‖x‖ ^ i ≤ ‖x‖ ^ m :=
      pow_le_pow_right₀ h.le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
    calc _ ≤ 1 * ‖x‖ ^ m := mul_le_mul h1 h2 (by positivity) zero_le_one
      _ = _ := one_mul _
  have heq : x ^ (m + 1) =
      -∑ i ∈ Finset.range (m + 1), (algebraMap ℤ_[l] (PadicAlgCl l)) (p.coeff i) * x ^ i := by
    linear_combination hp
  have hn := congrArg norm heq
  rw [norm_neg, norm_pow] at hn
  have h3 : ‖x‖ ^ (m + 1) ≤ ‖x‖ ^ m := hn ▸ hsum
  have h4 : ‖x‖ ^ m < ‖x‖ ^ (m + 1) := pow_lt_pow_right₀ h (Nat.lt_succ_self m)
  linarith

private theorem norm_coe_padicAlgCl_coefO_le_one {l : ℕ} [Fact l.Prime] (c : Coef l) (x : c.O) :
    ‖(x : PadicAlgCl l)‖ ≤ 1 := by
  haveI := c.fin
  haveI : Algebra.IsIntegral ℤ_[l] c.O := Algebra.IsIntegral.of_finite ℤ_[l] c.O
  exact norm_le_one_of_isIntegral_padicInt' _ ((Algebra.IsIntegral.isIntegral x).map c.O.val)

private theorem norm_natCast_prime_padicAlgCl_eq_inv {l : ℕ} [Fact l.Prime] : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℤ_[l] (PadicAlgCl l)) l, norm_algebraMap_padicInt_padicAlgCl, PadicInt.norm_p]

private theorem norm_coe_lt_one_of_mem_maximalIdeal_coefO {l : ℕ} [Fact l.Prime] (c : Coef l) (x : c.O)
    (hx : x ∈ IsLocalRing.maximalIdeal c.O) : ‖(x : PadicAlgCl l)‖ < 1 := by
  haveI := c.dvr
  have hcast : ((l : c.O) : PadicAlgCl l) = (l : PadicAlgCl l) := by simp
  have hl : ‖((l : c.O) : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by rw [hcast, norm_natCast_prime_padicAlgCl_eq_inv]
  have hlt : (l : ℝ)⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hl0 : (l : c.O) ≠ 0 := by
    intro h0
    have hne : (l : ℝ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero)
    rw [h0, ZeroMemClass.coe_zero, norm_zero] at hl
    exact hne hl.symm
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  have hL : Ideal.span {(l : c.O)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hl0
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hL hϖ
  have hdvd : ϖ ∣ x := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer] at hϖ
    rw [hϖ, Ideal.mem_span_singleton] at hx
    exact hx
  have hxn : x ^ n ∈ Ideal.span {(l : c.O)} := by
    rw [hn, Ideal.mem_span_singleton]
    exact pow_dvd_pow_of_dvd hdvd n
  rw [Ideal.mem_span_singleton] at hxn
  obtain ⟨y, hy⟩ := hxn
  have hy' : (x : PadicAlgCl l) ^ n = ((l : c.O) : PadicAlgCl l) * (y : PadicAlgCl l) := by
    have h5 := congrArg (fun z : c.O => (z : PadicAlgCl l)) hy
    simpa using h5
  have hnorm : ‖(x : PadicAlgCl l)‖ ^ n < 1 := by
    rw [← norm_pow, hy', norm_mul, hl]
    calc (l : ℝ)⁻¹ * ‖(y : PadicAlgCl l)‖ ≤ (l : ℝ)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left (norm_coe_padicAlgCl_coefO_le_one c y) (by positivity)
      _ < 1 := by rw [mul_one]; exact hlt
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0, pow_zero] at hnorm
    exact absurd hnorm (lt_irrefl 1)
  · exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hpos.ne').mp hnorm

private theorem norm_pow_sub_one_le_of_norm_sub_one_lt_one {l : ℕ} [Fact l.Prime] (z : PadicAlgCl l) (h : ‖z - 1‖ < 1) (i : ℕ) :
    ‖z ^ i - 1‖ ≤ ‖z - 1‖ := by
  have hz1 : ‖z‖ ≤ 1 := by
    have h1 := IsUltrametricDist.norm_add_le_max (z - 1) 1
    rw [sub_add_cancel, norm_one] at h1
    exact h1.trans (max_le h.le le_rfl)
  rw [← geom_sum_mul, norm_mul, mul_comm]
  have h2 : ‖∑ j ∈ Finset.range i, z ^ j‖ ≤ 1 := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    intro j _
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hz1
  calc ‖z - 1‖ * ‖∑ j ∈ Finset.range i, z ^ j‖ ≤ ‖z - 1‖ * 1 :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = ‖z - 1‖ := mul_one _

private theorem padicAlgCl_eq_one_of_pow_eq_one_of_norm_sub_one_lt_one {l : ℕ} [Fact l.Prime] (z : PadicAlgCl l) (m : ℕ)
    (hm : ‖(m : PadicAlgCl l)‖ = 1) (hz : z ^ m = 1) (h : ‖z - 1‖ < 1) : z = 1 := by
  have hS : ∑ i ∈ Finset.range m, z ^ i =
      (m : PadicAlgCl l) + ∑ i ∈ Finset.range m, (z ^ i - 1) := by
    rw [Finset.sum_sub_distrib]
    simp
  have hsmall : ‖∑ i ∈ Finset.range m, (z ^ i - 1)‖ < 1 :=
    lt_of_le_of_lt (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _)
      (fun i _ => norm_pow_sub_one_le_of_norm_sub_one_lt_one z h i)) h
  have hSn : ‖∑ i ∈ Finset.range m, z ^ i‖ = 1 := by
    rw [hS, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hm]; exact hsmall.ne'), hm]
    exact max_eq_left hsmall.le
  have hprod : (∑ i ∈ Finset.range m, z ^ i) * (z - 1) = 0 := by
    rw [geom_sum_mul, hz, sub_self]
  rcases mul_eq_zero.mp hprod with h0 | h0
  · rw [h0, norm_zero] at hSn
    exact absurd hSn zero_ne_one
  · exact sub_eq_zero.mp h0

private theorem norm_padicInt_unit_pow_pred_sub_one_lt_one {l : ℕ} [Fact l.Prime] (u : ℤ_[l]ˣ) :
    ‖(u : ℤ_[l]) ^ (l - 1) - 1‖ < 1 := by
  have hmem : (u : ℤ_[l]) ^ (l - 1) - 1 ∈ RingHom.ker (PadicInt.toZMod (p := l)) := by
    rw [RingHom.mem_ker, map_sub, map_pow, map_one]
    have hne : PadicInt.toZMod (u : ℤ_[l]) ≠ 0 := ((u.isUnit).map PadicInt.toZMod).ne_zero
    rw [ZMod.pow_card_sub_one_eq_one hne, sub_self]
  rw [PadicInt.ker_toZMod] at hmem
  exact PadicInt.mem_nonunits.mp ((IsLocalRing.mem_maximalIdeal _).mp hmem)

private theorem norm_natCast_prime_sub_one_padicAlgCl_eq_one {l : ℕ} [Fact l.Prime] : ‖((l - 1 : ℕ) : PadicAlgCl l)‖ = 1 := by
  have hl1 : 1 ≤ l := (Fact.out : l.Prime).one_lt.le
  have hlt : (l : ℝ)⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  rw [Nat.cast_sub hl1, Nat.cast_one, sub_eq_neg_add,
    IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (by rw [norm_neg, norm_one, norm_natCast_prime_padicAlgCl_eq_inv]; exact hlt.ne'),
    norm_neg, norm_one, norm_natCast_prime_padicAlgCl_eq_inv]
  exact max_eq_left hlt.le

private theorem sq_mul_eq_of_pow_two_mul_pred_eq_of_norm_sub_lt_one {l : ℕ} [Fact l.Prime] (b w y : PadicAlgCl l) (hb : ‖b - 1‖ < 1)
    (hw : w ^ (l - 1) = 1) (hw1 : ‖w‖ ≤ 1) (hwy : ‖w - y‖ < 1) (hy1 : ‖y‖ = 1)
    (hbn : b ^ (2 * (l - 1)) = y ^ (l - 1)) : b ^ 2 * w = y := by
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hy1
    exact zero_ne_one hy1
  have hb1 : ‖b ^ 2 - 1‖ < 1 := lt_of_le_of_lt (norm_pow_sub_one_le_of_norm_sub_one_lt_one b hb 2) hb
  have hz : (b ^ 2 * w * y⁻¹) ^ (l - 1) = 1 := by
    rw [mul_pow, mul_pow, ← pow_mul, hbn, hw, mul_one, inv_pow,
      mul_inv_cancel₀ (pow_ne_zero _ hy0)]
  have hyi : ‖y⁻¹‖ = 1 := by rw [norm_inv, hy1, inv_one]
  have hz1 : ‖b ^ 2 * w * y⁻¹ - 1‖ < 1 := by
    have hyy : y * y⁻¹ = 1 := mul_inv_cancel₀ hy0
    have hsplit : b ^ 2 * w * y⁻¹ - 1 = (b ^ 2 - 1) * w * y⁻¹ + (w - y) * y⁻¹ := by
      linear_combination hyy
    rw [hsplit]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · rw [norm_mul, norm_mul, hyi, mul_one]
      calc ‖b ^ 2 - 1‖ * ‖w‖ ≤ ‖b ^ 2 - 1‖ * 1 := mul_le_mul_of_nonneg_left hw1 (norm_nonneg _)
        _ < 1 := by rw [mul_one]; exact hb1
    · rw [norm_mul, hyi, mul_one]
      exact hwy
  exact (mul_inv_eq_one₀ hy0).mp (padicAlgCl_eq_one_of_pow_eq_one_of_norm_sub_one_lt_one _ (l - 1) norm_natCast_prime_sub_one_padicAlgCl_eq_one hz hz1)

private theorem coe_cycBar_eq_algebraMap_cycZ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    (g : G ℚ Ω) :
    ((cycBar ℚ Ω l g : (PadicAlgCl l)ˣ) : PadicAlgCl l) =
      algebraMap ℤ_[l] (PadicAlgCl l) (cycZ ℚ Ω l g : ℤ_[l]) := rfl

private theorem coe_toQ_apply {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    {c : Coef l} (om : G ℚ Ω →* (↥c.O)ˣ) (g : G ℚ Ω) :
    ((toQ om g : (PadicAlgCl l)ˣ) : PadicAlgCl l) = ((om g : c.O) : PadicAlgCl l) := rfl

private theorem coe_chiO_eq_algebraMap_cycZ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    {c : Coef l} (g : G ℚ Ω) :
    ((chiO ℚ Ω l c.O g : c.O) : PadicAlgCl l) =
      algebraMap ℤ_[l] (PadicAlgCl l) (cycZ ℚ Ω l g : ℤ_[l]) := rfl

private theorem sub_chiO_mem_maximalIdeal_of_bar_eq {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    {c : Coef l} (om : G ℚ Ω →* (↥c.O)ˣ) (g : G ℚ Ω)
    (h : Raw.bar om g = Raw.bar (chiO ℚ Ω l c.O) g) :
    (om g : c.O) - (chiO ℚ Ω l c.O g : c.O) ∈ IsLocalRing.maximalIdeal c.O :=
  (Ideal.Quotient.eq (I := IsLocalRing.maximalIdeal c.O)).mp h

theorem UpperTheory.V.Ws.Lk.halfEx :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}, D.Good → ∃ γ : G ℚ Ω →* (PadicAlgCl l)ˣ, Continuous γ ∧ (∀ g, ‖(γ g : PadicAlgCl l) - 1‖ < 1) ∧ (∀ g, γ g ^ 2 * toQ D.om g = cycBar ℚ Ω l g) ∧ (cycZ ℚ Ω l).ker ≤ γ.ker := by
  intro Ω _ _ _ l _ c D hD
  have hl2 : l ≠ 2 := hD.l_odd
  have hlp : l.Prime := Fact.out
  obtain ⟨π, hπapp⟩ : ∃ π : G ℚ Ω →* ℤ_[l]ˣ, ∀ g, π g = (cycZ ℚ Ω l g) ^ (l - 1) :=
    ⟨(cycZ ℚ Ω l) ^ (l - 1), fun g => rfl⟩
  have hπc : Continuous π := by
    have hfun : (⇑π) = fun g => (cycZ ℚ Ω l g) ^ (l - 1) := funext hπapp
    rw [hfun]
    exact (continuous_cycZ ℚ Ω l).pow _
  have hπn : ∀ s, ‖((π s : ℤ_[l]ˣ) : ℤ_[l]) - 1‖ < 1 := by
    intro s
    rw [hπapp, Units.val_pow_eq_pow_val]
    exact norm_padicInt_unit_pow_pred_sub_one_lt_one _
  have hn : 0 < 2 * (l - 1) := by
    have := hlp.two_le
    omega
  obtain ⟨t, β, c₁, htc, htk, htβ, hβc, hβ1, hβn, -⟩ :=
    Tw.rootChar l hl2 (G ℚ Ω) π hπc hπn (2 * (l - 1)) hn
  refine ⟨β, hβc, fun g => (hβ1 g).2, ?_, ?_⟩
  · intro g
    apply Units.ext
    rw [Units.val_mul, Units.val_pow_eq_pow_val, coe_cycBar_eq_algebraMap_cycZ, coe_toQ_apply]
    apply sq_mul_eq_of_pow_two_mul_pred_eq_of_norm_sub_lt_one (l := l) _ _ _ (hβ1 g).2
    · have h := congrArg (fun f : G ℚ Ω →* (↥c.O)ˣ => ((f g : c.O) : PadicAlgCl l)) hD.om_pow
      simpa using h
    · exact norm_coe_padicAlgCl_coefO_le_one c _
    · have h := norm_coe_lt_one_of_mem_maximalIdeal_coefO c _ (sub_chiO_mem_maximalIdeal_of_bar_eq D.om g (hD.om_bar g))
      rw [AddSubgroupClass.coe_sub, coe_chiO_eq_algebraMap_cycZ] at h
      exact h
    · rw [norm_algebraMap_padicInt_padicAlgCl]
      exact PadicInt.isUnit_iff.mp (Units.isUnit _)
    · rw [hβn g, hπapp, Units.val_pow_eq_pow_val, map_pow]
  · intro g hg
    apply htβ
    rw [htk, MonoidHom.mem_ker, hπapp, (MonoidHom.mem_ker).mp hg, one_pow]
