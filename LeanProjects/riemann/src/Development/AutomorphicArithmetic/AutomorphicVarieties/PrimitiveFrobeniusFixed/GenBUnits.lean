import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.SamePrimesMulPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.StickelbergerBernoulliCoeffExpansionModDenominat
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.ExistsBinomialExpansionModSq
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Sumicc

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem th_eq (F b : ℕ) [NeZero F] (t : ZMod F) (ht : t ≠ 0) (hy : (b : ZMod F) * t ≠ 0) :
    (b : ℤ) * (t.val : ℤ) = (((b : ZMod F) * t).val : ℤ) + F * ((t.val * b / F : ℕ) : ℤ) ∧
    th F b t = 2 * ((t.val * b / F : ℕ) : ℤ) - ((b : ℤ) - 1) := by
  have hF : 0 < F := Nat.pos_of_ne_zero (NeZero.ne F)
  have h1 : ((b : ZMod F) * t).val = t.val * b % F := by
    rw [ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod, mul_comm]
  have h0 : 0 < ((b : ZMod F) * t).val := Nat.pos_of_ne_zero fun h => hy ((ZMod.val_eq_zero _).1 h)
  have hlt := ZMod.val_lt ((b : ZMod F) * t)
  have h2 : F * (t.val * b / F) + t.val * b % F = t.val * b := Nat.div_add_mod _ _
  have h3 : F * ((-t).val * b / F) + (-t).val * b % F = (-t).val * b := Nat.div_add_mod _ _
  have h4 : (-t).val * b % F < F := Nat.mod_lt _ hF
  have h5 : (-t).val + t.val = F := by
    rw [ZMod.neg_val, if_neg ht]
    have := ZMod.val_lt t
    omega
  rw [← h1] at h2
  rw [th]
  generalize ((b : ZMod F) * t).val = y at *
  generalize (-t).val * b % F = r at *
  generalize (-t).val * b / F = j' at *
  generalize t.val * b / F = j at *
  generalize (-t).val = s at *
  generalize t.val = u at *
  zify at h0 hlt h2 h3 h4 h5 hF
  have hr : (0 : ℤ) ≤ r := by positivity
  have h6 : (F : ℤ) * (b - j - j') = y + r := by linear_combination -h2 - h3 - b * h5
  have h7 : (0 : ℤ) < b - j - j' := by
    by_contra h
    nlinarith
  have h8 : (b : ℤ) - j - j' < 2 := by
    by_contra h
    nlinarith
  exact ⟨by linear_combination -h2, by omega⟩

private theorem pointwise (F e b : ℕ) [NeZero F] (t : ZMod F) (ht : t ≠ 0) (hy : (b : ZMod F) * t ≠ 0) :
    ∃ z : ℤ, (Stk.dk (e + 1) : ℚ) * ((b : ℚ) ^ e * (th F b t * (t.val : ℚ) ^ e) +
      2 * (Bern.bcoef F (e + 1) ((b : ZMod F) * t).val / (e + 1) -
        (b : ℚ) ^ (e + 1) * (Bern.bcoef F (e + 1) t.val / (e + 1)))) = F * z := by
  have hM0 : 0 < F := Nat.pos_of_ne_zero (NeZero.ne F)
  have hM : (F : ℚ) ≠ 0 := by exact_mod_cast hM0.ne'
  have hD : (primorial (e + 1 + 1) : ℚ) ≠ 0 := by exact_mod_cast (primorial_pos _).ne'
  have hk : (e : ℚ) + 1 ≠ 0 := by positivity
  obtain ⟨h1, h2⟩ := th_eq F b t ht hy
  obtain ⟨z1, hz1⟩ := Stk.stickelbergerBernoulliCoeff_expansion_mod_denominator F e ((b : ZMod F) * t).val hM0
  obtain ⟨z2, hz2⟩ := Stk.stickelbergerBernoulliCoeff_expansion_mod_denominator F e t.val hM0
  rw [h2]
  generalize ((b : ZMod F) * t).val = y at *
  generalize t.val * b / F = j at *
  generalize t.val = u at *
  obtain ⟨⟨z3, hz3⟩, ⟨w, hw⟩⟩ := Stk.exists_binomial_expansion_mod_sq ((b : ℤ) * u) (-(j : ℤ)) F e
  have h3 : (b : ℤ) * u + F * (-(j : ℤ)) = y := by linear_combination h1
  rw [h3] at hz3 hw
  have q3 : (y : ℚ) ^ (e + 1) =
      ((b : ℚ) * u) ^ (e + 1) + ((e : ℚ) + 1) * ((b : ℚ) * u) ^ e * ((F : ℚ) * (-(j : ℚ))) + (F : ℚ) ^ 2 * z3 := by
    exact_mod_cast hz3
  have qw : (y : ℚ) ^ e = ((b : ℚ) * u) ^ e + (F : ℚ) * w := by
    exact_mod_cast hw
  have hdk : (Stk.dk (e + 1) : ℚ) = 2 * ((e : ℚ) + 1) * (primorial (e + 1 + 1) : ℚ) := by
    rw [Stk.dk]; push_cast; ring
  refine ⟨4 * z1 - 4 * (b : ℤ) ^ (e + 1) * z2 + 4 * (primorial (e + 1 + 1) : ℤ) * z3
    - 2 * ((e : ℤ) + 1) * (primorial (e + 1 + 1) : ℤ) * w, ?_⟩
  rw [Nat.cast_add, Nat.cast_one] at hz1 hz2
  rw [hz1, hz2, q3, qw, hdk]
  push_cast
  field_simp
  ring

private theorem genB_units {R : Type} [CommRing R] [Algebra ℚ R] {F : ℕ} [NeZero F] (hF : 1 < F) (k : ℕ)
    (χ : DirichletCharacter R F) :
    Bern.genB k (χ : ZMod F → R) = ∑ t : (ZMod F)ˣ, χ t * algebraMap ℚ R (Bern.bcoef F k (t : ZMod F).val) := by
  haveI : Fact (1 < F) := ⟨hF⟩
  have h1 : Bern.genB k (χ : ZMod F → R) = ∑ t : ZMod F, χ t * algebraMap ℚ R (Bern.bcoef F k t.val) := by
    rw [← Bern.b_sumicc (fun x : ZMod F => χ x * algebraMap ℚ R (Bern.bcoef F k x.val)), Bern.genB]
    refine Finset.sum_congr rfl fun a ha => ?_
    rcases (Finset.mem_Icc.1 ha).2.lt_or_eq with h | h
    · rw [ZMod.val_cast_of_lt h]
    · rw [h, ZMod.natCast_self, χ.map_nonunit not_isUnit_zero, zero_mul, zero_mul]
  rw [h1]
  symm
  refine Finset.sum_of_injOn (fun t : (ZMod F)ˣ => (t : ZMod F)) (fun a _ b _ h => Units.ext h)
    (fun _ _ => Finset.mem_univ _) ?_ (fun _ _ => rfl)
  intro x _ hx
  rw [χ.map_nonunit, zero_mul]
  rintro ⟨u, rfl⟩
  exact hx ⟨u, by simp, rfl⟩

private theorem norm_chi {R : Type} [NormedField R] {F : ℕ} [NeZero F] (χ : DirichletCharacter R F) (t : (ZMod F)ˣ) :
    ‖χ t‖ = 1 := by
  have h : χ t ^ Fintype.card (ZMod F)ˣ = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
  have h2 : ‖χ t‖ ^ Fintype.card (ZMod F)ˣ = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) Fintype.card_ne_zero).1 h2

theorem UpperTheory.V.ML.zCong :
    ∀ (l : ℕ) [Fact l.Prime] (F m e b : ℕ) [NeZero F], l ^ m ∣ F → 1 ≤ m → 1 ≤ e → b.Coprime F → ∀ χ : DirichletCharacter (PadicAlgCl l) F, χ (-1) = (-1) ^ (e + 1) →
    ‖(UpperTheory.V.Stk.dk (e + 1) : PadicAlgCl l) * ((b : PadicAlgCl l) ^ e * χ b * ∑ t : (ZMod F)ˣ, (th F b t : PadicAlgCl l) * (((t : ZMod F).val : PadicAlgCl l) ^ e * χ t) -
      2 * (χ b * (b : PadicAlgCl l) ^ (e + 1) - 1) * (UpperTheory.V.Bern.genB (e + 1) (χ : ZMod F → PadicAlgCl l) / (e + 1)))‖ ≤ ‖(l : PadicAlgCl l) ^ m‖ := by
  intro l hl F m e b _ hm h1m _ hb χ _
  have hF : 1 < F := lt_of_lt_of_le (Nat.one_lt_pow (by omega) hl.out.one_lt)
    (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne F)) hm)
  haveI : Fact (1 < F) := ⟨hF⟩
  set u : (ZMod F)ˣ := ZMod.unitOfCoprime b hb with hu
  have hub : (u : ZMod F) = b := ZMod.coe_unitOfCoprime b hb
  have g1 := genB_units hF (e + 1) χ
  have g2 : Bern.genB (e + 1) (χ : ZMod F → PadicAlgCl l) = ∑ t : (ZMod F)ˣ, χ ((b : ZMod F) * t) *
      algebraMap ℚ (PadicAlgCl l) (Bern.bcoef F (e + 1) ((b : ZMod F) * t).val) := by
    rw [g1, ← hub]
    exact (Equiv.sum_comp (Equiv.mulLeft u) (fun t : (ZMod F)ˣ => χ t *
      algebraMap ℚ (PadicAlgCl l) (Bern.bcoef F (e + 1) (t : ZMod F).val))).symm
  have hp : ∀ t : (ZMod F)ˣ, _ := fun t => pointwise F e b (t : ZMod F) t.ne_zero (by
    rw [← hub]; exact (u * t).ne_zero)
  choose z hz using hp
  have key : (UpperTheory.V.Stk.dk (e + 1) : PadicAlgCl l) * ((b : PadicAlgCl l) ^ e * χ b * ∑ t : (ZMod F)ˣ, (th F b t : PadicAlgCl l) * (((t : ZMod F).val : PadicAlgCl l) ^ e * χ t) -
      2 * (χ b * (b : PadicAlgCl l) ^ (e + 1) - 1) * (UpperTheory.V.Bern.genB (e + 1) (χ : ZMod F → PadicAlgCl l) / (e + 1))) =
      ∑ t : (ZMod F)ˣ, χ ((b : ZMod F) * t) * ((F : PadicAlgCl l) * z t) := by
    have e1 : 2 * (χ b * (b : PadicAlgCl l) ^ (e + 1) - 1) * (UpperTheory.V.Bern.genB (e + 1) (χ : ZMod F → PadicAlgCl l) / (e + 1)) =
      2 * (χ b * (b : PadicAlgCl l) ^ (e + 1)) / (e + 1) * UpperTheory.V.Bern.genB (e + 1) (χ : ZMod F → PadicAlgCl l)
        - 2 / (e + 1) * UpperTheory.V.Bern.genB (e + 1) (χ : ZMod F → PadicAlgCl l) := by ring
    rw [e1]
    nth_rewrite 2 [g2]
    rw [g1, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    have h := congrArg (algebraMap ℚ (PadicAlgCl l)) (hz t)
    simp only [map_mul, map_sub, map_add, map_pow, map_natCast, map_intCast, map_div₀, map_one, map_ofNat] at h
    rw [← h, map_mul]
    ring
  rw [key]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun t _ => ?_
  obtain ⟨c, hc⟩ := hm
  have hn : ‖χ ((b : ZMod F) * t)‖ = 1 := by
    rw [← hub]; exact norm_chi χ (u * t)
  have hFc : (F : PadicAlgCl l) * z t = (l : PadicAlgCl l) ^ m * (((c : ℤ) * z t : ℤ) : PadicAlgCl l) := by
    have : (F : PadicAlgCl l) = (l : PadicAlgCl l) ^ m * c := by exact_mod_cast congrArg (Nat.cast : ℕ → PadicAlgCl l) hc
    rw [this]; push_cast; ring
  rw [norm_mul, hn, one_mul, hFc, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one _ _)
