import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

open Filter Asymptotics CongruenceSubgroup Matrix.SpecialLinearGroup
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm Pointwise

private theorem bounded_petersson_weight (H : ℍ → ℂ) (B a : ℝ) (ha : 0 < a) (hB : ∀ z, ‖H z‖ ≤ B)
    (hd : H =O[atImInfty] fun τ => Real.exp (-a * τ.im)) : ∃ C : ℝ, ∀ z : ℍ, ‖H z‖ * z.im ^ 3 ≤ C := by
  obtain ⟨c, hc⟩ := Asymptotics.isBigO_iff.mp hd
  obtain ⟨A, hA⟩ := (UpperHalfPlane.atImInfty_mem _).mp hc
  set M := max A 0 with hM
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB UpperHalfPlane.I)
  have hM0 : 0 ≤ M := le_max_right _ _
  refine ⟨B * M ^ 3 + |c| * (6 / a ^ 3), fun z => ?_⟩
  have ht := z.im_pos
  have h1 : 0 ≤ B * M ^ 3 := by positivity
  have h2 : 0 ≤ |c| * (6 / a ^ 3) := by positivity
  rcases le_total z.im M with h | h
  · have : ‖H z‖ * z.im ^ 3 ≤ B * M ^ 3 :=
      mul_le_mul (hB z) (pow_le_pow_left₀ ht.le h 3) (by positivity) hB0
    linarith
  · have hz := hA z ((le_max_left _ _).trans h)
    simp only [Set.mem_setOf_eq] at hz
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hz
    have hexp : (a * z.im) ^ 3 / 6 ≤ Real.exp (a * z.im) := by
      have := Real.pow_div_factorial_le_exp (a * z.im) (by positivity) 3
      simpa [Nat.factorial] using this
    have he := Real.exp_pos (a * z.im)
    have hkey : Real.exp (-a * z.im) * z.im ^ 3 ≤ 6 / a ^ 3 := by
      rw [le_div_iff₀ (by positivity), neg_mul, Real.exp_neg, inv_mul_eq_div, div_mul_eq_mul_div,
        div_le_iff₀ he]
      rw [mul_pow] at hexp
      nlinarith
    have : ‖H z‖ * z.im ^ 3 ≤ |c| * (6 / a ^ 3) :=
      calc ‖H z‖ * z.im ^ 3 ≤ c * Real.exp (-a * z.im) * z.im ^ 3 :=
            mul_le_mul_of_nonneg_right hz (by positivity)
        _ ≤ |c| * (Real.exp (-a * z.im) * z.im ^ 3) := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)
        _ ≤ |c| * (6 / a ^ 3) := mul_le_mul_of_nonneg_left hkey (abs_nonneg c)
    linarith

theorem UpperTheory.V.Af.Rs.nicePet :
    UpperTheory.V.Af.Rs.NicePet := by
  intro k L _ f g
  refine ⟨by fun_prop, ?_⟩
  obtain ⟨B, hB⟩ := CuspFormClass.petersson_bounded_left (k : ℤ) (Subgroup.map (mapGL ℝ) (Gamma1 L)) g f
  have hdec : ∀ h : SL(2, ℤ), ∃ a > 0,
      (fun τ => UpperHalfPlane.petersson (k : ℤ) ⇑g ⇑f (h • τ)) =O[atImInfty]
        fun τ => Real.exp (-a * τ.im) := by
    intro h
    have : ((ConjAct.toConjAct (h : GL (Fin 2) ℝ)⁻¹) •
        (Subgroup.map (mapGL ℝ) (Gamma1 L))).IsArithmetic := by
      simpa [(show Rat.castHom ℝ = algebraMap ℚ ℝ by rfl), map_inv, map_mapGL]
        using! Subgroup.IsArithmetic.conj (Subgroup.map (mapGL ℝ) (Gamma1 L)) (mapGL ℚ h)⁻¹
    simp_rw [← UpperHalfPlane.petersson_slash_SL]
    exact (CuspFormClass.zero_at_infty (CuspForm.translate g h)).petersson_exp_decay_left
      (k : ℤ) _ (ModularForm.translate f h)
  have key : ∀ h : SL(2, ℤ), ∃ C : ℝ, ∀ z : ℍ,
      ‖UpperHalfPlane.petersson (k : ℤ) ⇑g ⇑f (h • z)‖ * z.im ^ 3 ≤ C := by
    intro h
    obtain ⟨a, ha, hd⟩ := hdec h
    exact bounded_petersson_weight (fun τ => UpperHalfPlane.petersson (k : ℤ) ⇑g ⇑f (h • τ)) B a ha
      (fun z => hB _) hd
  choose Cf hCf using key
  let Γ' : Subgroup SL(2, ℤ) :=
    (Subgroup.map (mapGL ℝ) (Gamma1 L)).comap (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
  have : Fintype (SL(2, ℤ) ⧸ Γ') := Subgroup.fintypeQuotientOfFiniteIndex
  have hinv : ∀ j ∈ Γ', ∀ w : ℍ,
      ‖UpperHalfPlane.petersson (k : ℤ) ⇑g ⇑f (j • w)‖ = ‖UpperHalfPlane.petersson (k : ℤ) ⇑g ⇑f w‖ :=
    fun j hj w => SlashInvariantFormClass.norm_petersson_smul (g := mapGL ℝ j) hj
  refine ⟨∑ q : SL(2, ℤ) ⧸ Γ', |Cf (Quotient.out q)⁻¹|, fun γ z _ => ?_⟩
  obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul Γ' γ⁻¹
  have hγ : γ = (j : SL(2, ℤ)) * (Quotient.out (QuotientGroup.mk γ⁻¹ : SL(2, ℤ) ⧸ Γ'))⁻¹ := by
    rw [hj]; group
  rw [hγ, mul_smul, hinv _ j.2]
  refine (hCf _ z).trans ((le_abs_self _).trans ?_)
  exact Finset.single_le_sum (f := fun q : SL(2, ℤ) ⧸ Γ' => |Cf (Quotient.out q)⁻¹|)
    (fun q _ => abs_nonneg _) (Finset.mem_univ _)
