import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExtReal

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Published
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc

private theorem tendsto_zero_adicCompletion_of_eventually_mem_pow {F : Type} [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (x : ℕ → NumberField.RingOfIntegers F)
    (hx : ∀ j : ℕ, ∀ᶠ k in Filter.atTop, x k ∈ v.asIdeal ^ j) :
    Filter.Tendsto (fun k => ((algebraMap (NumberField.RingOfIntegers F) F (x k) : F) :
      v.adicCompletion F)) Filter.atTop (nhds 0) := by
  rw [(Valued.hasBasis_nhds_zero _ _).tendsto_right_iff]
  intro γ _
  have h0 : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).restrict 0
      < γ.1 := by
    rw [map_zero]
    exact Units.zero_lt γ
  rw [Valuation.restrict_lt_iff_lt_embedding, map_zero] at h0
  obtain ⟨j, hj⟩ : ∃ j : ℕ, WithZero.exp (-(j : ℤ)) <
      MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := by
    refine ⟨(-(WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1))).toNat + 1, ?_⟩
    conv_rhs => rw [← WithZero.exp_log h0.ne']
    rw [WithZero.exp_lt_exp]
    omega
  filter_upwards [hx j] with k hk
  show Valued.v.restrict _ < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  refine lt_of_le_of_lt ?_ hj
  have := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := F) v
    (algebraMap (NumberField.RingOfIntegers F) F (x k))
  refine le_of_eq_of_le this ?_
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  exact (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v _ j).2 hk

private theorem eventually_unit_pow_factorial_sub_one_mem {F : Type} [Field F] [NumberField F]
    (u : (NumberField.RingOfIntegers F)ˣ) (I : Ideal (NumberField.RingOfIntegers F))
    (hI : I ≠ ⊥) :
    ∀ᶠ k in Filter.atTop, ((u : NumberField.RingOfIntegers F) ^ (Nat.factorial k) - 1) ∈ I := by
  haveI := Ideal.finiteQuotientOfFreeOfNeBot I hI
  have hM : 0 < Nat.card (NumberField.RingOfIntegers F ⧸ I)ˣ := Nat.card_pos
  filter_upwards [Filter.eventually_ge_atTop (Nat.card (NumberField.RingOfIntegers F ⧸ I)ˣ)]
    with k hk
  obtain ⟨c, hc⟩ := Nat.dvd_factorial hM hk
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, sub_eq_zero]
  have h1 : (Units.map (Ideal.Quotient.mk I : NumberField.RingOfIntegers F →* _) u) ^
      Nat.card (NumberField.RingOfIntegers F ⧸ I)ˣ = 1 := pow_card_eq_one'
  have h3 : (Ideal.Quotient.mk I (u : NumberField.RingOfIntegers F)) ^
      Nat.card (NumberField.RingOfIntegers F ⧸ I)ˣ = 1 := by
    have := congrArg Units.val h1
    rw [Units.val_pow_eq_pow_val, Units.coe_map, Units.val_one] at this
    exact this
  rw [hc, pow_mul, map_pow, map_pow, h3, one_pow]

private theorem tendsto_unit_pow_factorial_finiteAdele_one {F : Type} [Field F] [NumberField F]
    (u : (NumberField.RingOfIntegers F)ˣ) :
    Filter.Tendsto (fun k : ℕ => algebraMap F (IsDedekindDomain.FiniteAdeleRing
      (NumberField.RingOfIntegers F) F)
      (algebraMap (NumberField.RingOfIntegers F) F ((u : NumberField.RingOfIntegers F) ^
        (Nat.factorial k)))) Filter.atTop (nhds 1) := by
  let g : ℕ → (Π v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
      v.adicCompletionIntegers F) := fun k v =>
    ⟨((algebraMap (NumberField.RingOfIntegers F) F ((u : NumberField.RingOfIntegers F) ^
        (Nat.factorial k)) : F) : v.adicCompletion F),
      IsDedekindDomain.HeightOneSpectrum.coe_algebraMap_mem _ _ v _⟩
  have hg : Filter.Tendsto g Filter.atTop (nhds 1) := by
    rw [tendsto_pi_nhds]
    intro v
    rw [tendsto_subtype_rng]
    have h := (tendsto_zero_adicCompletion_of_eventually_mem_pow v (fun k => (u : NumberField.RingOfIntegers F) ^ (Nat.factorial k) - 1)
      (fun j => eventually_unit_pow_factorial_sub_one_mem u _ (pow_ne_zero _ v.ne_bot))).add_const 1
    rw [zero_add] at h
    have e : ∀ k : ℕ, ((algebraMap (NumberField.RingOfIntegers F) F
        ((u : NumberField.RingOfIntegers F) ^ (Nat.factorial k) - 1) : F) : v.adicCompletion F) + 1
        = ((algebraMap (NumberField.RingOfIntegers F) F
        ((u : NumberField.RingOfIntegers F) ^ (Nat.factorial k)) : F) : v.adicCompletion F) := by
      intro k
      change algebraMap F (v.adicCompletion F) (algebraMap (NumberField.RingOfIntegers F) F
          ((u : NumberField.RingOfIntegers F) ^ (Nat.factorial k) - 1)) + 1 =
        algebraMap F (v.adicCompletion F) (algebraMap (NumberField.RingOfIntegers F) F
          ((u : NumberField.RingOfIntegers F) ^ (Nat.factorial k)))
      rw [map_sub (algebraMap (NumberField.RingOfIntegers F) F), map_one, map_sub, map_one,
        sub_add_cancel]
    exact h.congr e
  exact ((RestrictedProduct.isEmbedding_structureMap).continuous.tendsto 1).comp hg

private theorem infDiag_inv_unit_eq_infinite_one {F : Type} [Field F] [NumberField F] (u : Fˣ) :
    (((Formalism.L2.Host.infDiag u : Neutral.B1.Ideles F) :
      NumberField.AdeleRing (NumberField.RingOfIntegers F) F)) =
      ((algebraMap F (NumberField.InfiniteAdeleRing F) u, 1) : NumberField.InfiniteAdeleRing F ×
        IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F) := by
  classical
  rw [Formalism.L2.Host.infDiag, MonoidHom.finset_prod_apply, Units.coe_prod]
  let p2 : NumberField.AdeleRing (NumberField.RingOfIntegers F) F →*
      IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F :=
    ⟨⟨Prod.snd, rfl⟩, fun _ _ => rfl⟩
  refine Prod.ext ?_ ?_
  · funext w
    let q : NumberField.AdeleRing (NumberField.RingOfIntegers F) F →* w.Completion :=
      ⟨⟨fun x => x.1 w, rfl⟩, fun _ _ => rfl⟩
    change q _ = _
    rw [map_prod, Finset.prod_eq_single w]
    · exact Pi.mulSingle_eq_same (M := fun v : NumberField.InfinitePlace F => v.Completion) w _
    · intro b _ hb
      exact Pi.mulSingle_eq_of_ne (Ne.symm hb) _
    · intro h
      exact absurd (Finset.mem_univ w) h
  · change p2 _ = _
    rw [map_prod]
    exact Finset.prod_eq_one (fun _ _ => rfl)

private theorem one_le_of_tendsto_pow_factorial_one (r : ℝ) (h0 : 0 ≤ r)
    (h : Filter.Tendsto (fun k : ℕ => r ^ (Nat.factorial k)) Filter.atTop (nhds 1)) : 1 ≤ r := by
  by_contra hr
  push_neg at hr
  have hf : Filter.Tendsto (fun k : ℕ => Nat.factorial k) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono Nat.self_le_factorial Filter.tendsto_id
  have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one h0 hr).comp hf
  have := tendsto_nhds_unique h h2
  norm_num at this

private theorem one_le_norm_char_diagUnits_unit_of_continuous {F : Type} [Field F] [NumberField F]
    (χ : Neutral.B1.Ideles F →* ℂˣ) (hχ : Continuous χ) (u : (NumberField.RingOfIntegers F)ˣ) :
    1 ≤ ‖((χ (((Formalism.L2.Host.infDiag)⁻¹ * Neutral.B1.diagUnits F : Fˣ →* Neutral.B1.Ideles F)
      (Units.map (algebraMap (NumberField.RingOfIntegers F) F).toMonoidHom u)) : ℂˣ) : ℂ)‖ := by
  set θ : Fˣ →* Neutral.B1.Ideles F := (Formalism.L2.Host.infDiag)⁻¹ * Neutral.B1.diagUnits F with hθ
  have hval : ∀ y : Fˣ, ((θ y : Neutral.B1.Ideles F) :
      NumberField.AdeleRing (NumberField.RingOfIntegers F) F) =
      ((1 : NumberField.InfiniteAdeleRing F),
        algebraMap F (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F) (y : F)) := by
    intro y
    have e1 : ((Formalism.L2.Host.infDiag y : Neutral.B1.Ideles F) :
        NumberField.AdeleRing (NumberField.RingOfIntegers F) F) *
        (show NumberField.AdeleRing (NumberField.RingOfIntegers F) F from
          ((1 : NumberField.InfiniteAdeleRing F),
          algebraMap F (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F) (y : F))) =
        ((Neutral.B1.diagUnits F y : Neutral.B1.Ideles F) :
          NumberField.AdeleRing (NumberField.RingOfIntegers F) F) := by
      rw [infDiag_inv_unit_eq_infinite_one]
      refine Prod.ext ?_ ?_
      · change algebraMap F (NumberField.InfiniteAdeleRing F) (y : F) * 1 = _
        rw [mul_one]
        rfl
      · change 1 * algebraMap F (IsDedekindDomain.FiniteAdeleRing
          (NumberField.RingOfIntegers F) F) (y : F) = _
        rw [one_mul]
        rfl
    rw [hθ, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, ← e1,
      Units.inv_mul_cancel_left]
  have key : ∀ y : (NumberField.RingOfIntegers F)ˣ, Filter.Tendsto
      (fun k : ℕ => ((θ (Units.map (algebraMap (NumberField.RingOfIntegers F) F).toMonoidHom y) ^
        (Nat.factorial k) : Neutral.B1.Ideles F) :
          NumberField.AdeleRing (NumberField.RingOfIntegers F) F)) Filter.atTop (nhds 1) := by
    intro y
    have h := (tendsto_const_nhds (x := (1 : NumberField.InfiniteAdeleRing F))).prodMk_nhds
      (tendsto_unit_pow_factorial_finiteAdele_one y)
    refine h.congr (fun k => ?_)
    rw [← map_pow, hval]
    congr 2
  have ht : ∀ y : (NumberField.RingOfIntegers F)ˣ, Filter.Tendsto
      (fun k : ℕ => θ (Units.map (algebraMap (NumberField.RingOfIntegers F) F).toMonoidHom y) ^
        (Nat.factorial k)) Filter.atTop (nhds 1) := by
    intro y
    rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff, map_one]
    refine Filter.Tendsto.prodMk_nhds (key y) ?_
    have h2 := (MulOpposite.continuous_op.tendsto _).comp (key y⁻¹)
    refine h2.congr (fun k => ?_)
    simp [map_inv, inv_pow]
  have hc := ((Units.continuous_val.comp hχ).tendsto 1).comp
    (ht u)
  have hn := (continuous_norm.tendsto _).comp hc
  apply one_le_of_tendsto_pow_factorial_one _ (norm_nonneg _)
  refine (hn.congr (fun k => ?_)).trans ?_
  · simp [Function.comp, map_pow, norm_pow]
  · simp

private theorem const_of_sum_mul_log_norm_unit_eq_zero {F : Type} [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (a : (F →+* ℂ) → ℤ)
    (ha : ∀ u : (NumberField.RingOfIntegers F)ˣ,
      ∑ φ : F →+* ℂ, (a φ : ℝ) * Real.log ‖φ ((u : NumberField.RingOfIntegers F) : F)‖ = 0) :
    ∀ φ φ' : F →+* ℂ, a φ = a φ' := by
  have inj : ∀ φ ψ : F →+* ℂ, NumberField.InfinitePlace.mk φ = NumberField.InfinitePlace.mk ψ →
      φ = ψ := by
    intro φ ψ h
    rcases NumberField.InfinitePlace.mk_eq_iff.mp h with h1 | h1
    · exact h1
    · rwa [NumberField.ComplexEmbedding.isReal_iff.mp
        (NumberField.IsTotallyReal.complexEmbedding_isReal φ)] at h1
  have hsum : ∀ u : (NumberField.RingOfIntegers F)ˣ,
      ∑ φ : F →+* ℂ, Real.log ‖φ ((u : NumberField.RingOfIntegers F) : F)‖ = 0 := by
    intro u
    rw [← NumberField.Units.sum_mult_mul_log u]
    refine Fintype.sum_bijective (fun φ => NumberField.InfinitePlace.mk φ)
      ⟨fun φ ψ h => inj φ ψ h, fun w => ⟨w.embedding, NumberField.InfinitePlace.mk_embedding w⟩⟩
      _ _ (fun φ => ?_)
    simp [NumberField.IsTotallyReal.mult_eq, NumberField.InfinitePlace.apply]
  haveI : Nonempty (F →+* ℂ) := ⟨(Classical.arbitrary (NumberField.InfinitePlace F)).embedding⟩
  obtain ⟨φ₀, hφ₀⟩ := Finite.exists_min a
  obtain ⟨u, hu⟩ := NumberField.Units.dirichletUnitTheorem.exists_unit F
    (NumberField.InfinitePlace.mk φ₀)
  have hneg : ∀ φ : F →+* ℂ, φ ≠ φ₀ →
      Real.log ‖φ ((u : NumberField.RingOfIntegers F) : F)‖ < 0 := by
    intro φ hφ
    have := hu (NumberField.InfinitePlace.mk φ) (fun h => hφ (inj _ _ h))
    simpa [NumberField.InfinitePlace.apply] using this
  have h0 : ∑ φ : F →+* ℂ, ((a φ : ℝ) - a φ₀) *
      Real.log ‖φ ((u : NumberField.RingOfIntegers F) : F)‖ = 0 := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, ha u, hsum u, mul_zero, sub_zero]
  have hle : ∀ φ ∈ (Finset.univ : Finset (F →+* ℂ)), ((a φ : ℝ) - a φ₀) *
      Real.log ‖φ ((u : NumberField.RingOfIntegers F) : F)‖ ≤ 0 := by
    intro φ _
    by_cases hφ : φ = φ₀
    · subst hφ
      simp
    · have h1 : (0 : ℝ) ≤ (a φ : ℝ) - a φ₀ := by
        have := hφ₀ φ
        rw [sub_nonneg]
        exact_mod_cast this
      exact mul_nonpos_of_nonneg_of_nonpos h1 (hneg φ hφ).le
  have hz := (Finset.sum_eq_zero_iff_of_nonpos hle).mp h0
  have key : ∀ φ : F →+* ℂ, a φ = a φ₀ := by
    intro φ
    by_cases hφ : φ = φ₀
    · rw [hφ]
    · have := hz φ (Finset.mem_univ _)
      rcases mul_eq_zero.mp this with h | h
      · have : (a φ : ℝ) = a φ₀ := by linarith
        exact_mod_cast this
      · exact absurd h (hneg φ hφ).ne
  intro φ φ'
  rw [key φ, key φ']

theorem UpperTheory.heckeChar_parallel_weight :
    UpperTheory.V.Af.Cr.Parallel := by
  intro F _ _ _ χ a h
  have hc : Continuous (χ : Neutral.B1.Ideles F →* ℂˣ) := χ.2.1
  have hθ : ∀ y : Fˣ, (χ : Neutral.B1.Ideles F →* ℂˣ)
      ((Formalism.L2.Host.infDiag⁻¹ * Neutral.B1.diagUnits F : Fˣ →* Neutral.B1.Ideles F) y) =
      (χ.inf y)⁻¹ := by
    intro y
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, map_inv, χ.2.2 y, mul_one]
    rfl
  have hn1 : ∀ u : (NumberField.RingOfIntegers F)ˣ,
      ‖((χ.inf (Units.map (algebraMap (NumberField.RingOfIntegers F) F).toMonoidHom u) : ℂˣ) : ℂ)‖
        ≤ 1 := by
    intro u
    have := one_le_norm_char_diagUnits_unit_of_continuous (χ : Neutral.B1.Ideles F →* ℂˣ) hc u
    rw [hθ, Units.val_inv_eq_inv_val, norm_inv] at this
    have hp : 0 < ‖((χ.inf (Units.map (algebraMap (NumberField.RingOfIntegers F) F).toMonoidHom u)
      : ℂˣ) : ℂ)‖ := norm_pos_iff.mpr (Units.ne_zero _)
    exact (one_le_inv₀ hp).mp this
  apply const_of_sum_mul_log_norm_unit_eq_zero a
  intro u
  have hn : ‖((χ.inf (Units.map (algebraMap (NumberField.RingOfIntegers F) F).toMonoidHom u) : ℂˣ)
      : ℂ)‖ = 1 := by
    have h1 := hn1 u
    have h2 := hn1 u⁻¹
    rw [map_inv, map_inv, Units.val_inv_eq_inv_val, norm_inv] at h2
    have hp : 0 < ‖((χ.inf (Units.map (algebraMap (NumberField.RingOfIntegers F) F).toMonoidHom u)
      : ℂˣ) : ℂ)‖ := norm_pos_iff.mpr (Units.ne_zero _)
    exact le_antisymm h1 ((inv_le_one₀ hp).mp h2)
  have hpos : ∀ ψ : F →+* ℝ, 0 < ψ (((Units.map (algebraMap (NumberField.RingOfIntegers F) F).toMonoidHom u) ^ 2 : Fˣ) : F) := by
    intro ψ
    have hx : ψ (((Units.map (algebraMap (NumberField.RingOfIntegers F) F).toMonoidHom u) : Fˣ) : F) ≠ 0 :=
      (map_ne_zero ψ).mpr (Units.ne_zero _)
    rw [Units.val_pow_eq_pow_val, map_pow]
    exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hx))
  have hv := congrArg norm (h _ hpos)
  rw [map_pow, Units.val_pow_eq_pow_val, norm_pow, hn, one_pow, norm_prod] at hv
  simp only [norm_zpow, Units.val_pow_eq_pow_val, map_pow, norm_pow] at hv
  have hl := congrArg Real.log hv
  rw [Real.log_one, Real.log_prod] at hl
  · simp only [Real.log_zpow] at hl
    have e : ∀ φ : F →+* ℂ, (a φ : ℝ) * Real.log (‖φ (((Units.map (algebraMap
        (NumberField.RingOfIntegers F) F).toMonoidHom u) : Fˣ) : F)‖ ^ 2) =
        2 * ((a φ : ℝ) * Real.log ‖φ (((Units.map (algebraMap
        (NumberField.RingOfIntegers F) F).toMonoidHom u) : Fˣ) : F)‖) := by
      intro φ
      rw [Real.log_pow]
      push_cast
      ring
    simp only [e, ← Finset.mul_sum] at hl
    have h2 : ∑ φ : F →+* ℂ, (a φ : ℝ) * Real.log ‖φ (((Units.map (algebraMap
        (NumberField.RingOfIntegers F) F).toMonoidHom u) : Fˣ) : F)‖ = 0 := by linarith
    exact h2
  · intro φ _
    exact zpow_ne_zero _ (pow_ne_zero _ (norm_ne_zero_iff.mpr ((map_ne_zero φ).mpr
      (Units.ne_zero _))))
