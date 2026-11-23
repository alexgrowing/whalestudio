import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.TwoLe

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct
open scoped nonZeroDivisors

private theorem fractionalIdeal_count_spanSingleton_eq_ordP {F : Type} [Field F] [NumberField F] (P : HeightOneSpectrum (𝓞 F)) (x : Fˣ) :
    FractionalIdeal.count F P (FractionalIdeal.spanSingleton (𝓞 F)⁰ (x : F)) = ordP P x := by
  obtain ⟨r, s, hs, hrs⟩ := IsFractionRing.div_surjective (𝓞 F) (x : F)
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hrs
    exact x.ne_zero hrs.symm
  have hI : FractionalIdeal.spanSingleton (𝓞 F)⁰ (x : F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ ((algebraMap (𝓞 F) F) s)⁻¹ * ↑(Ideal.span {r}) := by
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton,
      ← hrs, div_eq_mul_inv, mul_comm]
  rw [FractionalIdeal.count_well_defined F P (by rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact x.ne_zero) hI]
  unfold ordP
  rw [← hrs, map_div₀]
  erw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
  rw [HeightOneSpectrum.intValuation_if_neg _ hr0, HeightOneSpectrum.intValuation_if_neg _ hs0,
    ← WithZero.exp_sub, WithZero.log_exp]
  ring

theorem UpperTheory.V.ZK.Ct.clFin :
    ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (γ : F ≃ₐ[L] F) (a : ℕ) (D : Dat (Additive Fˣ) (HeightOneSpectrum (𝓞 F) →₀ ℤ)), IsDat γ a D → Finite ((HeightOneSpectrum (𝓞 F) →₀ ℤ) ⧸ LinearMap.range D.d) := by
  intro L F _ _ _ _ _ γ a D hD
  classical
  obtain ⟨I, hI⟩ : ∃ I : (HeightOneSpectrum (𝓞 F) →₀ ℤ) → (FractionalIdeal (𝓞 F)⁰ F)ˣ,
      ∀ e P, FractionalIdeal.count F P (I e : FractionalIdeal (𝓞 F)⁰ F) = e P :=
    ⟨fun e => Units.mk0 (e.prod fun P n => ((P.asIdeal : FractionalIdeal (𝓞 F)⁰ F)) ^ n)
      (Finset.prod_ne_zero_iff.mpr fun P _ =>
        zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr P.ne_bot)),
      fun e P => FractionalIdeal.count_finsuppProd F P e⟩
  have key : ∀ e e', ClassGroup.mk F (I e) = ClassGroup.mk F (I e') → e - e' ∈ LinearMap.range D.d := by
    intro e e' h
    have h' : ClassGroup.mk F (I e * (I e')⁻¹) = 1 := by
      rw [map_mul, map_inv, h, mul_inv_cancel]
    obtain ⟨x, hx⟩ := (ClassGroup.mk_eq_one_iff.1 h').principal
    have hJ : ((I e * (I e')⁻¹ : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) =
        FractionalIdeal.spanSingleton (𝓞 F)⁰ x := by
      apply FractionalIdeal.coeToSubmodule_injective
      dsimp only
      rw [FractionalIdeal.coe_spanSingleton]
      exact hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [FractionalIdeal.spanSingleton_zero] at hJ
      exact Units.ne_zero _ hJ
    refine ⟨Additive.ofMul (Units.mk0 x hx0), ?_⟩
    ext P
    rw [hD.d_eq, Finsupp.coe_sub, Pi.sub_apply, ← hI e P, ← hI e' P, ← fractionalIdeal_count_spanSingleton_eq_ordP, Units.val_mk0, ← hJ,
      Units.val_mul, Units.val_inv_eq_inv_val,
      FractionalIdeal.count_mul F P (Units.ne_zero _) (inv_ne_zero (Units.ne_zero _)),
      FractionalIdeal.count_inv]
    ring
  refine Finite.of_injective (fun q => ClassGroup.mk F (I (Quotient.out q))) ?_
  intro q1 q2 h
  rw [← Submodule.Quotient.mk_out q1, ← Submodule.Quotient.mk_out q2]
  exact (Submodule.Quotient.eq _).2 (key _ _ h)
