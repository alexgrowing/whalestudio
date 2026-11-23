import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.GeoTransport

open NumberField IsDedekindDomain ValuativeRel PositivityTheory.Rg.Tf.Loc GroundTheory.Global GroundTheory.Global.SemiLocal PositivityTheory.Rg.Tf.Geo
open scoped TensorProduct

theorem UpperTheory.V.Z.Tf.Orb.placeData :
    UpperTheory.V.Z.Tf.Orb.PlaceData := by
  intro F E _ _ _ _ _ _ σ hσ v w hw
  have hfix : ∀ τ : E ≃ₐ[F] E, w.1 = τ • w.1 := fun τ => (congrArg Subtype.val (hw (τ • w))).symm
  have hrk : Module.finrank (v.adicCompletion F) (w.1.adicCompletion E) = Module.finrank F E := by
    rw [← sum_finrank_eq E v, Finset.sum_eq_single w (fun b _ hb => absurd (hw b) hb) (by simp)]
  have hfin : FiniteDimensional (v.adicCompletion F) (w.1.adicCompletion E) :=
    Module.finite_of_finrank_pos (hrk ▸ Module.finrank_pos)
  have he0 : w.1.asIdeal.ramificationIdx (𝓞 F) ≠ 0 := (Ideal.ramificationIdx_pos w.1.asIdeal (𝓞 F)).ne'
  have hle : ∀ x y : w.1.adicCompletion E, valuation _ x ≤ valuation _ y ↔ Valued.v x ≤ Valued.v y := fun x y =>
    ValuativeRel.isEquiv (valuation (w.1.adicCompletion E)) Valued.v x y
  have hlt : ∀ x : w.1.adicCompletion E, valuation _ x < 1 ↔ Valued.v x < 1 := fun x =>
    (ValuativeRel.isEquiv (valuation (w.1.adicCompletion E)) Valued.v).lt_one_iff_lt_one
  have hval : ValuativeExtension (v.adicCompletion F) (w.1.adicCompletion E) := ⟨fun a b => by
    change Valued.v (completionMap v w.1 a) ≤ Valued.v (completionMap v w.1 b) ↔ Valued.v a ≤ Valued.v b
    rw [valued_completionMap, valued_completionMap]
    exact pow_le_pow_iff_left₀ zero_le zero_le he0⟩
  let Φ : (E ≃ₐ[F] E) →* (w.1.adicCompletion E ≃ₐ[v.adicCompletion F] w.1.adicCompletion E) :=
    MonoidHom.mk' (fun τ => galEquiv v τ w.1 w.1 (hfix τ)) fun a b => AlgEquiv.ext fun y => by
      refine congrFun ((HeightOneSpectrum.denseRange_algebraMap E w.1).equalizer
        (continuous_galEquiv v (a * b) w.1 w.1 (hfix _))
        ((continuous_galEquiv v a w.1 w.1 (hfix _)).comp (continuous_galEquiv v b w.1 w.1 (hfix _))) ?_) y
      funext x
      simp only [Function.comp_apply, galEquiv_algebraMap, AlgEquiv.mul_apply]
  have hinj : Function.Injective Φ := fun a b h => AlgEquiv.ext fun x => by
    have h1 := DFunLike.congr_fun h (algebraMap E (w.1.adicCompletion E) x)
    change galEquiv v a w.1 w.1 (hfix _) _ = galEquiv v b w.1 w.1 (hfix _) _ at h1
    rw [galEquiv_algebraMap, galEquiv_algebraMap] at h1
    exact (algebraMap E (w.1.adicCompletion E)).injective h1
  have hc : Nat.card (w.1.adicCompletion E ≃ₐ[v.adicCompletion F] w.1.adicCompletion E) = Nat.card (E ≃ₐ[F] E) := by
    refine le_antisymm ?_ (Nat.card_le_card_of_injective Φ hinj)
    rw [IsGalois.card_aut_eq_finrank F E, ← hrk, Nat.card_eq_fintype_card]
    exact AlgEquiv.card_le
  have hgal : IsGalois (v.adicCompletion F) (w.1.adicCompletion E) :=
    IsGalois.of_card_aut_eq_finrank _ _ (by rw [hc, IsGalois.card_aut_eq_finrank F E, hrk])
  have hsurj : Function.Surjective Φ := ((Nat.bijective_iff_injective_and_card Φ).2 ⟨hinj, hc.symm⟩).2
  refine ⟨inferInstance, hval, hfin, hgal, Φ σ, fun τ => ?_, hrk, fun x => rfl, fun y => ?_, fun hu => ?_⟩
  · obtain ⟨a, rfl⟩ := hsurj τ
    obtain ⟨j, rfl⟩ := hσ a
    exact ⟨j, (map_zpow Φ σ j).symm⟩
  · obtain ⟨t, rfl⟩ := (tensorEquiv' E v).surjective y
    have h1 : galFin σ v (tensorEquiv' E v t) =
        tensorEquiv' E v (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F (v.adicCompletion F)) t) := by
      simp [galFin, galOf]
    rw [h1]
    clear h1
    induction t with
    | zero => simp
    | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]
    | tmul x a =>
      rw [Algebra.TensorProduct.map_tmul, tensorEquiv'_tmul, tensorEquiv'_tmul, Pi.mul_apply, Pi.mul_apply, map_mul]
      congr 1
      · exact (galEquiv_algebraMap v σ w.1 w.1 (hfix σ) x).symm
      · exact ((Φ σ).commutes a).symm
  · have := w.1.isPrime
    have he : w.1.asIdeal.ramificationIdx (𝓞 F) = 1 := Ideal.ramificationIdx_eq_one_iff.2 hu
    obtain ⟨π, hπ⟩ := valued_adicCompletion_surjective (K := F) v (WithZero.exp (-1 : ℤ))
    have h1 : Valued.v (algebraMap (v.adicCompletion F) (w.1.adicCompletion E) π) = WithZero.exp (-1 : ℤ) := by
      rw [algebraMap_completion_eq, valued_completionMap, he, pow_one, hπ]
    refine ⟨π, (hlt _).2 (by rw [h1, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega), fun x hx => (hle _ _).2 ?_⟩
    rw [h1]
    have h2 := (hlt x).1 hx
    by_cases h0 : Valued.v x = 0
    · rw [h0]; exact zero_le
    · rw [← WithZero.exp_log h0] at h2 ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h2
      rw [WithZero.exp_le_exp]
      omega
