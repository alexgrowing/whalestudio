import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.CintIdx

open QuadraticAlgebra Matrix UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.One.intE :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
        (∃ u : Oˣ, algebraMap O K u = τ ^ 2 - 4) → τ ∈ (algebraMap O K).range ∧ (∃ u : Oˣ, algebraMap O K u = 2 - τ) ∧ (∃ u : Oˣ, algebraMap O K u = 2 + τ) ∧
        ∀ x : Etau K τ, IsIntegral O x ↔ x.re ∈ (algebraMap O K).range ∧ x.im ∈ (algebraMap O K).range := by
  rintro O K _ _ _ _ _ Δ τ L ⟨u, hu⟩
  haveI := L.frac
  have sq_int : ∀ (x : K) (a : O), x ^ 2 = algebraMap O K a → ∃ b : O, algebraMap O K b = x := fun x a h =>
    IsIntegrallyClosed.algebraMap_eq_of_integral (IsIntegral.of_pow (n := 2) (by norm_num) (h ▸ isIntegral_algebraMap))
  obtain ⟨τ₀, e₀⟩ := sq_int τ (4 + u) (by rw [map_add, hu, map_ofNat]; ring)
  have hm : (2 - τ₀) * (2 + τ₀) = (-u : Oˣ) := IsFractionRing.injective O K (by
    simp only [map_mul, map_sub, map_add, map_ofNat, e₀, Units.val_neg, map_neg, hu]; ring)
  have h1 : IsUnit (2 - τ₀) := isUnit_of_mul_isUnit_left (hm ▸ (-u).isUnit)
  have h2 : IsUnit (2 + τ₀) := isUnit_of_mul_isUnit_right (hm ▸ (-u).isUnit)
  refine ⟨⟨τ₀, e₀⟩, ⟨h1.unit, by simp [map_ofNat, e₀]⟩, ⟨h2.unit, by simp [map_ofNat, e₀]⟩, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · have down : ∀ a : K, IsIntegral O (algebraMap K (Etau K τ) a) → ∃ b : O, algebraMap O K b = a := fun a h =>
      IsIntegrallyClosed.algebraMap_eq_of_integral ((isIntegral_algebraMap_iff (algebraMap K (Etau K τ)).injective).1 h)
    obtain ⟨t, ht⟩ := down (2 * x.re + τ * x.im) (by
      convert hx.add (isIntegral_star hx) using 1
      ext <;> simp; ring)
    obtain ⟨d, hd⟩ := down (x.im ^ 2 * (τ ^ 2 - 4)) (by
      convert (hx.sub (isIntegral_star hx)).pow 2 using 1
      ext <;> simp [sq] <;> ring)
    have hi : algebraMap O K u * algebraMap O K (u⁻¹ : Oˣ) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    obtain ⟨b, hb⟩ := sq_int x.im (d * (u⁻¹ : Oˣ)) (by rw [map_mul, hd, ← hu]; linear_combination (-x.im ^ 2) * hi)
    obtain ⟨i, hi2⟩ := L.two.exists_right_inv
    have hi2' : 2 * algebraMap O K i = 1 := by rw [← map_ofNat (algebraMap O K) 2, ← map_mul, hi2, map_one]
    refine ⟨⟨i * (t - τ₀ * b), ?_⟩, ⟨b, hb⟩⟩
    rw [map_mul, map_sub, map_mul, ht, e₀, hb]
    linear_combination x.re * hi2'
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine isIntegral_of_trace_norm (2 * a + τ₀ * b) (a * a + τ₀ * a * b + b * b) ?_ ?_
    · simp [QuadraticAlgebra.trace_def, map_ofNat, ha, hb, e₀]
    · simp [QuadraticAlgebra.norm_def, ha, hb, e₀]
