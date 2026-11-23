import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.SplitUnitElements.IntE
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.SplitUnitElements.EUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.SplitUnitElements.Princ
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.SplitUnitElements.SplitS
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.SplitUnitElements.Fst
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.SplitUnitElements.Snd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.SplitUnitElements.Imports

open QuadraticAlgebra Matrix UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

private theorem ofE_mul {K : Type} [Field K] {Δ τ : K} (x y : Etau K τ) : ofE Δ (x * y) = ofE Δ x * ofE Δ y := by
  ext <;> simp [ofE]

private theorem ofE_one {K : Type} [Field K] {Δ τ : K} : ofE Δ (1 : Etau K τ) = 1 := by
  ext <;> simp [ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

private theorem herm_adj {K : Type} [Field K] {Δ τ : K} (c : K) (m : EL Δ τ) (u : Etau K τ) (x : Sp Δ τ) (y : EL Δ τ) :
    herm c m x (0, ofE Δ (star u) * y) = herm c m (0, ofE Δ u * x.2) (0, y) := by
  have e : star (sigL (ofE Δ (star u) * y)) = ofE Δ u * star (sigL y) := by
    ext <;> simp [ofE, sigL] <;> ring
  simp only [herm, e, star_zero, mul_zero, zero_add]
  congr 1
  ring

set_option maxHeartbeats 800000 in

theorem UpperTheory.V.Z.Sym.Loc.One.uniq :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    (∃ u : Oˣ, algebraMap O K u = τ ^ 2 - 4) → ∀ (c : K) (d m : EL Δ τ), IsDat c d m → ∀ S₀ S₁ : Set (Sp Δ τ), IsFix O c d m S₀ → IsFix O c d m S₁ →
    ∃ z : (Etau K τ)ˣ, ∀ x, x ∈ S₀ ↔ tor Δ z x ∈ S₁ := by
  intro O K _ _ _ _ _ Δ τ hl hu c d m hd
  haveI := hl.frac
  obtain ⟨hτ, h2, -, hint⟩ := One.intE O K Δ τ hl hu
  obtain ⟨ε, s₀, hs₀, hΔ⟩ := hl.even
  obtain ⟨y₀, hy⟩ := One.snd O K Δ τ hl hu c d m hd s₀⁻¹ ε (by rw [hΔ]; field_simp)
  have hsp := One.splitS O K Δ τ hl hτ h2 c d m hd
  have hmul : ∀ S, IsFix O c d m S → ∀ v : Etau K τ, IsIntegral O v → ∀ x ∈ S, ((0, ofE Δ v * x.2) : Sp Δ τ) ∈ S :=
    fun S hS v hv x hx => (hsp S hS).2.2.2 x hx v ((hint v).1 hv).1 ((hint v).1 hv).2
  have hsnd : ∀ S, IsFix O c d m S → ∀ x ∈ S, ((0, x.2) : Sp Δ τ) ∈ S := fun S hS x hx => by
    simpa [ofE_one] using hmul S hS 1 isIntegral_one x hx
  have hpr : ∀ S, IsFix O c d m S → ∃ u : (Etau K τ)ˣ, ∀ a, ((0, (y₀ : EL Δ τ) * ofE Δ a) : Sp Δ τ) ∈ S ↔
      IsIntegral O (((u⁻¹ : (Etau K τ)ˣ) : Etau K τ) * a) := fun S hS => by
    refine One.princ O K Δ τ hl hu _ (One.lat O K Δ τ hl c d m S hS y₀) fun a ha => ?_
    have hω : IsIntegral O (ω : Etau K τ) := (hint _).2 ⟨by simp, by simp⟩
    have := hmul S hS ω hω _ ha
    change ((0, (y₀ : EL Δ τ) * ofE Δ (ω * a)) : Sp Δ τ) ∈ S
    rw [ofE_mul, mul_left_comm]
    exact this
  have half : ∀ S S', IsFix O c d m S → IsFix O c d m S' → ∀ u u' : (Etau K τ)ˣ,
      (∀ a, ((0, (y₀ : EL Δ τ) * ofE Δ a) : Sp Δ τ) ∈ S ↔ IsIntegral O (((u⁻¹ : (Etau K τ)ˣ) : Etau K τ) * a)) →
      (∀ a, ((0, (y₀ : EL Δ τ) * ofE Δ a) : Sp Δ τ) ∈ S' ↔ IsIntegral O (((u'⁻¹ : (Etau K τ)ˣ) : Etau K τ) * a)) →
      (∀ x ∈ S, ((0, ofE Δ ((u' * u⁻¹ : (Etau K τ)ˣ) : Etau K τ) * x.2) : Sp Δ τ) ∈ S') ∧
        QuadraticAlgebra.norm ((u' * u⁻¹ : (Etau K τ)ˣ) : Etau K τ) ∈ (algebraMap O K).range := by
    intro S S' hS hS' u u' h h'
    have k : ∀ a, ((0, (y₀ : EL Δ τ) * ofE Δ a) : Sp Δ τ) ∈ S →
        ((0, (y₀ : EL Δ τ) * ofE Δ (((u' * u⁻¹ : (Etau K τ)ˣ) : Etau K τ) * a)) : Sp Δ τ) ∈ S' := fun a ha => by
      rw [h', Units.val_mul, mul_assoc, Units.inv_mul_cancel_left]
      exact (h a).1 ha
    have f : ∀ x ∈ S, ((0, ofE Δ ((u' * u⁻¹ : (Etau K τ)ˣ) : Etau K τ) * x.2) : Sp Δ τ) ∈ S' := fun x hx => by
      obtain ⟨a, b, e, ha, hb⟩ := (hy S hS x.2).1 (hsnd S hS x hx)
      refine (hy S' hS' _).2 ⟨_, _, ?_, k a ha, k b hb⟩
      rw [e, ofE_mul, ofE_mul, ← mul_smul_comm]
      ring
    refine ⟨f, ?_⟩
    generalize ((u' * u⁻¹ : (Etau K τ)ˣ) : Etau K τ) = t at f
    have g : ∀ y, ((0, y) : Sp Δ τ) ∈ S' → ((0, ofE Δ (star t) * y) : Sp Δ τ) ∈ S := fun y hy' =>
      (hS.dual _).2 fun x hx => by
        rw [herm_adj]
        exact (hS'.dual _).1 hy' _ (f x hx)
    have h1 : ((0, (y₀ : EL Δ τ) * ofE Δ (u : Etau K τ)) : Sp Δ τ) ∈ S := by
      rw [h, Units.inv_mul]; exact isIntegral_one
    have h3 := g _ (f _ h1)
    have e : ofE Δ (star t) * (ofE Δ t * ((y₀ : EL Δ τ) * ofE Δ (u : Etau K τ))) =
        (y₀ : EL Δ τ) * ofE Δ ((u : Etau K τ) * (t * star t)) := by
      rw [ofE_mul, ofE_mul]; ring
    dsimp only at h3
    rw [e, h, Units.inv_mul_cancel_left, ← algebraMap_norm_eq_mul_star] at h3
    simpa using ((hint _).1 h3).1
  intro S₀ S₁ h₀ h₁
  obtain ⟨u₀, hu₀⟩ := hpr S₀ h₀
  obtain ⟨u₁, hu₁⟩ := hpr S₁ h₁
  obtain ⟨f₀, n₀, hn₀⟩ := half S₀ S₁ h₀ h₁ u₀ u₁ hu₀ hu₁
  obtain ⟨f₁, n₁, hn₁⟩ := half S₁ S₀ h₁ h₀ u₁ u₀ hu₁ hu₀
  have hinv : u₀ * u₁⁻¹ = (u₁ * u₀⁻¹)⁻¹ := by simp
  rw [hinv] at f₁ hn₁
  generalize u₁ * u₀⁻¹ = u at f₀ f₁ hn₀ hn₁
  have hn : n₀ * n₁ = 1 := IsFractionRing.injective O K (by
    rw [map_mul, hn₀, hn₁, ← map_mul, Units.mul_inv, map_one, map_one])
  obtain ⟨z, v, hv, hv', e⟩ := One.eUnit O K Δ τ hl hu u ⟨Units.mkOfMulEqOne n₀ n₁ hn, hn₀.symm⟩
  refine ⟨z, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · have a := One.fst O K Δ τ hl hτ h2 c d m hd S₀ S₁ h₀ h₁ _ ((hsp S₀ h₀).2.2.1 x hx)
    have b := f₀ _ (hmul S₀ h₀ _ hv' x hx)
    have := (hsp S₁ h₁).1 _ a _ b
    rw [e, ← mul_assoc, ← ofE_mul, Units.mul_inv_cancel_right] at this
    simpa [tor] using this
  · have a := One.fst O K Δ τ hl hτ h2 c d m hd S₁ S₀ h₁ h₀ _ ((hsp S₁ h₁).2.2.1 _ hx)
    have b := f₁ _ (hmul S₁ h₁ _ hv _ hx)
    have := (hsp S₀ h₀).1 _ a _ b
    have e' : ofE Δ ((u⁻¹ : (Etau K τ)ˣ) : Etau K τ) * (ofE Δ (v : Etau K τ) * (ofE Δ (quo z) * x.2)) = x.2 := by
      rw [← mul_assoc (ofE Δ (v : Etau K τ)), ← ofE_mul, mul_comm (v : Etau K τ), ← e, ← mul_assoc, ← ofE_mul, Units.inv_mul, ofE_one,
        one_mul]
    simp only [tor, e'] at this
    simpa using this
