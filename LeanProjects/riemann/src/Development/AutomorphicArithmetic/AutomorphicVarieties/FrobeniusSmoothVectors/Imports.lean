import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.star :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → (∀ g : F.G0, F.star (F.star g) = g) ∧ (∀ g h : F.G0, F.star (g * h) = F.star h * F.star g) ∧ (∀ g : F.G0, F.Ψ (F.star g) = (F.Ψ g)⁻¹) ∧ Continuous F.star ∧ ∀ {n : ℕ} {K : Type} [CommRing K] (ρ : NRep F n K) (g : F.G0) (i j : Fin n), ρ.r (F.star g) i j = ρ.r g j.rev i.rev := by
  intro l _ k _ _ F C₀ hF
  have hs : ∀ g : F.G0, ((F.star g : F.G0) : F.Γ) = F.c * (g : F.Γ)⁻¹ * F.c⁻¹ := fun g => by
    simp [Frame.star, Frame.conj, MulAut.conjNormal_apply, mul_assoc]
  have hc : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right hF.c_sq
  refine ⟨fun g => ?_, fun g h => ?_, fun g => ?_, ?_, fun {n} {K} _ ρ g i j => ?_⟩
  · apply Subtype.ext
    rw [hs, hs, hc]
    simp only [_root_.mul_inv_rev, inv_inv, hc]
    calc F.c * (F.c * ((g : F.Γ) * F.c)) * F.c = (F.c * F.c) * (g : F.Γ) * (F.c * F.c) := by group
      _ = g := by rw [hF.c_sq]; group
  · apply Subtype.ext
    simp only [Subgroup.coe_mul, hs, _root_.mul_inv_rev, hc]
    calc F.c * ((h : F.Γ)⁻¹ * (g : F.Γ)⁻¹) * F.c
        = F.c * (h : F.Γ)⁻¹ * (F.c * F.c) * (g : F.Γ)⁻¹ * F.c := by rw [hF.c_sq]; group
      _ = F.c * (h : F.Γ)⁻¹ * F.c * (F.c * (g : F.Γ)⁻¹ * F.c) := by group
  · rw [hs, map_mul, map_mul, map_inv, map_inv, hF.Ψ_c]
    simp
  · refine continuous_induced_rng.2 ?_
    have : (fun g : F.G0 => ((F.star g : F.G0) : F.Γ)) = fun g : F.G0 => F.c * (g : F.Γ)⁻¹ * F.c⁻¹ := funext hs
    change Continuous (fun g : F.G0 => ((F.star g : F.G0) : F.Γ))
    rw [this]
    exact (continuous_const.mul continuous_subtype_val.inv).mul continuous_const
  · rw [ρ.pol]
    simp only [Matrix.mul_apply, Jmat, Matrix.transpose_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, one_mul]
    have h : ∀ a : Fin n, (j = a.rev) ↔ (a = j.rev) := fun a => by
      constructor <;> rintro rfl <;> simp
    simp [h]
