import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {F : Type*} [Field F] [NumberField F]

noncomputable def ordAt (v : HeightOneSpectrum (𝓞 F)) (x : Fˣ) : ℤ :=
  -Multiplicative.toAdd (v.valuationOfNeZero x)

theorem ordAt_mul (v : HeightOneSpectrum (𝓞 F)) (x y : Fˣ) :
    ordAt v (x * y) = ordAt v x + ordAt v y := by
  simp only [ordAt, map_mul, toAdd_mul, neg_add]

theorem ordAt_one (v : HeightOneSpectrum (𝓞 F)) : ordAt v (1 : Fˣ) = 0 := by
  simp [ordAt]

theorem ordAt_inv (v : HeightOneSpectrum (𝓞 F)) (x : Fˣ) : ordAt v x⁻¹ = -ordAt v x := by
  simp [ordAt]

theorem ordAt_eq_zero_iff (v : HeightOneSpectrum (𝓞 F)) (x : Fˣ) :
    ordAt v x = 0 ↔ v.valuation F (x : F) = 1 := by
  rw [ordAt, neg_eq_zero, ← valuationOfNeZero_eq, ← WithZero.coe_one, WithZero.coe_inj,
    ← toAdd_one]
  exact Multiplicative.toAdd.injective.eq_iff

theorem valuation_eq_exp_neg_ordAt (v : HeightOneSpectrum (𝓞 F)) (x : Fˣ) :
    v.valuation F (x : F) = WithZero.exp (-ordAt v x) := by
  rw [ordAt, neg_neg, ← valuationOfNeZero_eq]
  rfl

theorem finite_ordAt_ne_zero (x : Fˣ) : {v : HeightOneSpectrum (𝓞 F) | ordAt v x ≠ 0}.Finite := by
  refine ((Support.finite (𝓞 F) (x : F)).union (Support.finite (𝓞 F) ((x⁻¹ : Fˣ) : F))).subset ?_
  intro v hv
  have hv' : v.valuation F (x : F) ≠ 1 := fun h => hv ((ordAt_eq_zero_iff v x).2 h)
  rcases lt_or_gt_of_ne hv' with h | h
  · right
    change 1 < v.valuation F ((x⁻¹ : Fˣ) : F)
    rw [Units.val_inv_eq_inv_val, map_inv₀]
    exact one_lt_inv₀ (lt_of_le_of_ne zero_le (((map_ne_zero (v.valuation F)).2 x.ne_zero)).symm)
      |>.2 h
  · left
    exact h

variable (S : Set (HeightOneSpectrum (𝓞 F)))

abbrev sDivisor := {v : HeightOneSpectrum (𝓞 F) // v ∉ S} →₀ ℤ

noncomputable def divS : Additive Fˣ →+ sDivisor S where
  toFun x := Finsupp.ofSupportFinite (fun v => ordAt v.1 (Additive.toMul x)) (by
    refine ((finite_ordAt_ne_zero (Additive.toMul x)).preimage
      Subtype.val_injective.injOn).subset ?_
    intro v hv
    exact hv)
  map_zero' := by
    ext v
    simp [Finsupp.ofSupportFinite_coe, ordAt_one]
  map_add' x y := by
    ext v
    simp [Finsupp.ofSupportFinite_coe, toMul_add, ordAt_mul]

theorem divS_apply (x : Additive Fˣ) (v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}) :
    divS S x v = ordAt v.1 (Additive.toMul x) :=
  rfl

abbrev sPic := sDivisor S ⧸ (divS S).range

noncomputable abbrev sPicMk : sDivisor S →+ sPic S := QuotientAddGroup.mk' (divS S).range

theorem sPicMk_eq_zero_iff (D : sDivisor S) : sPicMk S D = 0 ↔ ∃ x : Fˣ, divS S (Additive.ofMul x) = D := by
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddMonoidHom.mem_range]
  exact ⟨fun ⟨x, hx⟩ => ⟨Additive.toMul x, hx⟩, fun ⟨x, hx⟩ => ⟨Additive.ofMul x, hx⟩⟩

end GroundTheory.ProfCoh
