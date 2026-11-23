import Mathlib
import GroundTheory.GlobalFields.WeilGroups.QuasiCharacter

open NumberField

namespace GroundTheory.Global

noncomputable section

namespace QuasiCharacter

variable {K : Type*} [Field K] [NumberField K]

def toUnitary (ψ : QuasiCharacter K) (h : ∀ c, ‖((ψ c : ℂˣ) : ℂ)‖ = 1) : HeckeCharacter K where
  toFun c := ⟨((ψ c : ℂˣ) : ℂ), mem_sphere_zero_iff_norm.2 (h c)⟩
  map_one' := Circle.ext (by simp)
  map_mul' c d := Circle.ext (by simp only [map_mul, Units.val_mul]; rfl)
  continuous_toFun := (Units.continuous_val.comp ψ.continuous).subtype_mk _

theorem ofUnitary_toUnitary (ψ : QuasiCharacter K) (h : ∀ c, ‖((ψ c : ℂˣ) : ℂ)‖ = 1) :
    ofUnitary (toUnitary ψ h) = ψ := by
  ext c
  rfl

theorem mul_modulePow_zero (ψ : QuasiCharacter K) : ψ * modulePow (0 : ℂ) = ψ := by
  ext c
  simp

theorem ofUnitary_one_mul (ψ : QuasiCharacter K) : ofUnitary 1 * ψ = ψ := by
  ext c
  simp

theorem norm_ofUnitary_mul_modulePow (χ : HeckeCharacter K) (σ : ℝ) (c : IdeleClassGroup K) :
    ‖(((ofUnitary χ * modulePow (σ : ℂ) : QuasiCharacter K) c : ℂˣ) : ℂ)‖ =
      (IdeleClassGroup.ideleModule K c : ℝ) ^ σ := by
  rw [ContinuousMonoidHom.mul_apply, Units.val_mul, norm_mul, norm_ofUnitary, one_mul,
    norm_modulePow_ofReal]

theorem exists_ofUnitary_mul_modulePow (ψ : QuasiCharacter K) :
    ∃ (χ : HeckeCharacter K) (σ : ℝ), ofUnitary χ * modulePow (σ : ℂ) = ψ := by
  obtain ⟨σ, hσ⟩ := ψ.exists_norm_eq_rpow
  have h : ∀ c, ‖(((ψ * modulePow (-(σ : ℂ)) : QuasiCharacter K) c : ℂˣ) : ℂ)‖ = 1 := by
    intro c
    rw [ContinuousMonoidHom.mul_apply, Units.val_mul, norm_mul, hσ, ← Complex.ofReal_neg,
      norm_modulePow_ofReal, ← Real.rpow_add (IdeleClassGroup.ideleModule K c).2, add_neg_cancel,
      Real.rpow_zero]
  refine ⟨toUnitary _ h, σ, ?_⟩
  rw [ofUnitary_toUnitary, mul_assoc, ← modulePow_add, neg_add_cancel, mul_modulePow_zero]

theorem eq_of_ofUnitary_mul_modulePow_eq {χ χ' : HeckeCharacter K} {σ σ' : ℝ}
    (h : ofUnitary χ * modulePow (σ : ℂ) = ofUnitary χ' * modulePow (σ' : ℂ)) :
    χ = χ' ∧ σ = σ' := by
  obtain ⟨c, hc⟩ := IdeleClassGroup.ideleModule_surjective K ⟨Real.exp 1, Real.exp_pos 1⟩
  have hn := congrArg (fun ψ : QuasiCharacter K ↦ ‖((ψ c : ℂˣ) : ℂ)‖) h
  simp only [norm_ofUnitary_mul_modulePow, hc] at hn
  rw [Real.exp_one_rpow, Real.exp_one_rpow] at hn
  have hσ : σ = σ' := Real.exp_injective hn
  subst hσ
  refine ⟨ofUnitary_injective (ContinuousMonoidHom.ext fun c ↦ Units.ext ?_), rfl⟩
  have hc := congrArg (fun ψ : QuasiCharacter K ↦ ((ψ c : ℂˣ) : ℂ)) h
  simp only [ContinuousMonoidHom.mul_apply, Units.val_mul] at hc
  exact mul_right_cancel₀ (modulePow (σ : ℂ) c).ne_zero hc

def ofUnitaryMulModulePow : HeckeCharacter K × Multiplicative ℝ →* QuasiCharacter K where
  toFun p := ofUnitary p.1 * modulePow ((p.2.toAdd : ℝ) : ℂ)
  map_one' := by
    simp only [Prod.fst_one, Prod.snd_one, toAdd_one, Complex.ofReal_zero, mul_modulePow_zero, map_one]
  map_mul' p q := by
    simp only [Prod.fst_mul, Prod.snd_mul, toAdd_mul, map_mul, Complex.ofReal_add, modulePow_add]
    exact mul_mul_mul_comm (ofUnitary p.1) (ofUnitary q.1) _ _

theorem ofUnitaryMulModulePow_bijective :
    Function.Bijective (ofUnitaryMulModulePow (K := K)) := by
  refine ⟨fun p q h ↦ ?_, fun ψ ↦ ?_⟩
  · obtain ⟨h1, h2⟩ := eq_of_ofUnitary_mul_modulePow_eq h
    exact Prod.ext h1 (Multiplicative.toAdd.injective h2)
  · obtain ⟨χ, σ, h⟩ := ψ.exists_ofUnitary_mul_modulePow
    exact ⟨(χ, Multiplicative.ofAdd σ), h⟩

variable (K) in

def unitaryDecomposition : QuasiCharacter K ≃* HeckeCharacter K × Multiplicative ℝ :=
  (MulEquiv.ofBijective _ ofUnitaryMulModulePow_bijective).symm

variable (ψ : QuasiCharacter K)

def unitaryPart : HeckeCharacter K := (unitaryDecomposition K ψ).1

def exponent : ℝ := (unitaryDecomposition K ψ).2.toAdd

theorem ofUnitary_unitaryPart_mul_modulePow_exponent :
    ofUnitary ψ.unitaryPart * modulePow (ψ.exponent : ℂ) = ψ :=
  MulEquiv.ofBijective_apply_symm_apply (n := ψ) ofUnitaryMulModulePow ofUnitaryMulModulePow_bijective

theorem norm_apply (c : IdeleClassGroup K) :
    ‖((ψ c : ℂˣ) : ℂ)‖ = (IdeleClassGroup.ideleModule K c : ℝ) ^ ψ.exponent := by
  conv_lhs => rw [← ψ.ofUnitary_unitaryPart_mul_modulePow_exponent]
  exact norm_ofUnitary_mul_modulePow _ _ _

@[simp]
theorem unitaryPart_ofUnitary_mul_modulePow (χ : HeckeCharacter K) (σ : ℝ) :
    (ofUnitary χ * modulePow (σ : ℂ)).unitaryPart = χ :=
  (eq_of_ofUnitary_mul_modulePow_eq
    (ofUnitary_unitaryPart_mul_modulePow_exponent (ofUnitary χ * modulePow (σ : ℂ)))).1

@[simp]
theorem exponent_ofUnitary_mul_modulePow (χ : HeckeCharacter K) (σ : ℝ) :
    (ofUnitary χ * modulePow (σ : ℂ)).exponent = σ :=
  (eq_of_ofUnitary_mul_modulePow_eq
    (ofUnitary_unitaryPart_mul_modulePow_exponent (ofUnitary χ * modulePow (σ : ℂ)))).2

@[simp]
theorem unitaryPart_ofUnitary (χ : HeckeCharacter K) : (ofUnitary χ).unitaryPart = χ := by
  have h := unitaryPart_ofUnitary_mul_modulePow χ 0
  rwa [Complex.ofReal_zero, mul_modulePow_zero] at h

@[simp]
theorem exponent_ofUnitary (χ : HeckeCharacter K) : (ofUnitary χ).exponent = 0 := by
  have h := exponent_ofUnitary_mul_modulePow χ 0
  rwa [Complex.ofReal_zero, mul_modulePow_zero] at h

@[simp]
theorem exponent_modulePow (σ : ℝ) : (modulePow (σ : ℂ) : QuasiCharacter K).exponent = σ := by
  have h := exponent_ofUnitary_mul_modulePow (1 : HeckeCharacter K) σ
  rwa [ofUnitary_one_mul] at h

end QuasiCharacter

end

end GroundTheory.Global
