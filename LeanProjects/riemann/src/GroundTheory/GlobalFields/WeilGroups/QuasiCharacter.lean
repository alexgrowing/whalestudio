import Mathlib
import GroundTheory.GlobalFields.TateThesis.HeckeChar
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
import GroundTheory.GlobalFields.IdeleGroups.NormOneCompact
import GroundTheory.GlobalFields.TateThesis.IdeleMeasureNormOne

open Topology NumberField
open scoped NumberField.AdeleRing

namespace GroundTheory.Global

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

abbrev QuasiCharacter : Type _ := IdeleClassGroup K →ₜ* ℂˣ

namespace QuasiCharacter

variable {K}

def circleToUnits : Circle →ₜ* ℂˣ where
  toMonoidHom := Circle.toUnits
  continuous_toFun := Units.continuous_iff.2 ⟨continuous_subtype_val, by
    refine (continuous_subtype_val.inv₀ fun z : Circle ↦ z.coe_ne_zero).congr fun z ↦ ?_
    change ((z : ℂ))⁻¹ = ((Circle.toUnits z)⁻¹ : ℂˣ).val
    rw [Units.val_inv_eq_inv_val]
    rfl⟩

@[simp]
theorem coe_circleToUnits (z : Circle) : ((circleToUnits z : ℂˣ) : ℂ) = z :=
  rfl

def ofUnitary : HeckeCharacter K →* QuasiCharacter K where
  toFun χ := circleToUnits.comp χ
  map_one' := by
    ext c
    simp
  map_mul' χ χ' := by
    ext c
    simp

@[simp]
theorem ofUnitary_apply (χ : HeckeCharacter K) (c : IdeleClassGroup K) :
    ((ofUnitary χ c : ℂˣ) : ℂ) = χ c :=
  rfl

theorem ofUnitary_injective : Function.Injective (ofUnitary (K := K)) := by
  intro χ χ' h
  ext c
  have := congrArg (fun ψ : QuasiCharacter K ↦ ((ψ c : ℂˣ) : ℂ)) h
  simpa using this

theorem norm_ofUnitary (χ : HeckeCharacter K) (c : IdeleClassGroup K) :
    ‖((ofUnitary χ c : ℂˣ) : ℂ)‖ = 1 := by
  rw [ofUnitary_apply, Circle.norm_coe]

theorem continuous_units_mk0 {X : Type*} [TopologicalSpace X] {f : X → ℂ} (hf : Continuous f)
    (h : ∀ x, f x ≠ 0) : Continuous fun x ↦ Units.mk0 (f x) (h x) := by
  refine Units.continuous_iff.2 ⟨hf, ?_⟩
  have e : (fun x ↦ ((Units.mk0 (f x) (h x))⁻¹ : ℂˣ).val) = fun x ↦ (f x)⁻¹ := by
    funext x
    rw [Units.val_inv_eq_inv_val, Units.val_mk0]
  rw [e]
  exact hf.inv₀ h

theorem continuous_ideleModule_val :
    Continuous fun c : IdeleClassGroup K ↦ (IdeleClassGroup.ideleModule K c : ℝ) :=
  continuous_subtype_val.comp (IdeleClassGroup.continuous_ideleModule K)

def modulePow (s : ℂ) : QuasiCharacter K where
  toFun c := Units.mk0 (Complex.exp (s * Real.log (IdeleClassGroup.ideleModule K c : ℝ)))
    (Complex.exp_ne_zero _)
  map_one' := by
    ext
    simp
  map_mul' c d := by
    ext
    simp only [map_mul, Positive.val_mul, Units.val_mk0, Units.val_mul]
    rw [Real.log_mul (IdeleClassGroup.ideleModule K c).2.ne' (IdeleClassGroup.ideleModule K d).2.ne',
      Complex.ofReal_add, mul_add, Complex.exp_add]
  continuous_toFun := continuous_units_mk0
    (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      (continuous_ideleModule_val.log fun c ↦ (IdeleClassGroup.ideleModule K c).2.ne'))))
    fun _ ↦ Complex.exp_ne_zero _

theorem modulePow_apply (s : ℂ) (c : IdeleClassGroup K) :
    ((modulePow s c : ℂˣ) : ℂ) = Complex.exp (s * Real.log (IdeleClassGroup.ideleModule K c : ℝ)) :=
  rfl

@[simp]
theorem modulePow_zero : modulePow (0 : ℂ) = (1 : QuasiCharacter K) := by
  ext c
  simp [modulePow_apply]

theorem modulePow_add (s t : ℂ) :
    modulePow (s + t) = (modulePow s * modulePow t : QuasiCharacter K) := by
  ext c
  simp only [modulePow_apply, ContinuousMonoidHom.mul_apply, Units.val_mul, add_mul, Complex.exp_add]

theorem norm_modulePow_ofReal (σ : ℝ) (c : IdeleClassGroup K) :
    ‖((modulePow (σ : ℂ) c : ℂˣ) : ℂ)‖ = (IdeleClassGroup.ideleModule K c : ℝ) ^ σ := by
  rw [modulePow_apply, ← Complex.ofReal_mul, Complex.norm_exp_ofReal,
    Real.rpow_def_of_pos (IdeleClassGroup.ideleModule K c).2, mul_comm]

variable (ψ : QuasiCharacter K)

theorem norm_apply_pos (c : IdeleClassGroup K) : 0 < ‖((ψ c : ℂˣ) : ℂ)‖ :=
  norm_pos_iff.2 (ψ c).ne_zero

theorem norm_apply_inv (c : IdeleClassGroup K) :
    ‖((ψ c⁻¹ : ℂˣ) : ℂ)‖ = ‖((ψ c : ℂˣ) : ℂ)‖⁻¹ := by
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv]

theorem norm_eq_one_of_mem_normOneSubgroup {c : IdeleClassGroup K}
    (hc : c ∈ IdeleClassGroup.normOneSubgroup K) : ‖((ψ c : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨C, hC⟩ := (IdeleClassGroup.isCompact_normOneSubgroup K).exists_bound_of_continuousOn
    (f := fun c ↦ ((ψ c : ℂˣ) : ℂ)) (Units.continuous_val.comp ψ.continuous).continuousOn
  have hle : ∀ d ∈ IdeleClassGroup.normOneSubgroup K, ‖((ψ d : ℂˣ) : ℂ)‖ ≤ 1 := by
    intro d hd
    by_contra h
    push Not at h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C h
    have hb := hC (d ^ n) (pow_mem hd n)
    rw [map_pow, Units.val_pow_eq_pow_val, norm_pow] at hb
    exact (not_le.2 hn) hb
  have h1 := hle c hc
  have h2 := hle c⁻¹ (inv_mem hc)
  rw [norm_apply_inv] at h2
  have hpos := ψ.norm_apply_pos c
  exact le_antisymm h1 (by rwa [inv_le_one₀ hpos] at h2)

theorem exists_norm_eq_rpow :
    ∃ σ : ℝ, ∀ c, ‖((ψ c : ℂˣ) : ℂ)‖ = (IdeleClassGroup.ideleModule K c : ℝ) ^ σ := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
  let sec : {r : ℝ // 0 < r} →* IdeleClassGroup K := (IdeleClassGroup.mk K).comp (moduleSection w)
  have hsec : ∀ t, IdeleClassGroup.ideleModule K (sec t) = t := fun t ↦ by
    simp [sec, IdeleClassGroup.ideleModule_mk]
  have hcont : Continuous fun x : ℝ ↦ ‖((ψ (sec (expPos x)) : ℂˣ) : ℂ)‖ :=
    continuous_norm.comp (Units.continuous_val.comp (ψ.continuous.comp
      ((IdeleClassGroup.continuous_mk K).comp ((continuous_moduleSection w).comp
        expPosHomeomorph.continuous))))
  let f : ℝ →+ ℝ :=
    { toFun := fun x ↦ Real.log ‖((ψ (sec (expPos x)) : ℂˣ) : ℂ)‖
      map_zero' := by
        have h0 : expPos 0 = 1 := Subtype.ext Real.exp_zero
        simp [h0]
      map_add' := fun x y ↦ by
        simp only [expPos_add, map_mul, Units.val_mul, norm_mul]
        exact Real.log_mul (ψ.norm_apply_pos _).ne' (ψ.norm_apply_pos _).ne' }
  have hf : Continuous f := hcont.log fun x ↦ (ψ.norm_apply_pos _).ne'
  refine ⟨f 1, fun c ↦ ?_⟩
  set t := IdeleClassGroup.ideleModule K c with ht
  have hd : c * (sec t)⁻¹ ∈ IdeleClassGroup.normOneSubgroup K := by
    rw [IdeleClassGroup.normOneSubgroup, MonoidHom.mem_ker, map_mul, map_inv, hsec, ← ht,
      mul_inv_cancel]
  have hc : c = c * (sec t)⁻¹ * sec t := by rw [inv_mul_cancel_right]
  have ht' : t = expPos (Real.log t) := Subtype.ext (Real.exp_log t.2).symm
  have hlin : f (Real.log t) = Real.log t * f 1 := by
    simpa using map_real_smul f hf (Real.log t) 1
  have hval : ‖((ψ (sec t) : ℂˣ) : ℂ)‖ = Real.exp (f (Real.log t)) := by
    change _ = Real.exp (Real.log ‖((ψ (sec (expPos (Real.log t))) : ℂˣ) : ℂ)‖)
    rw [Real.exp_log (ψ.norm_apply_pos _), ← ht']
  rw [hc, map_mul, Units.val_mul, norm_mul, ψ.norm_eq_one_of_mem_normOneSubgroup hd, one_mul, hval,
    hlin, Real.rpow_def_of_pos t.2]

end QuasiCharacter

end

end GroundTheory.Global
