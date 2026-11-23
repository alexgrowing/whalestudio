import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ResidualSpectrumByClass
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.Published

noncomputable section

namespace GlobalTheory.UnitaryTwist

def normRpow (r : ℝ) : ℂˣ →* ℂˣ where
  toFun z := Units.mk0 ((‖(z : ℂ)‖ ^ r : ℝ) : ℂ)
    (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (norm_pos_iff.2 z.ne_zero) r).ne')
  map_one' := by ext; simp
  map_mul' z w := by
    ext
    simp [Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]

theorem normRpow_val (r : ℝ) (z : ℂˣ) : ((normRpow r z : ℂˣ) : ℂ) = ((‖(z : ℂ)‖ ^ r : ℝ) : ℂ) := rfl

theorem continuous_normRpow (r : ℝ) : Continuous (normRpow r) := by
  have hn : Continuous fun z : ℂˣ => ‖(z : ℂ)‖ := Units.continuous_val.norm
  have hp : Continuous fun z : ℂˣ => ‖(z : ℂ)‖ ^ r :=
    hn.rpow_const fun z => Or.inl (norm_pos_iff.2 z.ne_zero).ne'
  have hc : Continuous fun z : ℂˣ => ((‖(z : ℂ)‖ ^ r : ℝ) : ℂ) := Complex.continuous_ofReal.comp hp
  refine Units.continuous_iff.2 ⟨hc, ?_⟩
  have : (fun z : ℂˣ => (((normRpow r z)⁻¹ : ℂˣ) : ℂ)) = fun z : ℂˣ => (((‖(z : ℂ)‖ ^ r : ℝ) : ℂ))⁻¹ := by
    funext z; rw [Units.val_inv_eq_inv_val, normRpow_val]
  rw [this]
  exact hc.inv₀ fun z => Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (norm_pos_iff.2 z.ne_zero) r).ne'

def normTwist {E : Type} [Field E] [NumberField E] (ω : HChar E) (r : ℝ) : HChar E :=
  ⟨(normRpow r).comp ω.1, (continuous_normRpow r).comp ω.2.1, fun k => by
    rw [MonoidHom.comp_apply, ω.2.2 k, map_one]⟩

theorem exists_pow_mul_isUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (ω : HChar E) (a : ℕ),
    1 ≤ a → ∃ ν : HChar E, (ω * ν ^ a).IsUnitary := by
  intro E _ _ _ ω a ha
  refine ⟨normTwist ω (-(1 / (a : ℝ))), fun x => ?_⟩
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 ha)
  have ht : 0 < ‖((ω.1 x : ℂˣ) : ℂ)‖ := norm_pos_iff.2 (ω.1 x).ne_zero
  set t : ℝ := ‖((ω.1 x : ℂˣ) : ℂ)‖ with htdef
  have hv : (((normTwist ω (-(1 / (a : ℝ)))).1 x : ℂˣ) : ℂ) = ((t ^ (-(1 / (a : ℝ))) : ℝ) : ℂ) := rfl
  have hm : (((ω * normTwist ω (-(1 / (a : ℝ))) ^ a).1 x : ℂˣ) : ℂ) =
      ((ω.1 x : ℂˣ) : ℂ) * (((normTwist ω (-(1 / (a : ℝ)))).1 x : ℂˣ) : ℂ) ^ a := by
    rw [Subgroup.coe_mul, Subgroup.coe_pow, MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul,
      Units.val_pow_eq_pow_val]
  show ‖(((ω * normTwist ω (-(1 / (a : ℝ))) ^ a).1 x : ℂˣ) : ℂ)‖ = 1
  rw [hm, hv, norm_mul, norm_pow, ← htdef, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos ht _), ← Real.rpow_natCast,
    ← Real.rpow_mul ht.le, show -(1 / (a : ℝ)) * (a : ℝ) = -1 by field_simp, Real.rpow_neg_one,
    mul_inv_cancel₀ ht.ne']

end GlobalTheory.UnitaryTwist
