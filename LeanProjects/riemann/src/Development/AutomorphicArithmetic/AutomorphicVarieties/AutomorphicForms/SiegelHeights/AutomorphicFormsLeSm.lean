import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.CoeSmEqSymm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.MemArchMaxCompactIffOrthogonalAtInfinitePlaces
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdelicHeightInfGLLeOpNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ConstantTermEqZeroOfIsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsCuspidalOfConstantTermEqZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsKFiniteTotallyRealModelOfIsKFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ModerateGrowthTotallyRealModelOfModerateGrowth

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace UpperTheory.V.Fb

variable (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (a : ℕ)

omit [NumberField E] [IsTotallyReal E] in
private theorem toUnits_mk (y : GL (Fin a) (TR.Rinf E)) (h : y.val ∈ Matrix.unitaryGroup (Fin a) (TR.Rinf E)) :
    Unitary.toUnits (⟨y.val, h⟩ : TR.Kinf E a) = y := Units.ext rfl

def cptEq : TR.Kinf E a ≃* archCompact E a where
  toFun k := ⟨grpEq E a (Unitary.toUnits k), (UpperTheory.mem_archMaxCompact_iff_orthogonal_at_infinitePlaces E a _).2 k.2⟩
  invFun k := ⟨((grpEq E a).symm k.1).val, (UpperTheory.mem_archMaxCompact_iff_orthogonal_at_infinitePlaces E a _).1 (by rw [MulEquiv.apply_symm_apply]; exact k.2)⟩
  left_inv k := Subtype.ext (congrArg Units.val ((grpEq E a).symm_apply_apply (Unitary.toUnits k)))
  right_inv k := Subtype.ext ((grpEq E a).eq_symm_apply.1 (toUnits_mk E a _ _))
  map_mul' k l := Subtype.ext (by
    change grpEq E a (Unitary.toUnits (k * l)) = grpEq E a _ * grpEq E a _
    rw [map_mul, map_mul])

variable {E a}

theorem coe_cptEq (k : TR.Kinf E a) : (cptEq E a k : archGroup E a) = grpEq E a (Unitary.toUnits k) := rfl

theorem infEmb_cptEq (k : TR.Kinf E a) : infEmb E a (cptEq E a k) = TR.infGL E a (Unitary.toUnits k) := by
  rw [coe_cptEq, infEmb_grpEq]

theorem kfin_of {φ : TR.Sm E a} (h : IsKFinite φ.1) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => TR.cptRep E a k φ)) := by
  unfold IsKFinite at h
  have hle : (Submodule.span ℂ (Set.range fun k => TR.cptRep E a k φ)).map (TR.Sm E a).subtype ≤ _ :=
    (Submodule.map_span _ _).le.trans (Submodule.span_mono (t := Set.range
      fun k : (Reduction.maxCompact : Subgroup (GA E a)) => rightTranslate (k : GA E a) φ.1) (by
        rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
        exact ⟨⟨infEmb E a (cptEq E a k), (cptEq E a k).2⟩, congrArg (rightTranslate · φ.1) (infEmb_cptEq k)⟩))
  have := Submodule.finiteDimensional_of_le hle
  exact Module.Finite.equiv (Submodule.equivMapOfInjective _ (TR.Sm E a).injective_subtype _).symm

theorem level_of {φ : TR.Sm E a} (hs : IsSmooth φ.1) (h : IsKFinite φ.1) : IsOpen {k | TR.finRep E a k φ = φ} := by
  obtain ⟨U, -, hU⟩ := exists_openSubgroup_rightInvariant hs h
  let S : Subgroup (GL (Fin a) (Af E)) :=
    { carrier := {k | TR.finRep E a k φ = φ}
      one_mem' := by simp
      mul_mem' := fun {k l} hk hl => by
        change TR.finRep E a (k * l) φ = φ
        rw [map_mul, Module.End.mul_apply, hl, hk]
      inv_mem' := fun {k} hk => by
        change TR.finRep E a k⁻¹ φ = φ
        conv_lhs => rw [← show TR.finRep E a k φ = φ from hk, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl }
  refine Subgroup.isOpen_mono (H₁ := U.toSubgroup) (H₂ := S) (fun u hu => Subtype.ext (funext fun g => ?_)) U.isOpen
  exact (congrArg (fun f : GL (Fin a) (Af E) →* GA E a => φ.1 (g * f u)) finEmb_eq).symm.trans (hU g u hu)

theorem isSmooth_of_level {φ : TR.Sm E a} (h : IsOpen {k | TR.finRep E a k φ = φ}) : IsSmooth φ.1 := by
  refine ⟨(smEq E a φ).2, fun g => ?_⟩
  filter_upwards [h.mem_nhds (show TR.finRep E a 1 φ = φ by simp)] with k hk
  rw [finEmb_eq]
  exact congrFun (congrArg Subtype.val hk) g

theorem growth_of {φ : GA E a → ℂ} (h : HasModerateGrowth φ) (g : GA E a) :
    ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ (g * TR.infGL E a y)‖ ≤ C * TR.height y ^ N := by
  obtain ⟨C, N, h⟩ := h
  obtain ⟨M, hM⟩ := UpperTheory.adelicHeight_infGL_le_opNorm E a
  refine ⟨|C| * (heightConst E a * AutomorphicForm.height g) ^ N, M * N, fun y => (h _).trans ?_⟩
  have h0 : 0 ≤ heightConst E a * AutomorphicForm.height g :=
    mul_nonneg (zero_le_one.trans one_le_heightConst) (height_pos g).le
  rw [mul_assoc, pow_mul, ← mul_pow]
  exact mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (height_pos _).le
    ((height_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hM y) h0)) N) (pow_nonneg (height_pos _).le N) (abs_nonneg C)

theorem isAutForm_iff (φ : TR.Sm E a) : TR.IsAutForm φ ↔ IsAutomorphicForm φ.1 :=
  ⟨fun h => ⟨h.left, isSmooth_of_level h.level, UpperTheory.isKFinite_totallyRealModel_of_isKFinite E a φ h.level h.kfin, (zfin_iff φ).1 h.zfin,
      UpperTheory.moderateGrowth_totallyRealModel_of_moderateGrowth E a φ h.left h.level h.growth⟩,
    fun h => ⟨h.isLeftInvariant, level_of h.isSmooth h.isKFinite, kfin_of h.isKFinite, (zfin_iff φ).2 h.isZFinite,
      growth_of h.hasModerateGrowth⟩⟩

theorem isCuspForm_iff (φ : TR.Sm E a) : TR.IsCuspForm φ ↔ φ.1 ∈ cuspForms E a := by
  rw [TR.IsCuspForm, isAutForm_iff, mem_cuspForms]
  exact and_congr_right fun h => ⟨UpperTheory.constantTerm_eq_zero_of_isCuspidal E a _ h.isLeftInvariant h.continuous,
    UpperTheory.isCuspidal_of_constantTerm_eq_zero E a _ h.isLeftInvariant h.continuous⟩

theorem cuspForms_le_Sm : cuspForms E a ≤ TR.Sm E a := fun _ h => (sm_eq E a).ge h.1.isSmooth.1

theorem automorphicForms_le_Sm : automorphicForms E a ≤ TR.Sm E a := fun _ h => (sm_eq E a).ge h.isSmooth.1

end UpperTheory.V.Fb
