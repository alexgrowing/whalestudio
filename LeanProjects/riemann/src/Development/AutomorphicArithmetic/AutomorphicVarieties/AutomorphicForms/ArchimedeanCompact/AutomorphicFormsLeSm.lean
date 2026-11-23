import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.OneTmulMemCenter
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelSetInterTranslateFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ConstantTermEqZeroOfIsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsCuspidalOfConstantTermEqZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelSetHeightBound

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace UpperTheory.V.Cm

variable (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)

omit [NumberField E] [IsTotallyComplex E] in
private theorem toUnits_mk (y : GL (Fin a) (Cinf E)) (h : y.val ∈ Matrix.unitaryGroup (Fin a) (Cinf E)) :
    Unitary.toUnits (⟨y.val, h⟩ : Kinf E a) = y := Units.ext rfl

def cptEq : Kinf E a ≃* archCompact E a where
  toFun k := ⟨grpEq E a (Unitary.toUnits k), (grpEq_mem_archCompact _).2 k.2⟩
  invFun k := ⟨((grpEq E a).symm k.1).val, (grpEq_mem_archCompact _).1 (by rw [MulEquiv.apply_symm_apply]; exact k.2)⟩
  left_inv k := Subtype.ext (congrArg Units.val ((grpEq E a).symm_apply_apply (Unitary.toUnits k)))
  right_inv k := Subtype.ext ((grpEq E a).eq_symm_apply.1 (toUnits_mk E a _ _))
  map_mul' k l := Subtype.ext (by
    change grpEq E a (Unitary.toUnits (k * l)) = grpEq E a _ * grpEq E a _
    rw [map_mul, map_mul])

variable {E a}

theorem coe_cptEq (k : Kinf E a) : (cptEq E a k : archGroup E a) = grpEq E a (Unitary.toUnits k) := rfl

theorem infEmb_cptEq (k : Kinf E a) : infEmb E a (cptEq E a k) = infGL E a (Unitary.toUnits k) := by
  rw [coe_cptEq, infEmb_grpEq]

theorem kfin_of {φ : Sm E a} (h : IsKFinite φ.1) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)) := by
  unfold IsKFinite at h
  have hle : (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)).map (Sm E a).subtype ≤ _ :=
    (Submodule.map_span _ _).le.trans (Submodule.span_mono (t := Set.range
      fun k : (Reduction.maxCompact : Subgroup (GA E a)) => rightTranslate (k : GA E a) φ.1) (by
        rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
        exact ⟨⟨infEmb E a (cptEq E a k), (cptEq E a k).2⟩, congrArg (rightTranslate · φ.1) (infEmb_cptEq k)⟩))
  have := Submodule.finiteDimensional_of_le hle
  exact Module.Finite.equiv (Submodule.equivMapOfInjective _ (Sm E a).injective_subtype _).symm

theorem level_of {φ : Sm E a} (hs : IsSmooth φ.1) (h : IsKFinite φ.1) : IsOpen {k | GlobalTheory.CuspRep.finRep E a k φ = φ} := by
  obtain ⟨U, -, hU⟩ := exists_openSubgroup_rightInvariant hs h
  let S : Subgroup (GL (Fin a) (Af E)) :=
    { carrier := {k | GlobalTheory.CuspRep.finRep E a k φ = φ}
      one_mem' := by simp
      mul_mem' := fun {k l} hk hl => by
        change GlobalTheory.CuspRep.finRep E a (k * l) φ = φ
        rw [map_mul, Module.End.mul_apply, hl, hk]
      inv_mem' := fun {k} hk => by
        change GlobalTheory.CuspRep.finRep E a k⁻¹ φ = φ
        conv_lhs => rw [← show GlobalTheory.CuspRep.finRep E a k φ = φ from hk, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl }
  refine Subgroup.isOpen_mono (H₁ := U.toSubgroup) (H₂ := S) (fun u hu => Subtype.ext (funext fun g => ?_)) U.isOpen
  exact (congrArg (fun f : GL (Fin a) (Af E) →* GA E a => φ.1 (g * f u)) Fb.finEmb_eq).symm.trans (hU g u hu)

theorem isSmooth_of_level {φ : Sm E a} (h : IsOpen {k | GlobalTheory.CuspRep.finRep E a k φ = φ}) : IsSmooth φ.1 := by
  refine ⟨(smEq E a φ).2, fun g => ?_⟩
  filter_upwards [h.mem_nhds (show GlobalTheory.CuspRep.finRep E a 1 φ = φ by simp)] with k hk
  rw [Fb.finEmb_eq]
  exact congrFun (congrArg Subtype.val hk) g

theorem growth_of {φ : GA E a → ℂ} (h : HasModerateGrowth φ) (g : GA E a) :
    ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ (g * infGL E a y)‖ ≤ C * GlobalTheory.CuspRep.height y ^ N := by
  obtain ⟨C, N, h⟩ := h
  obtain ⟨M, hM⟩ := exists_height_le E a
  refine ⟨|C| * (heightConst E a * AutomorphicForm.height g) ^ N, M * N, fun y => (h _).trans ?_⟩
  have h0 : 0 ≤ heightConst E a * AutomorphicForm.height g :=
    mul_nonneg (zero_le_one.trans one_le_heightConst) (height_pos g).le
  rw [mul_assoc, pow_mul, ← mul_pow]
  exact mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (height_pos _).le
    ((height_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hM y) h0)) N) (pow_nonneg (height_pos _).le N) (abs_nonneg C)

theorem isKFinite_of {φ : Sm E a} (hopen : IsOpen {k | GlobalTheory.CuspRep.finRep E a k φ = φ})
    (hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ))) : IsKFinite φ.1 := by
  let Kf := AdelicGLn.integralFiniteGL E a
  let V : Subgroup Kf :=
    { carrier := {v | GlobalTheory.CuspRep.finRep E a v.1 φ = φ}
      one_mem' := by
        show GlobalTheory.CuspRep.finRep E a 1 φ = φ
        rw [map_one]; rfl
      mul_mem' := fun {v w} hv hw => by
        have hv' : GlobalTheory.CuspRep.finRep E a v.1 φ = φ := hv
        have hw' : GlobalTheory.CuspRep.finRep E a w.1 φ = φ := hw
        show GlobalTheory.CuspRep.finRep E a (v.1 * w.1) φ = φ
        rw [map_mul, Module.End.mul_apply, hw', hv']
      inv_mem' := fun {v} hv => by
        have hv' : GlobalTheory.CuspRep.finRep E a v.1 φ = φ := hv
        show GlobalTheory.CuspRep.finRep E a (v.1⁻¹) φ = φ
        conv_lhs => rw [← hv']
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl }
  have hV : IsOpen (V : Set Kf) := hopen.preimage continuous_subtype_val
  haveI : CompactSpace Kf := isCompact_iff_compactSpace.1 (AdelicGLn.isCompact_integralFiniteGL E a)
  haveI : Finite (Kf ⧸ V) := Subgroup.quotient_finite_of_isOpen V hV
  unfold IsKFinite
  refine Submodule.finiteDimensional_of_le (S₂ := ⨆ q : Kf ⧸ V,
    ((Submodule.span ℂ (Set.range fun k => cptRep E a k φ)).map (GlobalTheory.CuspRep.finRep E a q.out.1)).map
      (Sm E a).subtype) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  let kf : Kf := ⟨finPart k.1, finPart_mem_integralFiniteGL k.2⟩
  obtain ⟨y, hy⟩ := (grpEq E a).surjective (archPart k.1)
  have hyu : y.val ∈ Matrix.unitaryGroup (Fin a) (Cinf E) :=
    (grpEq_mem_archCompact y).1 (hy ▸ archPart_mem_archCompact k.2)
  have hu : Unitary.toUnits (⟨y.val, hyu⟩ : Kinf E a) = y := Units.ext rfl
  obtain ⟨v, hv⟩ := QuotientGroup.mk_out_eq_mul V kf
  have hv2 : GlobalTheory.CuspRep.finRep E a v.1.1 φ = φ := v.2
  have hk : infGL E a y * finGL E a kf.1 = k.1 := by
    rw [← infEmb_grpEq, hy, ← Fb.finEmb_eq]
    exact infEmb_archPart_mul_finEmb_finPart k.1
  refine Submodule.mem_iSup_of_mem (QuotientGroup.mk kf)
    ⟨_, ⟨_, Submodule.subset_span ⟨⟨y.val, hyu⟩, rfl⟩, rfl⟩, ?_⟩
  rw [hv]
  funext g
  show φ.1 (g * finGL E a (kf.1 * v.1.1) * infGL E a (Unitary.toUnits (⟨y.val, hyu⟩ : Kinf E a))) = φ.1 (g * k.1)
  have h3 : φ.1 (g * k.1 * finGL E a v.1.1) = φ.1 (g * k.1) := congrFun (congrArg Subtype.val hv2) (g * k.1)
  rw [hu, ← h3, ← hk, mul_assoc g, ← infGL_comm, map_mul]
  simp only [mul_assoc]

private theorem unif (φ : Sm E a)
    (hU : IsOpen {k | GlobalTheory.CuspRep.finRep E a k φ = φ})
    (hg : ∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ.1 (g * infGL E a y)‖ ≤ C * GlobalTheory.CuspRep.height y ^ N)
    {Ω : Set (AdelicGLn.FiniteAdelicGL E a)} (hΩ : IsCompact Ω) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ l ∈ Ω, ∀ y, ‖φ.1 (finGL E a l * infGL E a y)‖ ≤ C * GlobalTheory.CuspRep.height y ^ N := by
  refine hΩ.induction_on (p := fun S => ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ l ∈ S, ∀ y,
    ‖φ.1 (finGL E a l * infGL E a y)‖ ≤ C * GlobalTheory.CuspRep.height y ^ N) ⟨0, 0, le_rfl, fun _ h => h.elim⟩ ?_ ?_ ?_
  · rintro S T hST ⟨C, N, h0, h⟩
    exact ⟨C, N, h0, fun l hl => h l (hST hl)⟩
  · rintro S T ⟨C, N, h0, h⟩ ⟨D, M, h1, h'⟩
    refine ⟨max C D, max N M, le_max_of_le_left h0, fun l hl y => ?_⟩
    have hy := GlobalTheory.CuspRep.one_le_height y
    rcases hl with hl | hl
    · exact (h l hl y).trans (mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ hy (le_max_left _ _))
        (pow_nonneg (zero_le_one.trans hy) _) (le_max_of_le_left h0))
    · exact (h' l hl y).trans (mul_le_mul (le_max_right _ _) (pow_le_pow_right₀ hy (le_max_right _ _))
        (pow_nonneg (zero_le_one.trans hy) _) (le_max_of_le_left h0))
  · intro k _
    obtain ⟨C, N, h⟩ := hg (finGL E a k)
    have ho : IsOpen ((fun l : AdelicGLn.FiniteAdelicGL E a => k⁻¹ * l) ⁻¹' {k | GlobalTheory.CuspRep.finRep E a k φ = φ}) :=
      hU.preimage (continuous_const.mul continuous_id)
    refine ⟨_, mem_nhdsWithin_of_mem_nhds (ho.mem_nhds ?_), |C|, N, abs_nonneg C, fun l hl y => ?_⟩
    · change GlobalTheory.CuspRep.finRep E a (k⁻¹ * k) φ = φ
      rw [inv_mul_cancel, map_one]
      rfl
    · have e : φ.1 (finGL E a k * infGL E a y * finGL E a (k⁻¹ * l)) = φ.1 (finGL E a k * infGL E a y) :=
        congrFun (congrArg Subtype.val hl) _
      rw [mul_assoc, infGL_comm, ← mul_assoc, ← map_mul, mul_inv_cancel_left] at e
      rw [e]
      exact (h y).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (zero_le_one.trans (GlobalTheory.CuspRep.one_le_height y)) _))

theorem hasModerateGrowth_of {φ : Sm E a} (hl : ∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g)
    (hU : IsOpen {k | GlobalTheory.CuspRep.finRep E a k φ = φ})
    (hg : ∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ.1 (g * infGL E a y)‖ ≤ C * GlobalTheory.CuspRep.height y ^ N) :
    HasModerateGrowth φ.1 := by
  obtain ⟨ω, hω, hB, t, ht, hred⟩ := Reduction.exists_siegelSet (K := E) a
  obtain ⟨Ω, hΩ, hfin⟩ := UpperTheory.siegelSet_inter_translate_finite E a ω hω t
  obtain ⟨D, M, hD⟩ := UpperTheory.siegelSet_height_bound E a ω hω hB t ht
  obtain ⟨C, N, h0, hC⟩ := unif φ hU hg hΩ
  refine ⟨C * (3 * D) ^ N, M * N, fun g => ?_⟩
  obtain ⟨γ, hγ⟩ := hred g
  have h1 := hC _ (hfin _ hγ) (GeneralLinearGroup.map (pInf E) (AdelicGLn.diagonal E a γ * g))
  have h2 := height_pInf_le (AdelicGLn.diagonal E a γ * g)
  have h3 := hD g γ hγ
  have e : finGL E a (finPart (AdelicGLn.diagonal E a γ * g)) *
      infGL E a (GeneralLinearGroup.map (pInf E) (AdelicGLn.diagonal E a γ * g)) = ratGL E a γ * g :=
    (infGL_comm _ _).symm.trans (infGL_mul_finGL (AdelicGLn.diagonal E a γ * g))
  rw [e, hl] at h1
  refine h1.trans ?_
  rw [mul_assoc C, pow_mul, ← mul_pow]
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans (GlobalTheory.CuspRep.one_le_height _)) ?_ N) h0
  rw [mul_assoc]
  linarith

theorem isAutForm_iff (φ : Sm E a) : IsAutForm φ ↔ IsAutomorphicForm φ.1 :=
  ⟨fun h => ⟨h.left, isSmooth_of_level h.level, isKFinite_of h.level h.kfin, (zfin_iff φ).1 h.zfin,
      hasModerateGrowth_of h.left h.level h.growth⟩,
    fun h => ⟨h.isLeftInvariant, level_of h.isSmooth h.isKFinite, kfin_of h.isKFinite, (zfin_iff φ).2 h.isZFinite,
      growth_of h.hasModerateGrowth⟩⟩

theorem isCuspForm_iff (φ : Sm E a) : GlobalTheory.CuspRep.IsCuspForm φ ↔ φ.1 ∈ cuspForms E a := by
  refine (and_congr_left' (isAutForm_iff φ)).trans ?_
  rw [mem_cuspForms]
  exact and_congr_right fun h => ⟨UpperTheory.constantTerm_eq_zero_of_isCuspidal E a _ h.isLeftInvariant h.continuous,
    UpperTheory.isCuspidal_of_constantTerm_eq_zero E a _ h.isLeftInvariant h.continuous⟩

theorem cuspForms_le_Sm : cuspForms E a ≤ Sm E a := fun _ h => (sm_eq E a).ge h.1.isSmooth.1

theorem automorphicForms_le_Sm : automorphicForms E a ≤ Sm E a := fun _ h => (sm_eq E a).ge h.isSmooth.1

theorem exists_isCuspForm {f : GA E a → ℂ} (hf : f ∈ cuspForms E a) : ∃ h : f ∈ Sm E a, GlobalTheory.CuspRep.IsCuspForm ⟨f, h⟩ :=
  ⟨cuspForms_le_Sm hf, (isCuspForm_iff _).2 hf⟩

theorem lie_val (X : Lie E a) (φ : Sm E a) (h : φ.1 ∈ archSmooth E a) :
    (lie E a X φ).1 = (uAction (UniversalEnvelopingAlgebra.ι ℝ (lieEq E a X)) ⟨φ.1, h⟩).1 :=
  (congrArg Subtype.val (uAction_ι_smEq X φ)).symm

end UpperTheory.V.Cm
