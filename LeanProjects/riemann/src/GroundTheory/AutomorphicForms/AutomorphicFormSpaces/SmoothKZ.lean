import Mathlib
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Translation

open NumberField IsDedekindDomain Topology Filter Set
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace AutomorphicForm

attribute [local instance 100] LieRing.ofAssociativeRing

theorem UEnv.induction {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    {C : UniversalEnvelopingAlgebra ℝ L → Prop}
    (halg : ∀ r : ℝ, C (algebraMap ℝ _ r)) (hι : ∀ x, C (UniversalEnvelopingAlgebra.ι ℝ x))
    (hmul : ∀ a b, C a → C b → C (a * b)) (hadd : ∀ a b, C a → C b → C (a + b))
    (u : UniversalEnvelopingAlgebra ℝ L) : C u := by
  obtain ⟨t, rfl⟩ := Quotient.exists_rep u
  show C (UniversalEnvelopingAlgebra.mkAlgHom ℝ L t)
  induction t using TensorAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes]; exact halg r
  | ι x => exact hι x
  | mul a b ha hb => rw [map_mul]; exact hmul _ _ ha hb
  | add a b ha hb => rw [map_add]; exact hadd _ _ ha hb

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

open Reduction

theorem fg_span_AdU (u : UEnv K n) :
    (Submodule.span ℝ (range fun a : archGroup K n => (isExpLieAlgebra K n).AdU a u)).FG := by
  induction u using UEnv.induction with
  | halg r =>
    refine (Submodule.fg_span_singleton (algebraMap ℝ (UEnv K n) r)).of_le ?_
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    dsimp only
    rw [AlgHom.commutes]
    exact Submodule.mem_span_singleton_self _
  | hι X =>
    have : Module.Finite ℝ (isExpLieAlgebra K n).lieSubalgebra :=
      FiniteDimensional.finiteDimensional_submodule
        ((isExpLieAlgebra K n).lieSubalgebra.toSubmodule)
    let ιL : (isExpLieAlgebra K n).lieSubalgebra →ₗ[ℝ] UEnv K n :=
      (UniversalEnvelopingAlgebra.ι ℝ (L := (isExpLieAlgebra K n).lieSubalgebra)).toLinearMap
    have hfg : (LinearMap.range ιL).FG := by
      rw [LinearMap.range_eq_map]
      exact (Module.Finite.fg_top).map ιL
    refine hfg.of_le (Submodule.span_le.2 ?_)
    rintro _ ⟨a, rfl⟩
    dsimp only
    rw [IsExpLieAlgebra.AdU_ι]
    exact ⟨_, rfl⟩
  | hmul a b ha hb =>
    refine (ha.mul hb).of_le (Submodule.span_le.2 ?_)
    rintro _ ⟨g, rfl⟩
    dsimp only
    rw [map_mul]
    exact Submodule.mul_mem_mul (Submodule.subset_span ⟨g, rfl⟩) (Submodule.subset_span ⟨g, rfl⟩)
  | hadd a b ha hb =>
    refine (ha.sup hb).of_le (Submodule.span_le.2 ?_)
    rintro _ ⟨g, rfl⟩
    dsimp only
    rw [map_add]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨g, rfl⟩) (Submodule.subset_span ⟨g, rfl⟩)

structure IsSmoothKZ (φ : AdelicGLn.AdelicGL K n → ℂ) : Prop where
  isLeftInvariant : IsLeftInvariant φ
  isSmooth : IsSmooth φ
  isKFinite : IsKFinite φ
  isZFinite : IsZFinite ⟨φ, isSmooth.1⟩

theorem isAutomorphicForm_iff {φ : AdelicGLn.AdelicGL K n → ℂ} :
    IsAutomorphicForm φ ↔ IsSmoothKZ φ ∧ HasModerateGrowth φ :=
  ⟨fun h => ⟨⟨h.1, h.2, h.3, h.4⟩, h.5⟩, fun ⟨h, m⟩ => ⟨h.1, h.2, h.3, h.4, m⟩⟩

theorem IsAutomorphicForm.isSmoothKZ {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : IsAutomorphicForm φ) :
    IsSmoothKZ φ :=
  (isAutomorphicForm_iff.1 hφ).1

variable (K n) in

def smoothKZ : Submodule ℂ (AdelicGLn.AdelicGL K n → ℂ) where
  carrier := {φ | IsSmoothKZ φ}
  zero_mem' := ⟨isLeftInvariant_zero, isSmooth_zero, isKFinite_zero, isZFinite_zero⟩
  add_mem' {φ ψ} hφ hψ := ⟨hφ.1.add hψ.1, hφ.2.add hψ.2, hφ.3.add hψ.3, by
    have := hφ.4.add hψ.4
    rwa [← archSmooth_mk_add] at this⟩
  smul_mem' c φ hφ := ⟨hφ.1.smul c, hφ.2.smul c, hφ.3.smul c, by
    have := hφ.4.smul c
    rwa [← archSmooth_mk_smul] at this⟩

theorem automorphicForms_le_smoothKZ : automorphicForms K n ≤ smoothKZ K n :=
  fun _ hφ => hφ.isSmoothKZ

theorem sliceL_diagonal_mul {φ : archSmooth K n} (hφ : IsLeftInvariant (φ : AdelicGLn.AdelicGL K n → ℂ))
    (γ : GL (Fin n) K) (g : AdelicGLn.AdelicGL K n) :
    sliceL (AdelicGLn.diagonal K n γ * g) φ = sliceL g φ :=
  Subtype.ext (funext fun x => by simp only [coe_sliceL, archSlice_apply, mul_assoc, hφ γ])

theorem IsLeftInvariant.uAction {φ : archSmooth K n}
    (hφ : IsLeftInvariant (φ : AdelicGLn.AdelicGL K n → ℂ)) (u : UEnv K n) :
    IsLeftInvariant (AutomorphicForm.uAction u φ : AdelicGLn.AdelicGL K n → ℂ) := fun γ g => by
  simp only [coe_uAction, uActFun, sliceL_diagonal_mul hφ]

theorem IsZFinite.uAction {φ : archSmooth K n} (hφ : IsZFinite φ) (u : UEnv K n) :
    IsZFinite (AutomorphicForm.uAction u φ) := by
  unfold IsZFinite at *
  have hle : Submodule.span ℂ ((fun z => AutomorphicForm.uAction z (AutomorphicForm.uAction u φ)) ''
        ((isExpLieAlgebra K n).centerU : Set (UEnv K n))) ≤
      (Submodule.span ℂ ((fun z => AutomorphicForm.uAction z φ) ''
        ((isExpLieAlgebra K n).centerU : Set (UEnv K n)))).map (AutomorphicForm.uAction u) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨_, Submodule.subset_span ⟨z, hz, rfl⟩, ?_⟩
    have hc : u * z = z * u := (Subalgebra.mem_center_iff.1 hz) u
    show (AutomorphicForm.uAction u * AutomorphicForm.uAction z) φ =
      (AutomorphicForm.uAction z * AutomorphicForm.uAction u) φ
    rw [← map_mul, ← map_mul, hc]
  exact Submodule.finiteDimensional_of_le hle

theorem IsSmoothKZ.isSmooth_uAction {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : IsSmoothKZ φ)
    (u : UEnv K n) : IsSmooth (uAction u ⟨φ, hφ.isSmooth.1⟩ : AdelicGLn.AdelicGL K n → ℂ) := by
  refine ⟨(uAction u _).2, fun g => ?_⟩
  obtain ⟨U, -, hU⟩ := exists_openSubgroup_rightInvariant hφ.isSmooth hφ.isKFinite
  filter_upwards [U.mem_nhds_one] with y hy
  have e : sliceL (g * finEmb K n y) (⟨φ, hφ.isSmooth.1⟩ : archSmooth K n) =
      sliceL g ⟨φ, hφ.isSmooth.1⟩ := Subtype.ext (funext fun x => by
    simp only [coe_sliceL, archSlice_apply]
    rw [mul_assoc, ← infEmb_mul_finEmb_comm, ← mul_assoc, hU _ y hy])
  simp only [coe_uAction, uActFun, e]

theorem IsSmoothKZ.isKFinite_uAction {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : IsSmoothKZ φ)
    (u : UEnv K n) : IsKFinite (uAction u ⟨φ, hφ.isSmooth.1⟩ : AdelicGLn.AdelicGL K n → ℂ) := by
  classical
  set φs : archSmooth K n := ⟨φ, hφ.isSmooth.1⟩
  set Wf := Submodule.span ℂ (range fun k : (maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
    rightTranslate (k : AdelicGLn.AdelicGL K n) φ)
  have : FiniteDimensional ℂ Wf := hφ.isKFinite
  set W' : Submodule ℂ (archSmooth K n) := Wf.comap (archSmooth K n).subtype
  have : FiniteDimensional ℂ W' := by
    refine FiniteDimensional.of_injective
      (((archSmooth K n).subtype.comp W'.subtype).codRestrict Wf fun x => x.2) ?_
    intro x y hxy
    have := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext this)
  obtain ⟨t, htfin, htspan⟩ := Submodule.fg_def.1 (fg_span_AdU u)
  have : Finite t := htfin.to_subtype
  let M : Submodule ℂ (archSmooth K n) := ⨆ b : t, W'.map (uAction (b : UEnv K n))
  unfold IsKFinite
  have hle : Submodule.span ℂ
      (range fun k : (maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
        rightTranslate (k : AdelicGLn.AdelicGL K n) (uAction u φs : AdelicGLn.AdelicGL K n → ℂ)) ≤
      M.map (archSmooth K n).subtype := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    set a := archPart (k : AdelicGLn.AdelicGL K n)
    set kf := finPart (k : AdelicGLn.AdelicGL K n)
    have hψ : ((rtInf a (rtFin kf φs) : archSmooth K n) : AdelicGLn.AdelicGL K n → ℂ) =
        rightTranslate (k : AdelicGLn.AdelicGL K n) φ := by
      simp only [coe_rtInf, coe_rtFin, ← rightTranslate_mul']
      rw [infEmb_archPart_mul_finEmb_finPart]
    have hψW : rtInf a (rtFin kf φs) ∈ W' := by
      show ((rtInf a (rtFin kf φs) : archSmooth K n) : AdelicGLn.AdelicGL K n → ℂ) ∈ Wf
      rw [hψ]
      exact Submodule.subset_span ⟨k, rfl⟩
    have heq : rightTranslate (k : AdelicGLn.AdelicGL K n) (uAction u φs : AdelicGLn.AdelicGL K n → ℂ) =
        (uAction ((isExpLieAlgebra K n).AdU a u) (rtInf a (rtFin kf φs)) :
          AdelicGLn.AdelicGL K n → ℂ) := by
      rw [uAction_rtInf, IsExpLieAlgebra.AdU_inv_apply, uAction_rtFin]
      simp only [coe_rtInf, coe_rtFin, ← rightTranslate_mul']
      rw [infEmb_archPart_mul_finEmb_finPart]
    show rightTranslate (k : AdelicGLn.AdelicGL K n) (uAction u φs : AdelicGLn.AdelicGL K n → ℂ) ∈
      M.map (archSmooth K n).subtype
    rw [heq]
    refine ⟨uAction ((isExpLieAlgebra K n).AdU a u) (rtInf a (rtFin kf φs)), ?_, rfl⟩
    have hmem : (isExpLieAlgebra K n).AdU a u ∈ Submodule.span ℝ t := by
      rw [htspan]
      exact Submodule.subset_span ⟨a, rfl⟩
    refine Submodule.span_induction
      (p := fun v _ => uAction v (rtInf a (rtFin kf φs)) ∈ M) ?_ ?_ ?_ ?_ hmem
    · intro b hb
      exact Submodule.mem_iSup_of_mem (⟨b, hb⟩ : t) ⟨_, hψW, rfl⟩
    · rw [map_zero, LinearMap.zero_apply]
      exact M.zero_mem
    · intro x y _ _ hx hy
      rw [map_add, LinearMap.add_apply]
      exact M.add_mem hx hy
    · intro r x _ hx
      rw [map_smul, LinearMap.smul_apply]
      exact Submodule.smul_of_tower_mem M r hx
  exact Submodule.finiteDimensional_of_le hle

theorem IsSmoothKZ.uAction {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : IsSmoothKZ φ) (u : UEnv K n) :
    IsSmoothKZ (AutomorphicForm.uAction u ⟨φ, hφ.isSmooth.1⟩ : AdelicGLn.AdelicGL K n → ℂ) where
  isLeftInvariant := IsLeftInvariant.uAction hφ.isLeftInvariant u
  isSmooth := hφ.isSmooth_uAction u
  isKFinite := hφ.isKFinite_uAction u
  isZFinite := hφ.isZFinite.uAction u

theorem IsSmoothKZ.rightTranslate_finEmb {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : IsSmoothKZ φ)
    (h : AdelicGLn.FiniteAdelicGL K n) : IsSmoothKZ (rightTranslate (finEmb K n h) φ) where
  isLeftInvariant := hφ.isLeftInvariant.translate _
  isSmooth := hφ.isSmooth.rightTranslate_finEmb h
  isKFinite := IsKFinite.rightTranslate_finEmb hφ.isSmooth hφ.isKFinite h
  isZFinite := hφ.isZFinite.map_rtFin h

theorem IsSmoothKZ.rightTranslate_infEmb {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : IsSmoothKZ φ)
    {a : archGroup K n} (ha : a ∈ archCompact K n) : IsSmoothKZ (rightTranslate (infEmb K n a) φ) where
  isLeftInvariant := hφ.isLeftInvariant.translate _
  isSmooth := hφ.isSmooth.rightTranslate_infEmb a
  isKFinite := hφ.isKFinite.rightTranslate_of_mem_maxCompact ha
  isZFinite := hφ.isZFinite.map_rtInf a

end AutomorphicForm

end

end GroundTheory.Automorphic
