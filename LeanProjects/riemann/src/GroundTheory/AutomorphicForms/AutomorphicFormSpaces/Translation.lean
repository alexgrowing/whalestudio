import Mathlib
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.ConstantTerm

open NumberField IsDedekindDomain Topology Filter Set
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace AutomorphicForm

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

open Reduction

def rightTranslateL (a : AdelicGLn.AdelicGL K n) :
    (AdelicGLn.AdelicGL K n → ℂ) →ₗ[ℂ] (AdelicGLn.AdelicGL K n → ℂ) where
  toFun := rightTranslate a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem rightTranslateL_apply (a : AdelicGLn.AdelicGL K n) (φ : AdelicGLn.AdelicGL K n → ℂ) :
    rightTranslateL a φ = rightTranslate a φ := rfl

abbrev archPart (g : AdelicGLn.AdelicGL K n) : archGroup K n :=
  archEquiv K n (AdelicGLn.prodEquiv K n g).1

theorem infEmb_archPart_mul_finEmb_finPart (g : AdelicGLn.AdelicGL K n) :
    infEmb K n (archPart g) * finEmb K n (finPart g) = g :=
  infEmb_mul_finEmb g

theorem infEmb_archPart_mem_maxCompact {k : AdelicGLn.AdelicGL K n} (hk : k ∈ maxCompact) :
    infEmb K n (archPart k) ∈ maxCompact := by
  refine ⟨fun w => ?_, fun v => ?_⟩
  · have : infAt w (infEmb K n (archPart k)) = infAt w k := by
      show (AdelicGLn.infiniteEquiv K n (AdelicGLn.prodEquiv K n (infEmb K n (archPart k))).1) w =
        (AdelicGLn.infiniteEquiv K n (AdelicGLn.prodEquiv K n k).1) w
      rw [prodEquiv_infEmb, ContinuousMulEquiv.symm_apply_apply]
    rw [this]
    exact hk.1 w
  · have : finAt v (infEmb K n (archPart k)) = 1 := by
      show (AdelicGLn.finiteRestrictedEquiv K n
        (AdelicGLn.prodEquiv K n (infEmb K n (archPart k))).2) v = 1
      rw [prodEquiv_infEmb, map_one]
      rfl
    rw [this]
    exact one_mem _

theorem archPart_mem_archCompact {k : AdelicGLn.AdelicGL K n} (hk : k ∈ maxCompact) :
    archPart k ∈ archCompact K n :=
  infEmb_archPart_mem_maxCompact hk

theorem finPart_mem_integralFiniteGL {k : AdelicGLn.AdelicGL K n} (hk : k ∈ maxCompact) :
    finPart k ∈ AdelicGLn.integralFiniteGL K n :=
  (AdelicGLn.mem_integralFiniteGL_iff_forall K n).2 fun v => hk.2 v

theorem archSlice_rightTranslate_finEmb (φ : AdelicGLn.AdelicGL K n → ℂ)
    (g : AdelicGLn.AdelicGL K n) (h : AdelicGLn.FiniteAdelicGL K n) :
    archSlice (rightTranslate (finEmb K n h) φ) g = archSlice φ (g * finEmb K n h) := by
  funext x
  simp only [archSlice_apply, rightTranslate, mul_assoc, infEmb_mul_finEmb_comm]

theorem archSlice_rightTranslate_infEmb (φ : AdelicGLn.AdelicGL K n → ℂ)
    (g : AdelicGLn.AdelicGL K n) (a : archGroup K n) :
    archSlice (rightTranslate (infEmb K n a) φ) g = rightTranslate a (archSlice φ g) := by
  funext x
  simp only [archSlice_apply, rightTranslate, mul_assoc, map_mul]

theorem IsArchSmooth.rightTranslate_finEmb {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : IsArchSmooth φ)
    (h : AdelicGLn.FiniteAdelicGL K n) : IsArchSmooth (rightTranslate (finEmb K n h) φ) :=
  fun g => by rw [archSlice_rightTranslate_finEmb]; exact hφ _

theorem IsArchSmooth.rightTranslate_infEmb {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : IsArchSmooth φ)
    (a : archGroup K n) : IsArchSmooth (rightTranslate (infEmb K n a) φ) :=
  fun g => by
    rw [archSlice_rightTranslate_infEmb]
    exact (isExpLieAlgebra K n).isSmoothFun_rightTranslate (hφ g) a

def rtFin (h : AdelicGLn.FiniteAdelicGL K n) : archSmooth K n →ₗ[ℂ] archSmooth K n :=
  (rightTranslateL (finEmb K n h)).restrict fun _ hφ => IsArchSmooth.rightTranslate_finEmb hφ h

def rtInf (a : archGroup K n) : archSmooth K n →ₗ[ℂ] archSmooth K n :=
  (rightTranslateL (infEmb K n a)).restrict fun _ hφ => IsArchSmooth.rightTranslate_infEmb hφ a

@[simp] theorem coe_rtFin (h : AdelicGLn.FiniteAdelicGL K n) (φ : archSmooth K n) :
    ((rtFin h φ : archSmooth K n) : AdelicGLn.AdelicGL K n → ℂ) =
      rightTranslate (finEmb K n h) (φ : AdelicGLn.AdelicGL K n → ℂ) := rfl

@[simp] theorem coe_rtInf (a : archGroup K n) (φ : archSmooth K n) :
    ((rtInf a φ : archSmooth K n) : AdelicGLn.AdelicGL K n → ℂ) =
      rightTranslate (infEmb K n a) (φ : AdelicGLn.AdelicGL K n → ℂ) := rfl

theorem uAction_rtFin (u : UEnv K n) (h : AdelicGLn.FiniteAdelicGL K n) (φ : archSmooth K n) :
    uAction u (rtFin h φ) = rtFin h (uAction u φ) := by
  ext g
  simp only [coe_uAction, coe_rtFin, uActFun, rightTranslate]
  have e : sliceL g (rtFin h φ) = sliceL (g * finEmb K n h) φ :=
    Subtype.ext (archSlice_rightTranslate_finEmb (φ : AdelicGLn.AdelicGL K n → ℂ) g h)
  rw [e]

theorem uAction_rtInf (u : UEnv K n) (a : archGroup K n) (φ : archSmooth K n) :
    uAction u (rtInf a φ) = rtInf a (uAction ((isExpLieAlgebra K n).AdU a⁻¹ u) φ) := by
  ext g
  simp only [coe_uAction, coe_rtInf, rightTranslate]
  have e : sliceL g (rtInf a φ) = (isExpLieAlgebra K n).rightTranslateEnd a (sliceL g φ) :=
    Subtype.ext (archSlice_rightTranslate_infEmb (φ : AdelicGLn.AdelicGL K n → ℂ) g a)
  have key := congrArg (fun T : Module.End ℂ ((isExpLieAlgebra K n).smoothFuns (F := ℂ)) =>
    ((T (sliceL g φ) : (isExpLieAlgebra K n).smoothFuns (F := ℂ)) : archGroup K n → ℂ) 1)
    ((isExpLieAlgebra K n).rightUAction_comp_rightTranslate (F := ℂ) a u)
  simp only [Module.End.mul_apply, IsExpLieAlgebra.coe_rightTranslateEnd, rightTranslate,
    one_mul] at key
  have hs := congrFun (archSlice_uActFun ((isExpLieAlgebra K n).AdU a⁻¹ u) φ g) a
  simp only [archSlice_apply] at hs
  rw [uActFun, e, key, ← hs]

theorem IsLeftInvariant.translate {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : IsLeftInvariant φ)
    (a : AdelicGLn.AdelicGL K n) : IsLeftInvariant (rightTranslate a φ) :=
  fun γ g => by simp only [GroundTheory.Automorphic.rightTranslate, mul_assoc, hφ γ]

theorem IsSmooth.rightTranslate_finEmb {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : IsSmooth φ)
    (h : AdelicGLn.FiniteAdelicGL K n) : IsSmooth (rightTranslate (finEmb K n h) φ) :=
  ⟨hφ.1.rightTranslate_finEmb h, fun g => hφ.eventually_mul_finEmb_mul g (finEmb K n h)⟩

theorem IsSmooth.rightTranslate_infEmb {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : IsSmooth φ)
    (a : archGroup K n) : IsSmooth (rightTranslate (infEmb K n a) φ) :=
  ⟨hφ.1.rightTranslate_infEmb a, fun g => hφ.eventually_mul_finEmb_mul g (infEmb K n a)⟩

theorem IsZFinite.map_rtFin {φ : archSmooth K n} (hφ : IsZFinite φ) (h : AdelicGLn.FiniteAdelicGL K n) :
    IsZFinite (rtFin h φ) := by
  unfold IsZFinite at *
  have hle : Submodule.span ℂ ((fun z => uAction z (rtFin h φ)) ''
        ((isExpLieAlgebra K n).centerU : Set (UEnv K n))) ≤
      (Submodule.span ℂ ((fun z => uAction z φ) ''
        ((isExpLieAlgebra K n).centerU : Set (UEnv K n)))).map (rtFin h) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨z, hz, rfl⟩, (uAction_rtFin z h φ).symm⟩
  exact Submodule.finiteDimensional_of_le hle

theorem IsZFinite.map_rtInf {φ : archSmooth K n} (hφ : IsZFinite φ) (a : archGroup K n) :
    IsZFinite (rtInf a φ) := by
  unfold IsZFinite at *
  have hle : Submodule.span ℂ ((fun z => uAction z (rtInf a φ)) ''
        ((isExpLieAlgebra K n).centerU : Set (UEnv K n))) ≤
      (Submodule.span ℂ ((fun z => uAction z φ) ''
        ((isExpLieAlgebra K n).centerU : Set (UEnv K n)))).map (rtInf a) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨_, (isExpLieAlgebra K n).AdU_mem_centerU a⁻¹ hz, rfl⟩,
      (uAction_rtInf z a φ).symm⟩
  exact Submodule.finiteDimensional_of_le hle

theorem HasModerateGrowth.translate {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : HasModerateGrowth φ)
    (a : AdelicGLn.AdelicGL K n) : HasModerateGrowth (rightTranslate a φ) := by
  obtain ⟨C, N, hC⟩ := hφ
  refine ⟨|C| * (heightConst K n * height a) ^ N, N, fun g => ?_⟩
  have h1 := hC (g * a)
  have h2 : height (g * a) ^ N ≤ (heightConst K n * height g * height a) ^ N :=
    pow_le_pow_left₀ (height_pos _).le (height_mul_le g a) N
  calc ‖rightTranslate a φ g‖ = ‖φ (g * a)‖ := rfl
    _ ≤ C * height (g * a) ^ N := h1
    _ ≤ |C| * height (g * a) ^ N :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (height_pos _).le N)
    _ ≤ |C| * (heightConst K n * height g * height a) ^ N :=
        mul_le_mul_of_nonneg_left h2 (abs_nonneg C)
    _ = |C| * (heightConst K n * height a) ^ N * height g ^ N := by ring

theorem IsKFinite.rightTranslate_of_mem_maxCompact {φ : AdelicGLn.AdelicGL K n → ℂ}
    (hφ : IsKFinite φ) {k : AdelicGLn.AdelicGL K n} (hk : k ∈ maxCompact) :
    IsKFinite (rightTranslate k φ) := by
  unfold IsKFinite at *
  have hle : Submodule.span ℂ
      (range fun k' : (maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
        rightTranslate (k' : AdelicGLn.AdelicGL K n) (rightTranslate k φ)) ≤
      Submodule.span ℂ (range fun k' : (maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
        rightTranslate (k' : AdelicGLn.AdelicGL K n) φ) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k', rfl⟩
    refine Submodule.subset_span ⟨⟨_, mul_mem k'.2 hk⟩, ?_⟩
    simp only [rightTranslate_mul']
  exact Submodule.finiteDimensional_of_le hle

theorem IsKFinite.rightTranslate_finEmb {φ : AdelicGLn.AdelicGL K n → ℂ} (hs : IsSmooth φ)
    (hk : IsKFinite φ) (h : AdelicGLn.FiniteAdelicGL K n) :
    IsKFinite (rightTranslate (finEmb K n h) φ) := by
  classical
  obtain ⟨U, -, hU⟩ := exists_openSubgroup_rightInvariant hs hk
  set Kf := AdelicGLn.integralFiniteGL K n

  let V : Subgroup Kf :=
    { carrier := {v | h⁻¹ * (v : AdelicGLn.FiniteAdelicGL K n) * h ∈ U}
      one_mem' := by
        show h⁻¹ * ((1 : Kf) : AdelicGLn.FiniteAdelicGL K n) * h ∈ U
        rw [OneMemClass.coe_one, mul_one, inv_mul_cancel]
        exact one_mem U
      mul_mem' := fun {v w} hv hw => by
        change h⁻¹ * (v : AdelicGLn.FiniteAdelicGL K n) * h ∈ U at hv
        change h⁻¹ * (w : AdelicGLn.FiniteAdelicGL K n) * h ∈ U at hw
        show h⁻¹ * ((v * w : Kf) : AdelicGLn.FiniteAdelicGL K n) * h ∈ U
        rw [Subgroup.coe_mul]
        have := mul_mem hv hw
        simpa only [mul_assoc, mul_inv_cancel_left] using this
      inv_mem' := fun {v} hv => by
        change h⁻¹ * (v : AdelicGLn.FiniteAdelicGL K n) * h ∈ U at hv
        show h⁻¹ * ((v⁻¹ : Kf) : AdelicGLn.FiniteAdelicGL K n) * h ∈ U
        rw [InvMemClass.coe_inv]
        have := inv_mem hv
        simpa only [mul_inv_rev, inv_inv, mul_assoc] using this }
  have hVopen : IsOpen (V : Set Kf) := by
    have hc : Continuous fun v : Kf => h⁻¹ * (v : AdelicGLn.FiniteAdelicGL K n) * h :=
      (continuous_const.mul continuous_subtype_val).mul continuous_const
    exact U.isOpen.preimage hc
  haveI : CompactSpace Kf :=
    isCompact_iff_compactSpace.1 (AdelicGLn.isCompact_integralFiniteGL K n)
  haveI : Finite (Kf ⧸ V) := Subgroup.quotient_finite_of_isOpen V hVopen

  have hinv : ∀ v ∈ V, ∀ g, φ (g * finEmb K n (v : AdelicGLn.FiniteAdelicGL K n) * finEmb K n h) =
      φ (g * finEmb K n h) := by
    intro v hv g
    have := hU (g * finEmb K n h) _ hv
    rw [← this]
    congr 1
    simp only [map_mul, map_inv, mul_assoc, mul_inv_cancel_left]
  set W := Submodule.span ℂ (range fun k : (maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
    rightTranslate (k : AdelicGLn.AdelicGL K n) φ)
  haveI : FiniteDimensional ℂ W := hk
  unfold IsKFinite
  have hle : Submodule.span ℂ
      (range fun k : (maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
        rightTranslate (k : AdelicGLn.AdelicGL K n) (rightTranslate (finEmb K n h) φ)) ≤
      ⨆ q : Kf ⧸ V, W.map (rightTranslateL (finEmb K n ((q.out : AdelicGLn.FiniteAdelicGL K n) * h))) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    set kf : Kf := ⟨finPart (k : AdelicGLn.AdelicGL K n), finPart_mem_integralFiniteGL k.2⟩
    set a := archPart (k : AdelicGLn.AdelicGL K n)
    set q : Kf ⧸ V := QuotientGroup.mk kf
    refine Submodule.mem_iSup_of_mem q ⟨rightTranslate (infEmb K n a) φ,
      Submodule.subset_span ⟨⟨_, infEmb_archPart_mem_maxCompact k.2⟩, rfl⟩, ?_⟩
    obtain ⟨v, hv⟩ := QuotientGroup.mk_out_eq_mul V kf
    have hout : ((q.out : Kf) : AdelicGLn.FiniteAdelicGL K n) =
        (kf : AdelicGLn.FiniteAdelicGL K n) * ((v : Kf) : AdelicGLn.FiniteAdelicGL K n) := by
      rw [hv]; rfl
    have hk_dec : infEmb K n a * finEmb K n (kf : AdelicGLn.FiniteAdelicGL K n) =
        (k : AdelicGLn.AdelicGL K n) := infEmb_archPart_mul_finEmb_finPart _
    funext g
    show φ (g * finEmb K n ((q.out : AdelicGLn.FiniteAdelicGL K n) * h) * infEmb K n a) =
      φ (g * (k : AdelicGLn.AdelicGL K n) * finEmb K n h)
    have hcomm : g * finEmb K n ((kf : AdelicGLn.FiniteAdelicGL K n) *
        ((v : Kf) : AdelicGLn.FiniteAdelicGL K n) * h) * infEmb K n a =
        g * infEmb K n a * finEmb K n (kf : AdelicGLn.FiniteAdelicGL K n) *
          finEmb K n ((v : Kf) : AdelicGLn.FiniteAdelicGL K n) * finEmb K n h := by
      rw [mul_assoc g, ← infEmb_mul_finEmb_comm]
      simp only [map_mul, mul_assoc]
    rw [hout, hcomm, hinv (v : Kf) v.2, ← hk_dec, mul_assoc g]
  exact Submodule.finiteDimensional_of_le hle

theorem IsAutomorphicForm.rightTranslate_finEmb {φ : AdelicGLn.AdelicGL K n → ℂ}
    (hφ : IsAutomorphicForm φ) (h : AdelicGLn.FiniteAdelicGL K n) :
    IsAutomorphicForm (rightTranslate (finEmb K n h) φ) where
  isLeftInvariant := hφ.isLeftInvariant.translate _
  isSmooth := hφ.isSmooth.rightTranslate_finEmb h
  isKFinite := IsKFinite.rightTranslate_finEmb hφ.isSmooth hφ.isKFinite h
  isZFinite := hφ.isZFinite.map_rtFin h
  hasModerateGrowth := hφ.hasModerateGrowth.translate _

theorem IsAutomorphicForm.rightTranslate_infEmb {φ : AdelicGLn.AdelicGL K n → ℂ}
    (hφ : IsAutomorphicForm φ) {a : archGroup K n} (ha : a ∈ archCompact K n) :
    IsAutomorphicForm (rightTranslate (infEmb K n a) φ) where
  isLeftInvariant := hφ.isLeftInvariant.translate _
  isSmooth := hφ.isSmooth.rightTranslate_infEmb a
  isKFinite := hφ.isKFinite.rightTranslate_of_mem_maxCompact ha
  isZFinite := hφ.isZFinite.map_rtInf a
  hasModerateGrowth := hφ.hasModerateGrowth.translate _

theorem IsAutomorphicForm.rightTranslate_of_mem_maxCompact {φ : AdelicGLn.AdelicGL K n → ℂ}
    (hφ : IsAutomorphicForm φ) {k : AdelicGLn.AdelicGL K n} (hk : k ∈ maxCompact) :
    IsAutomorphicForm (rightTranslate k φ) := by
  rw [← infEmb_archPart_mul_finEmb_finPart k, rightTranslate_mul']
  exact (hφ.rightTranslate_finEmb _).rightTranslate_infEmb (archPart_mem_archCompact hk)

theorem IsCuspidal.translate {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : IsCuspidal φ)
    (a : AdelicGLn.AdelicGL K n) : IsCuspidal (rightTranslate a φ) :=
  fun r hr hrn g => by rw [constantTerm_rightTranslate]; exact hφ r hr hrn _

variable (K n)

def finRep : Representation ℂ (AdelicGLn.FiniteAdelicGL K n) (automorphicForms K n) where
  toFun h := (rightTranslateL (finEmb K n h)).restrict fun _ hφ => hφ.rightTranslate_finEmb h
  map_one' := LinearMap.ext fun φ => Subtype.ext (funext fun g => by
    simp [GroundTheory.Automorphic.rightTranslate])
  map_mul' h₁ h₂ := LinearMap.ext fun φ => Subtype.ext (funext fun g => by
    show (φ : AdelicGLn.AdelicGL K n → ℂ) (g * finEmb K n (h₁ * h₂)) =
      (φ : AdelicGLn.AdelicGL K n → ℂ) (g * finEmb K n h₁ * finEmb K n h₂)
    rw [map_mul, mul_assoc])

def archCompactRep : Representation ℂ (archCompact K n) (automorphicForms K n) where
  toFun k := (rightTranslateL (infEmb K n k)).restrict fun _ hφ => hφ.rightTranslate_infEmb k.2
  map_one' := LinearMap.ext fun φ => Subtype.ext (funext fun g => by
    simp [GroundTheory.Automorphic.rightTranslate])
  map_mul' k₁ k₂ := LinearMap.ext fun φ => Subtype.ext (funext fun g => by
    show (φ : AdelicGLn.AdelicGL K n → ℂ) (g * infEmb K n ((k₁ * k₂ : archCompact K n) : archGroup K n)) =
      (φ : AdelicGLn.AdelicGL K n → ℂ) (g * infEmb K n k₁ * infEmb K n k₂)
    rw [Subgroup.coe_mul, map_mul, mul_assoc])

variable {K n}

@[simp] theorem coe_finRep_apply (h : AdelicGLn.FiniteAdelicGL K n) (φ : automorphicForms K n) :
    ((finRep K n h φ : automorphicForms K n) : AdelicGLn.AdelicGL K n → ℂ) =
      rightTranslate (finEmb K n h) (φ : AdelicGLn.AdelicGL K n → ℂ) := rfl

@[simp] theorem coe_archCompactRep_apply (k : archCompact K n) (φ : automorphicForms K n) :
    ((archCompactRep K n k φ : automorphicForms K n) : AdelicGLn.AdelicGL K n → ℂ) =
      rightTranslate (infEmb K n k) (φ : AdelicGLn.AdelicGL K n → ℂ) := rfl

theorem finRep_archCompactRep_comm (h : AdelicGLn.FiniteAdelicGL K n) (k : archCompact K n)
    (φ : automorphicForms K n) :
    finRep K n h (archCompactRep K n k φ) = archCompactRep K n k (finRep K n h φ) := by
  apply Subtype.ext
  funext g
  simp only [coe_finRep_apply, coe_archCompactRep_apply, GroundTheory.Automorphic.rightTranslate,
    mul_assoc, infEmb_mul_finEmb_comm]

variable (K n)

def finRepCusp : Representation ℂ (AdelicGLn.FiniteAdelicGL K n) (cuspForms K n) where
  toFun h := (rightTranslateL (finEmb K n h)).restrict fun _ hφ =>
    ⟨hφ.1.rightTranslate_finEmb h, hφ.2.translate _⟩
  map_one' := LinearMap.ext fun φ => Subtype.ext (funext fun g => by
    simp [GroundTheory.Automorphic.rightTranslate])
  map_mul' h₁ h₂ := LinearMap.ext fun φ => Subtype.ext (funext fun g => by
    show (φ : AdelicGLn.AdelicGL K n → ℂ) (g * finEmb K n (h₁ * h₂)) =
      (φ : AdelicGLn.AdelicGL K n → ℂ) (g * finEmb K n h₁ * finEmb K n h₂)
    rw [map_mul, mul_assoc])

def archCompactRepCusp : Representation ℂ (archCompact K n) (cuspForms K n) where
  toFun k := (rightTranslateL (infEmb K n k)).restrict fun _ hφ =>
    ⟨hφ.1.rightTranslate_infEmb k.2, hφ.2.translate _⟩
  map_one' := LinearMap.ext fun φ => Subtype.ext (funext fun g => by
    simp [GroundTheory.Automorphic.rightTranslate])
  map_mul' k₁ k₂ := LinearMap.ext fun φ => Subtype.ext (funext fun g => by
    show (φ : AdelicGLn.AdelicGL K n → ℂ) (g * infEmb K n ((k₁ * k₂ : archCompact K n) : archGroup K n)) =
      (φ : AdelicGLn.AdelicGL K n → ℂ) (g * infEmb K n k₁ * infEmb K n k₂)
    rw [Subgroup.coe_mul, map_mul, mul_assoc])

end AutomorphicForm

end

end GroundTheory.Automorphic
