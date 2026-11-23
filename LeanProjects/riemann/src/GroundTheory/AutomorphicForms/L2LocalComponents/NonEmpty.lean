import Mathlib
import GroundTheory.AutomorphicForms.L2LocalComponents.NonEmptyOps
import GroundTheory.AutomorphicForms.MultiplicityOne.ArchTypeExists

open MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace GroundTheory.Automorphic

noncomputable section

namespace CuspidalSpectrum

open AutomorphicForm Reduction

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

theorem uAction_mem {V : Submodule ℂ (CuspL2 μ)} (hVc : IsClosed (V : Set (CuspL2 μ)))
    (hV : (cuspRepT μ).IsInvariant V) (u : UEnv K n) (v : (isExpLieAlgebra K n).smoothVectors (archRepT μ))
    (hv : (v : CuspL2 μ) ∈ V) : ((isExpLieAlgebra K n).uAction (archRepT μ) u v : CuspL2 μ) ∈ V := by
  obtain ⟨L, hL⟩ := (isExpLieAlgebra K n).exists_wordSum (archRepT μ) u
  rw [hL]
  clear hL
  have hlist : ∀ l : List (archLie K n), (isExpLieAlgebra K n).listOp (archRepT μ) l v ∈ V := by
    intro l
    induction l with
    | nil => exact hv
    | cons X l ih =>
      rw [IsExpLieAlgebra.listOp_cons]
      exact derivOp_mem μ hVc hV ih ((isExpLieAlgebra K n).isSmoothVector_listOp (archRepT μ) v.2 l) X
  induction L with
  | nil => exact V.zero_mem
  | cons p L ih =>
    rw [IsExpLieAlgebra.wordSum_cons]
    exact V.add_mem (V.smul_mem _ (hlist p.2)) ih

theorem starProjection_fixU_mem {V : Submodule ℂ (CuspL2 μ)} (hVc : IsClosed (V : Set (CuspL2 μ)))
    (hV : (cuspRepT μ).IsInvariant V) (U : Subgroup (AdelicGLn.integralFiniteGL K n)) {x : CuspL2 μ}
    (hx : x ∈ V) : (fixU μ U).starProjection x ∈ V := by
  have : CompleteSpace V := hVc.completeSpace_coe
  set Q := V.starProjection
  set P := (fixU μ U).starProjection
  have hQ : ∀ g, Commute (cuspRepT μ g) Q := (UnitaryRep.isInvariant_iff_commute_starProjection V).1 hV
  have hQfix : ∀ y ∈ fixU μ U, Q y ∈ fixU μ U := by
    intro y hy u hu
    have := congrArg (fun T : CuspL2 μ →L[ℂ] CuspL2 μ => T y) (hQ (finOne K n u)).eq
    change cuspRepT μ (finOne K n u) (Q y) = Q (cuspRepT μ (finOne K n u) y) at this
    rw [this, hy u hu]
  have hPx : P x = Q (P x) := by
    refine (Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hQfix _ (Submodule.starProjection_apply_mem _ _))
      fun w hw => ?_)
    have hxQ : x = Q x := (Submodule.starProjection_eq_self_iff.2 hx).symm
    have e : x - Q (P x) = Q (x - P x) := by rw [map_sub, ← hxQ]
    rw [e, Submodule.inner_starProjection_left_eq_right]
    exact Submodule.inner_left_of_mem_orthogonal (hQfix w hw)
      (Submodule.sub_starProjection_mem_orthogonal x)
  rw [hPx]
  exact Submodule.starProjection_apply_mem V _

theorem archRepT_comm_starProjection {V : Submodule ℂ (CuspL2 μ)} [CompleteSpace V]
    (hV : (cuspRepT μ).IsInvariant V) (a : archGroup K n) :
    V.starProjection ∘L archRepT μ a = archRepT μ a ∘L V.starProjection := by
  have h := ((UnitaryRep.isInvariant_iff_commute_starProjection V).1 hV (archP K n a)).eq
  ext y
  have := congrArg (fun T : CuspL2 μ →L[ℂ] CuspL2 μ => T y) h
  exact this.symm

set_option maxHeartbeats 4000000 in

theorem exists_isZKFinite_of_summand (V : Submodule ℂ (CuspL2 μ)) [CompleteSpace V]
    (hV : (cuspRepT μ).IsInvariant V) (hirr : ((cuspRepT μ).restrict V hV).IsIrreducible) :
    ∃ e ∈ V, e ≠ 0 ∧ IsZKFinite μ e := by
  have hVc : IsClosed (V : Set (CuspL2 μ)) := (completeSpace_coe_iff_isComplete.1 ‹_›).isClosed

  obtain ⟨U, hU, hne⟩ :=
    MultiplicityOne.exists_fixedSubspace_ne_bot (σ := (cuspRepT μ).restrict V hV) μ hirr
  obtain ⟨w₀, hw₀, hw₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  set w : CuspL2 μ := V.subtype w₀ with hwdef
  have hwV : w ∈ V := w₀.2
  have hw0 : w ≠ 0 := fun h => hw₀0 (Subtype.ext h)
  have hwU : w ∈ fixU μ U := by
    intro u hu
    have h1 := hw₀ (u : AdelicGLn.FiniteAdelicGL K n) ⟨u, hu, rfl⟩
    have h2 := congrArg Subtype.val h1
    rw [UnitaryRep.coe_restrict_apply, MultiplicityOne.finProj_eq_finOne] at h2
    exact h2

  set ν : Measure (archGroup K n) := Measure.haar
  set N : Set (archGroup K n) := {a | ‖archRepT μ a w - w‖ < ‖w‖ / 2}
  have hN : N ∈ 𝓝 (1 : archGroup K n) := by
    refine IsOpen.mem_nhds (isOpen_lt (((archRepT μ).continuous_orbit w).sub continuous_const).norm
      continuous_const) ?_
    show ‖archRepT μ 1 w - w‖ < ‖w‖ / 2
    rw [BanachRep.map_one_apply, sub_self, norm_zero]
    exact half_pos (norm_pos_iff.2 hw0)
  obtain ⟨ρ, hρ0, hρt, hρ1, hρinv, hρconj, hρN, hρexp⟩ := exists_archBump ν hN
  set κ : archGroup K n → ℂ := fun a => (ρ a : ℂ) with hκdef
  have hκ : (isExpLieAlgebra K n).IsTestFunction κ := hρt
  have hκc : Continuous κ := hκ.continuous _
  have hρc : Continuous ρ := Complex.continuous_re.comp hκc
  have hreal : ∀ a, starRingEnd ℂ (κ a) = κ a := fun a => Complex.conj_ofReal _
  have hsymm : ∀ a, κ a⁻¹ = κ a := fun a => by simp only [hκdef, hρinv]
  have hconjκ : ∀ k ∈ archCompact K n, ∀ a, κ (k * a * k⁻¹) = κ a := fun k hk a => by
    simp only [hκdef, hρconj k hk a]
  have hsupp : ∀ a, κ a ≠ 0 → ∃ X : archLie K n, a = (isExpLieAlgebra K n).expG X := fun a ha =>
    hρexp a (fun h => ha (by simp only [hκdef, h, Complex.ofReal_zero]))
  set πκ := archOp μ ν hκ

  have hπw : πκ w ≠ 0 := by
    have hi1 : Integrable (fun a => κ a • archRepT μ a w) ν :=
      integrable_smul_archRepT μ ν hκc hκ.2 w
    have hi2 : Integrable (fun a => κ a • w) ν :=
      (hκc.smul continuous_const).integrable_of_hasCompactSupport hκ.2.smul_right
    have hint1 : ∫ a, κ a ∂ν = 1 := by
      show ∫ a, ((ρ a : ℝ) : ℂ) ∂ν = 1
      rw [integral_complex_ofReal, hρ1, Complex.ofReal_one]
    have e : πκ w - w = ∫ a, κ a • (archRepT μ a w - w) ∂ν := by
      simp_rw [smul_sub]
      rw [integral_sub hi1 hi2, integral_smul_const, hint1, one_smul]
      rfl
    have hg : Integrable (fun a => ρ a * (‖w‖ / 2)) ν :=
      (hρc.mul continuous_const).integrable_of_hasCompactSupport
        ((hκ.2.comp_left (g := Complex.re) Complex.zero_re).mul_right)
    have hbound : ‖πκ w - w‖ ≤ ‖w‖ / 2 := by
      rw [e]
      calc ‖∫ a, κ a • (archRepT μ a w - w) ∂ν‖ ≤ ∫ a, ρ a * (‖w‖ / 2) ∂ν := by
            refine norm_integral_le_of_norm_le hg (Eventually.of_forall fun a => ?_)
            rw [norm_smul, hκdef, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hρ0 a)]
            by_cases ha : ρ a = 0
            · rw [ha, zero_mul, zero_mul]
            · exact mul_le_mul_of_nonneg_left (hρN a ha).le (hρ0 a)
        _ = ‖w‖ / 2 := by rw [integral_mul_const, hρ1, one_mul]
    intro h0
    rw [h0, zero_sub, norm_neg] at hbound
    have := norm_pos_iff.2 hw0
    linarith

  obtain ⟨F₀, c, hc, -, hint⟩ := exists_cc_integral_mul_eq μ ν U hU κ hκc hκ.2
  set R : CuspL2 μ →L[ℂ] CuspL2 μ := (cuspRepT μ).integrated μ (UnitaryRep.ccToL1 μ F₀)
  set P := (fixU μ U).starProjection
  have hPP : ∀ x, P (P x) = P x := fun x =>
    Submodule.starProjection_eq_self_iff.2 (Submodule.starProjection_apply_mem _ x)
  have hPcomm : ∀ x, P (πκ x) = πκ (P x) := archOp_comm μ ν hκ P (starProjection_fixU_comm μ U)
  have hπfix : ∀ y ∈ fixU μ U, πκ y ∈ fixU μ U := fun y hy => by
    rw [← Submodule.starProjection_eq_self_iff, hPcomm, Submodule.starProjection_eq_self_iff.2 hy]
  set A : CuspL2 μ →L[ℂ] CuspL2 μ := R ∘L P
  have hA : ∀ x, A x = (c : ℂ) • πκ (P x) := fun x =>
    integrated_eq_smul_archOp μ ν hκ hint (Submodule.starProjection_apply_mem _ x)
  have hAc : IsCompactOperator A := (isCompactOperator_cuspRep μ F₀).comp_clm P
  set T : CuspL2 μ →L[ℂ] CuspL2 μ := A ∘L A
  have hT : ∀ x, T x = ((c : ℂ) * c) • πκ (πκ (P x)) := by
    intro x
    show A (A x) = _
    rw [hA, hA, map_smul, map_smul, hPcomm, hPP, smul_smul]
  have hTc : IsCompactOperator T := hAc.comp_clm A
  have hTsymm : ∀ x y, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ := by
    intro x y
    rw [hT, hT, inner_smul_left, inner_smul_right, inner_archOp μ ν hκ hreal hsymm,
      inner_archOp μ ν hκ hreal hsymm, Submodule.inner_starProjection_left_eq_right, hPcomm, hPcomm]
    simp only [map_mul, Complex.conj_ofReal]

  have hπV : ∀ x ∈ V, πκ x ∈ V := by
    intro x hx
    have hQ := archOp_comm μ ν hκ V.starProjection (archRepT_comm_starProjection μ hV)
    have hx' : V.starProjection x = x := Submodule.starProjection_eq_self_iff.2 hx
    rw [← hx', ← hQ]
    exact Submodule.starProjection_apply_mem V _
  have hTV : ∀ x ∈ V, T x ∈ V := by
    intro x hx
    rw [hT]
    exact V.smul_mem _ (hπV _ (hπV _ (starProjection_fixU_mem μ hVc hV U hx)))
  have hTfix : ∀ x, T x ∈ fixU μ U := fun x => by
    rw [hT]
    exact (fixU μ U).smul_mem _ (hπfix _ (hπfix _ (Submodule.starProjection_apply_mem _ x)))
  have hTsmooth : ∀ x, (isExpLieAlgebra K n).IsSmoothVector (archRepT μ) (T x) := fun x => by
    rw [hT]
    exact ((isExpLieAlgebra K n).smoothVectors (archRepT μ)).smul_mem _
      ((isExpLieAlgebra K n).isSmoothVector_integrated (archRepT μ) ν hκ _)
  have hTk : ∀ k ∈ archCompact K n, ∀ x, archRepT μ k (T x) = T (archRepT μ k x) := by
    intro k hk x
    rw [hT, hT, map_smul, archOp_comm_archCompact μ ν hκ hconjκ hk,
      archOp_comm_archCompact μ ν hκ hconjκ hk]
    congr 3
    exact (congrArg (fun S : CuspL2 μ →L[ℂ] CuspL2 μ => S x) (starProjection_fixU_comm μ U k)).symm
  have hπ1 : ∀ g, ‖archRepT μ g‖ ≤ 1 := norm_archRepT_le μ
  have hTz : ∀ z ∈ (isExpLieAlgebra K n).centerU, ∀ v : (isExpLieAlgebra K n).smoothVectors (archRepT μ),
      ((isExpLieAlgebra K n).uAction (archRepT μ) z ⟨T v, hTsmooth v⟩ : CuspL2 μ) =
        T ((isExpLieAlgebra K n).uAction (archRepT μ) z v) := by
    intro z hz v
    have hP0 := (isExpLieAlgebra K n).isSmoothVector_of_commute (archRepT μ) P
      (starProjection_fixU_comm μ U) v.2
    have hP1 := (isExpLieAlgebra K n).isSmoothVector_integrated (archRepT μ) ν hκ (P v)
    have hP2 := (isExpLieAlgebra K n).isSmoothVector_integrated (archRepT μ) ν hκ (πκ (P v))
    have e0 : (⟨T v, hTsmooth v⟩ : (isExpLieAlgebra K n).smoothVectors (archRepT μ)) =
        ((c : ℂ) * c) • ⟨πκ (πκ (P v)), hP2⟩ := Subtype.ext (hT v)
    have e1 := (isExpLieAlgebra K n).uAction_integrated (archRepT μ) ν hπ1 hz hκ hsupp hP1
    have e2 := (isExpLieAlgebra K n).uAction_integrated (archRepT μ) ν hπ1 hz hκ hsupp hP0
    have e3 := (isExpLieAlgebra K n).uAction_of_commute (archRepT μ) P (starProjection_fixU_comm μ U) z v
    rw [e0, map_smul, Submodule.coe_smul, hT]
    congr 1
    calc ((isExpLieAlgebra K n).uAction (archRepT μ) z ⟨πκ (πκ (P v)), hP2⟩ : CuspL2 μ)
        = πκ ((isExpLieAlgebra K n).uAction (archRepT μ) z ⟨πκ (P v), hP1⟩) := e1
      _ = πκ (πκ ((isExpLieAlgebra K n).uAction (archRepT μ) z ⟨P v, hP0⟩)) :=
          congrArg (fun y => πκ y) e2
      _ = πκ (πκ (P ((isExpLieAlgebra K n).uAction (archRepT μ) z v))) := by rw [← e3]

  set TV : V →L[ℂ] V := (T ∘L V.subtypeL).codRestrict V (fun x => hTV x x.2)
  have hTVc : IsCompactOperator TV :=
    (hTc.comp_clm V.subtypeL).codRestrict (fun x => hTV x x.2) hVc
  have hTVs : (TV : V →ₗ[ℂ] V).IsSymmetric := fun x y => by
    show ⟪TV x, y⟫_ℂ = ⟪x, TV y⟫_ℂ
    rw [Submodule.coe_inner, Submodule.coe_inner]
    exact hTsymm x y
  have hTV0 : TV ≠ 0 := by
    intro h0
    have h1 : T w = 0 := by
      have h' := congrArg (fun S : V →L[ℂ] V => S ⟨w, hwV⟩) h0
      exact congrArg Subtype.val h'
    have h2 : ⟪T w, w⟫_ℂ = ((c : ℂ) * c) * ⟪πκ w, πκ w⟫_ℂ := by
      rw [hT, Submodule.starProjection_eq_self_iff.2 hwU, inner_smul_left, inner_archOp μ ν hκ hreal hsymm]
      simp only [map_mul, Complex.conj_ofReal]
      rfl
    rw [h1, inner_zero_left] at h2
    have h3 : ⟪πκ w, πκ w⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hπw
    have hcc : ((c : ℂ) * c) ≠ 0 := mul_ne_zero (by exact_mod_cast hc.ne') (by exact_mod_cast hc.ne')
    exact h3 ((mul_eq_zero.1 h2.symm).resolve_left hcc)
  obtain ⟨lam, hlam, hlam0⟩ : ∃ lam, Module.End.HasEigenvalue (TV : V →ₗ[ℂ] V) lam ∧ lam ≠ 0 := by
    by_contra h
    push Not at h
    exact hTV0 ((ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero hTVc hTVs).1 h)
  obtain ⟨eV, heV⟩ := hlam.exists_hasEigenvector
  have hE := ContinuousLinearMap.finite_dimensional_eigenspace hTVc lam hlam0
  set E := Module.End.eigenspace (TV : V →ₗ[ℂ] V) lam
  set e : CuspL2 μ := V.subtype eV
  have hTe : T e = lam • e := congrArg Subtype.val (Module.End.mem_eigenspace_iff.1 heV.1)
  have he0 : e ≠ 0 := fun h => heV.2 (Subtype.ext h)
  have hs : (isExpLieAlgebra K n).IsSmoothVector (archRepT μ) e := by
    have : e = lam⁻¹ • T e := by rw [hTe, smul_smul, inv_mul_cancel₀ hlam0, one_smul]
    rw [this]
    exact ((isExpLieAlgebra K n).smoothVectors (archRepT μ)).smul_mem _ (hTsmooth e)

  set F : Submodule ℂ (CuspL2 μ) := E.map V.subtype
  have hFfd : FiniteDimensional ℂ F := inferInstance
  have hmemF : ∀ x ∈ V, T x = lam • x → x ∈ F := fun x hx hTx =>
    ⟨⟨x, hx⟩, Module.End.mem_eigenspace_iff.2 (Subtype.ext hTx), rfl⟩
  have hFV : ∀ f ∈ F, f ∈ V ∧ T f = lam • f := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨f.2, congrArg Subtype.val (Module.End.mem_eigenspace_iff.1 hf)⟩
  have hFfix : ∀ f ∈ F, f ∈ fixU μ U := fun f hf => by
    obtain ⟨-, hTf⟩ := hFV f hf
    have : f = lam⁻¹ • T f := by rw [hTf, smul_smul, inv_mul_cancel₀ hlam0, one_smul]
    rw [this]
    exact (fixU μ U).smul_mem _ (hTfix f)
  have heF : e ∈ F := ⟨eV, heV.1, rfl⟩
  have hFk : ∀ k ∈ archCompact K n, ∀ f ∈ F, archRepT μ k f ∈ F := fun k hk f hf => by
    obtain ⟨hfV, hTf⟩ := hFV f hf
    refine hmemF _ (by rw [archRepT_apply]; exact hV _ _ hfV) ?_
    rw [← hTk k hk, hTf, map_smul]
  refine ⟨e, eV.2, he0, hs, ?_, ?_⟩
  ·
    have : CompactSpace (AdelicGLn.integralFiniteGL K n) :=
      isCompact_iff_compactSpace.1 (AdelicGLn.isCompact_integralFiniteGL K n)
    have : Finite (AdelicGLn.integralFiniteGL K n ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU
    set S : Submodule ℂ (CuspL2 μ) := ⨆ q : AdelicGLn.integralFiniteGL K n ⧸ U,
      F.map ((cuspRepT μ (finOne K n q.out) : CuspL2 μ →L[ℂ] CuspL2 μ) : CuspL2 μ →ₗ[ℂ] CuspL2 μ)
    have : FiniteDimensional ℂ S := Submodule.finiteDimensional_iSup _
    refine Submodule.finiteDimensional_of_le (Submodule.span_le.2 ?_ : _ ≤ S)
    rintro _ ⟨k, rfl⟩
    set k₁ := archPart (k : AdelicGLn.AdelicGL K n)
    have hk₁ : k₁ ∈ archCompact K n := archPart_mem_archCompact k.2
    have hk₂ : AutomorphicForm.finPart (k : AdelicGLn.AdelicGL K n) ∈ AdelicGLn.integralFiniteGL K n :=
      finPart_mem_integralFiniteGL k.2
    set k₂ : AdelicGLn.integralFiniteGL K n := ⟨_, hk₂⟩
    have h1 : ((archP K n k₁ : normOneGL K n) : AdelicGLn.AdelicGL K n) = infEmb K n k₁ :=
      congrArg Subtype.val (archimedeanProjection_maximalCompact ⟨k₁, hk₁⟩)
    have hdec : (⟨k, Reduction.maxCompact_le_normOneGL k.2⟩ : normOneGL K n) =
        finOne K n k₂ * archP K n k₁ := by
      rw [finOne_archP_comm]
      ext1
      rw [Subgroup.coe_mul, h1, coe_finOne]
      exact (infEmb_archPart_mul_finEmb_finPart (k : AdelicGLn.AdelicGL K n)).symm
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul U k₂
    have hf : archRepT μ k₁ e ∈ F := hFk k₁ hk₁ e heF
    show cuspRepT μ _ e ∈ S
    rw [hdec, UnitaryRep.map_mul_apply]
    have e4 : cuspRepT μ (finOne K n k₂) (archRepT μ k₁ e) =
        cuspRepT μ (finOne K n (QuotientGroup.mk k₂ : AdelicGLn.integralFiniteGL K n ⧸ U).out)
          (archRepT μ k₁ e) := by
      rw [hh, map_mul, UnitaryRep.map_mul_apply, hFfix _ hf h h.2]
    rw [show cuspRepT μ (archP K n k₁) e = archRepT μ k₁ e from rfl, e4]
    exact Submodule.mem_iSup_of_mem (QuotientGroup.mk k₂ : AdelicGLn.integralFiniteGL K n ⧸ U)
      ⟨_, hf, rfl⟩
  ·
    set W := Submodule.span ℂ ((fun z => (isExpLieAlgebra K n).uAction (archRepT μ) z ⟨e, hs⟩) ''
      ((isExpLieAlgebra K n).centerU : Set (UEnv K n)))
    have hle : W.map ((isExpLieAlgebra K n).smoothVectors (archRepT μ)).subtype ≤ F := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      refine hmemF _ (uAction_mem μ hVc hV z ⟨e, hs⟩ eV.2) ?_
      have e5 : (⟨T e, hTsmooth e⟩ : (isExpLieAlgebra K n).smoothVectors (archRepT μ)) =
          lam • ⟨e, hs⟩ := Subtype.ext hTe
      have := hTz z hz ⟨e, hs⟩
      rw [e5, map_smul] at this
      exact this.symm
    have : FiniteDimensional ℂ (W.map ((isExpLieAlgebra K n).smoothVectors (archRepT μ)).subtype) :=
      Submodule.finiteDimensional_of_le hle
    exact LinearEquiv.finiteDimensional
      (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) W).symm

theorem summandCuspForms_ne_bot (V : Submodule ℂ (CuspL2 μ)) [CompleteSpace V]
    (hV : (cuspRepT μ).IsInvariant V) (hirr : ((cuspRepT μ).restrict V hV).IsIrreducible) :
    summandCuspForms V ≠ ⊥ := by
  obtain ⟨e, heV, he0, hZK⟩ := exists_isZKFinite_of_summand μ V hV hirr
  obtain ⟨φ, hφ, hcent⟩ := exists_cuspForm_of_isZKFinite μ e hZK
  have hφe : cuspVecL μ φ = e := toLp_injective μ hφ
  intro hbot
  have hmem : φ ∈ summandCuspForms V := ⟨hcent, show cuspVecL μ φ ∈ V by rw [hφe]; exact heV⟩
  rw [hbot, Submodule.mem_bot] at hmem
  apply he0
  rw [← hφe, hmem, map_zero]

end CuspidalSpectrum

end

end GroundTheory.Automorphic
