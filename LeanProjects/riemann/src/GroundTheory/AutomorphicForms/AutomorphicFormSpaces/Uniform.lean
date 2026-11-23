import Mathlib
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.HasModerateGrowthZero

open NumberField IsDedekindDomain Topology Filter Set
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace AutomorphicForm

set_option linter.unusedSectionVars false

theorem exists_finset_eval_eq_zero {X : Type*} (W : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ W] :
    ∃ S : Finset X, ∀ w ∈ W, (∀ x ∈ S, w x = 0) → w = 0 := by
  classical
  let kerS : Finset X → Submodule ℂ W := fun S =>
    ⨅ x ∈ S, LinearMap.ker ((LinearMap.proj (R := ℂ) (φ := fun _ : X => ℂ) x).comp W.subtype)
  have mem_kerS : ∀ (S : Finset X) (w : W), w ∈ kerS S ↔ ∀ x ∈ S, (w : X → ℂ) x = 0 := by
    intro S w
    simp only [kerS, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
      Submodule.coe_subtype, LinearMap.coe_proj, Function.eval]
  have key : ∀ m : ℕ, ∀ S : Finset X, Module.finrank ℂ (kerS S) = m →
      ∃ S' : Finset X, kerS S' = ⊥ := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro S hS
      by_cases h : kerS S = ⊥
      · exact ⟨S, h⟩
      · obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
        have : ∃ x, (w : X → ℂ) x ≠ 0 := by
          by_contra hc
          push Not at hc
          exact hw0 (Subtype.ext (funext hc))
        obtain ⟨x, hx⟩ := this
        have hle : kerS (insert x S) ≤ kerS S := fun v hv =>
          (mem_kerS S v).2 fun y hy => (mem_kerS _ v).1 hv y (Finset.mem_insert_of_mem hy)
        have hne : kerS (insert x S) ≠ kerS S := by
          intro e
          rw [← e] at hw
          exact hx ((mem_kerS _ w).1 hw x (Finset.mem_insert_self x S))
        have hlt := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle hne)
        exact ih _ (hS ▸ hlt) _ rfl
  obtain ⟨S, hS⟩ := key _ ∅ rfl
  refine ⟨S, fun w hw h0 => ?_⟩
  have : (⟨w, hw⟩ : W) ∈ kerS S := (mem_kerS S _).2 h0
  rw [hS, Submodule.mem_bot] at this
  exact congrArg Subtype.val this

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

open Reduction

abbrev finPart (g : AdelicGLn.AdelicGL K n) : AdelicGLn.FiniteAdelicGL K n :=
  (AdelicGLn.prodEquiv K n g).2

theorem inv_mul_finEmb_mul (k : AdelicGLn.AdelicGL K n) (y : AdelicGLn.FiniteAdelicGL K n) :
    k⁻¹ * finEmb K n y * k = finEmb K n ((finPart k)⁻¹ * y * finPart k) := by
  apply (AdelicGLn.prodEquiv K n).injective
  rw [map_mul, map_mul, map_inv, prodEquiv_finEmb, prodEquiv_finEmb]
  ext <;> simp [finPart]

theorem finEmb_mem_maxCompact {y : AdelicGLn.FiniteAdelicGL K n}
    (hy : y ∈ AdelicGLn.integralFiniteGL K n) : finEmb K n y ∈ maxCompact := by
  rw [AdelicGLn.mem_integralFiniteGL_iff_forall] at hy
  refine ⟨fun w => ?_, fun v => ?_⟩
  · have : infAt w (finEmb K n y) = 1 := by
      show (AdelicGLn.infiniteEquiv K n (AdelicGLn.prodEquiv K n (finEmb K n y)).1) w = 1
      rw [prodEquiv_finEmb, map_one]
      rfl
    rw [this]
    exact one_mem _
  · have : finAt v (finEmb K n y) = AdelicGLn.finiteRestrictedEquiv K n y v := by
      show (AdelicGLn.finiteRestrictedEquiv K n (AdelicGLn.prodEquiv K n (finEmb K n y)).2) v = _
      rw [prodEquiv_finEmb]
    rw [this]
    exact hy v

theorem rightTranslate_one' {M : Type*} [MulOneClass M] {F : Type*} (f : M → F) :
    rightTranslate (1 : M) f = f := by
  funext g
  simp only [rightTranslate, mul_one]

theorem rightTranslate_mul' {M : Type*} [Semigroup M] {F : Type*} (a b : M)
    (f : M → F) : rightTranslate (a * b) f = rightTranslate a (rightTranslate b f) := by
  funext g
  simp only [rightTranslate, mul_assoc]

theorem IsSmooth.eventually_mul_finEmb_mul {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : IsSmooth φ)
    (g k : AdelicGLn.AdelicGL K n) :
    ∀ᶠ y in 𝓝 (1 : AdelicGLn.FiniteAdelicGL K n), φ (g * finEmb K n y * k) = φ (g * k) := by
  have hc : Tendsto (fun y : AdelicGLn.FiniteAdelicGL K n => (finPart k)⁻¹ * y * finPart k)
      (𝓝 1) (𝓝 1) := by
    have : Continuous fun y : AdelicGLn.FiniteAdelicGL K n => (finPart k)⁻¹ * y * finPart k :=
      (continuous_const.mul continuous_id).mul continuous_const
    simpa using this.tendsto 1
  refine (hc.eventually (hφ.2 (g * k))).mono fun y hy => ?_
  rw [← hy, ← inv_mul_finEmb_mul]
  congr 1
  group

theorem exists_openSubgroup_rightInvariant {φ : AdelicGLn.AdelicGL K n → ℂ} (hs : IsSmooth φ)
    (hk : IsKFinite φ) :
    ∃ U : OpenSubgroup (AdelicGLn.FiniteAdelicGL K n),
      (U : Set (AdelicGLn.FiniteAdelicGL K n)) ⊆ AdelicGLn.integralFiniteGL K n ∧
        ∀ g, ∀ u ∈ U, φ (g * finEmb K n u) = φ g := by
  classical
  set Kc := (maxCompact : Subgroup (AdelicGLn.AdelicGL K n))
  set s : Set (AdelicGLn.AdelicGL K n → ℂ) :=
    range fun k : Kc => rightTranslate (k : AdelicGLn.AdelicGL K n) φ with hs_def
  set W := Submodule.span ℂ s
  have : FiniteDimensional ℂ W := hk
  obtain ⟨S, hS⟩ := exists_finset_eval_eq_zero W
  obtain ⟨b, hbs, hbspan, hbli⟩ := exists_linearIndependent ℂ s
  have hbfin : b.Finite := by
    have hli : LinearIndependent ℂ (fun x : b => (⟨(x : AdelicGLn.AdelicGL K n → ℂ),
        Submodule.subset_span (hbs x.2)⟩ : W)) := by
      apply LinearIndependent.of_comp W.subtype
      exact hbli
    exact Set.finite_coe_iff.1 hli.finite

  have hbk : ∀ w ∈ b, ∃ k : Kc, w = rightTranslate (k : AdelicGLn.AdelicGL K n) φ := by
    intro w hw
    obtain ⟨k, hk⟩ := hbs hw
    exact ⟨k, hk.symm⟩

  have hstab : ∀ u ∈ AdelicGLn.integralFiniteGL K n, ∀ w ∈ W,
      rightTranslate (finEmb K n u) w ∈ W := by
    intro u hu w hw
    refine Submodule.span_induction (p := fun w _ => rightTranslate (finEmb K n u) w ∈ W)
      ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨k, rfl⟩
      rw [← rightTranslate_mul']
      exact Submodule.subset_span ⟨⟨_, mul_mem (finEmb_mem_maxCompact hu) k.2⟩, rfl⟩
    · exact W.zero_mem
    · intro x y _ _ hx hy
      exact W.add_mem hx hy
    · intro c x _ hx
      exact W.smul_mem c hx

  have hnhds : ∀ᶠ u in 𝓝 (1 : AdelicGLn.FiniteAdelicGL K n),
      u ∈ AdelicGLn.integralFiniteGL K n ∧
        ∀ w ∈ hbfin.toFinset, ∀ x ∈ S, w (x * finEmb K n u) = w x := by
    have h0 : ∀ᶠ u in 𝓝 (1 : AdelicGLn.FiniteAdelicGL K n), u ∈ AdelicGLn.integralFiniteGL K n :=
      (AdelicGLn.isOpen_integralFiniteGL K n).mem_nhds (one_mem _)
    refine h0.and ?_
    rw [eventually_all_finset]
    intro w hw
    rw [eventually_all_finset]
    intro x _
    obtain ⟨k, rfl⟩ := hbk w (hbfin.mem_toFinset.1 hw)
    simpa only [rightTranslate] using hs.eventually_mul_finEmb_mul x k

  let H : Subgroup (AdelicGLn.FiniteAdelicGL K n) :=
    { carrier := {u | u ∈ AdelicGLn.integralFiniteGL K n ∧
        ∀ w ∈ W, rightTranslate (finEmb K n u) w = w}
      one_mem' := ⟨one_mem _, fun w _ => by rw [map_one, rightTranslate_one']⟩
      mul_mem' := fun {u v} hu hv => ⟨mul_mem hu.1 hv.1, fun w hw => by
        rw [map_mul, rightTranslate_mul', hv.2 w hw, hu.2 w hw]⟩
      inv_mem' := fun {u} hu => ⟨inv_mem hu.1, fun w hw => by
        have := congrArg (rightTranslate (finEmb K n u⁻¹)) (hu.2 w hw)
        rw [← rightTranslate_mul', ← map_mul, inv_mul_cancel, map_one, rightTranslate_one'] at this
        exact this.symm⟩ }
  have hHnhds : (H : Set (AdelicGLn.FiniteAdelicGL K n)) ∈ 𝓝 1 := by
    refine Filter.mem_of_superset hnhds fun u hu => ⟨hu.1, fun w hw => ?_⟩

    rw [show W = Submodule.span ℂ b from hbspan.symm] at hw
    refine Submodule.span_induction (p := fun w _ => rightTranslate (finEmb K n u) w = w)
      ?_ ?_ ?_ ?_ hw
    · intro w hwb
      have hwW : w ∈ W := Submodule.subset_span (hbs hwb)
      have hd := W.sub_mem (hstab u hu.1 w hwW) hwW
      have := hS _ hd fun x hx => by
        simp only [Pi.sub_apply, rightTranslate]
        rw [hu.2 w (hbfin.mem_toFinset.2 hwb) x hx, sub_self]
      exact sub_eq_zero.1 this
    · rfl
    · intro x y _ _ hx hy
      rw [show rightTranslate (finEmb K n u) (x + y) =
        rightTranslate (finEmb K n u) x + rightTranslate (finEmb K n u) y from rfl, hx, hy]
    · intro c x _ hx
      rw [show rightTranslate (finEmb K n u) (c • x) = c • rightTranslate (finEmb K n u) x from rfl,
        hx]
  refine ⟨⟨H, Subgroup.isOpen_of_mem_nhds H hHnhds⟩, fun u hu => hu.1, fun g u hu => ?_⟩
  have hφW : φ ∈ W := Submodule.subset_span ⟨1, rightTranslate_one' φ⟩
  exact congrFun (hu.2 φ hφW) g

theorem continuous_of_isSmooth_of_isKFinite {φ : AdelicGLn.AdelicGL K n → ℂ} (hs : IsSmooth φ)
    (hk : IsKFinite φ) : Continuous φ := by
  obtain ⟨U, -, hU⟩ := exists_openSubgroup_rightInvariant hs hk
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  let e : AdelicGLn.AdelicGL K n → AdelicGLn.InfiniteAdelicGL K n × AdelicGLn.FiniteAdelicGL K n :=
    fun g => AdelicGLn.prodEquiv K n (g₀⁻¹ * g)
  have he : Continuous e :=
    (AdelicGLn.prodEquiv K n).continuous.comp (continuous_const.mul continuous_id)
  let F : AdelicGLn.InfiniteAdelicGL K n × AdelicGLn.FiniteAdelicGL K n → ℂ :=
    fun p => φ (g₀ * infEmb K n (archEquiv K n p.1) * finEmb K n p.2)
  have hφF : φ = F ∘ e := by
    funext g
    simp only [F, e, Function.comp_apply, mul_assoc]
    rw [infEmb_mul_finEmb, mul_inv_cancel_left]
  have hslice : Continuous (archSlice φ g₀) := by
    letI := (isExpLieAlgebra K n).chartedSpace
    exact (hs.1 g₀).continuous
  have hF : ContinuousAt F (e g₀) := by
    have hFeq : F =ᶠ[𝓝 (e g₀)] fun p => archSlice φ g₀ (archEquiv K n p.1) := by
      have he1 : e g₀ = 1 := by simp only [e, inv_mul_cancel, map_one]
      have hmem : (univ ×ˢ (U : Set (AdelicGLn.FiniteAdelicGL K n))) ∈ 𝓝 (e g₀) := by
        rw [he1]
        exact prod_mem_nhds univ_mem (U.isOpen.mem_nhds (one_mem U))
      filter_upwards [hmem] with p hp
      exact hU _ p.2 hp.2
    refine ContinuousAt.congr ?_ hFeq.symm
    exact (hslice.comp ((archEquiv K n).continuous.comp continuous_fst)).continuousAt
  rw [hφF]
  exact hF.comp he.continuousAt

theorem IsAutomorphicForm.continuous {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : IsAutomorphicForm φ) :
    Continuous φ :=
  continuous_of_isSmooth_of_isKFinite hφ.isSmooth hφ.isKFinite

end AutomorphicForm

end

end GroundTheory.Automorphic
