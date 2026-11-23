import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs

noncomputable section

open scoped ZeroAtInfty InnerProductSpace ComplexConjugate
open Complex Filter Topology

namespace GlobalTheory.CompanionTheory.FuncCalc

section Ops

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : Submodule ℂ H} {Ω : M →ₗ[ℂ] M} {T : H →L[ℂ] H}

theorem res_val (h3 : ∀ x : M, ∃ v : M, (v : H) = T x ∧ (v : H) + (Ω (Ω v) : H) = x)
    (x v : M) (hv : (v : H) = T x) : (v : H) + (Ω (Ω v) : H) = x := by
  obtain ⟨v', hv', h⟩ := h3 x
  have : v' = v := Subtype.ext (hv'.trans hv.symm)
  subst this
  exact h

theorem res_symm (hd : Dense (M : Set H)) (hs : ∀ x y : M, ⟪(Ω x : H), y⟫_ℂ = ⟪(x : H), Ω y⟫_ℂ)
    (h3 : ∀ x : M, ∃ v : M, (v : H) = T x ∧ (v : H) + (Ω (Ω v) : H) = x) (x y : H) :
    ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ := by
  have h0 : ∀ x y : M, ⟪T x, (y : H)⟫_ℂ = ⟪(x : H), T y⟫_ℂ := by
    intro x y
    obtain ⟨v, hv, hx⟩ := h3 x
    obtain ⟨u, hu, hy⟩ := h3 y
    rw [← hv, ← hu, ← hy, ← hx, inner_add_right, inner_add_left, hs (Ω v) u, hs v (Ω u)]
  have h1 : ∀ (x : M) (y : H), ⟪T x, y⟫_ℂ = ⟪(x : H), T y⟫_ℂ := fun x =>
    congrFun (Continuous.ext_on hd (f := fun y => ⟪T x, y⟫_ℂ) (g := fun y => ⟪(x : H), T y⟫_ℂ)
      (by fun_prop) (by fun_prop) (fun y hy => h0 x ⟨y, hy⟩))
  exact congrFun (Continuous.ext_on hd (f := fun x => ⟪T x, y⟫_ℂ) (g := fun x => ⟪x, T y⟫_ℂ)
      (by fun_prop) (by fun_prop) (fun x hx => h1 ⟨x, hx⟩ y)) x

theorem res_omega (h3 : ∀ x : M, ∃ v : M, (v : H) = T x ∧ (v : H) + (Ω (Ω v) : H) = x)
    (h4 : ∀ x : M, T ((x : H) + (Ω (Ω x) : H)) = x) (w v : M) (hv : (v : H) = T w) :
    T (Ω w) = Ω v := by
  have hw : w = v + Ω (Ω v) := Subtype.ext (by simpa using (res_val h3 w v hv).symm)
  have := h4 (Ω v)
  rw [hw]
  simpa using this

theorem res_inj (hd : Dense (M : Set H)) (hs : ∀ x y : M, ⟪(Ω x : H), y⟫_ℂ = ⟪(x : H), Ω y⟫_ℂ)
    (h3 : ∀ x : M, ∃ v : M, (v : H) = T x ∧ (v : H) + (Ω (Ω v) : H) = x)
    (h4 : ∀ x : M, T ((x : H) + (Ω (Ω x) : H)) = x) : Function.Injective T := by
  refine (injective_iff_map_eq_zero T).2 fun x hx => ?_
  have h : (fun y => ⟪x, y⟫_ℂ) = fun _ => 0 :=
    Continuous.ext_on hd (by fun_prop) (by fun_prop) (fun y hy => by
      have h1 := h4 ⟨y, hy⟩
      have h2 := res_symm hd hs h3 x ((⟨y, hy⟩ : M) + Ω (Ω ⟨y, hy⟩) : M)
      simp only [Submodule.coe_add] at h2
      rw [h1, hx, inner_zero_left] at h2
      exact h2.symm)
  exact inner_self_eq_zero.1 (congrFun h x)

theorem exists_bdd (hd : Dense (M : Set H)) (hs : ∀ x y : M, ⟪(Ω x : H), y⟫_ℂ = ⟪(x : H), Ω y⟫_ℂ)
    (h3 : ∀ x : M, ∃ v : M, (v : H) = T x ∧ (v : H) + (Ω (Ω v) : H) = x) :
    ∃ Z : H →L[ℂ] H, ∀ x v : M, (v : H) = T x → Z x = (Ω v : H) - I • (v : H) := by
  let T₀ : M →ₗ[ℂ] M := (T.toLinearMap.comp M.subtype).codRestrict M (fun x => by
    obtain ⟨v, hv, _⟩ := h3 x
    simpa [← hv] using v.2)
  have hT₀ : ∀ x : M, ((T₀ x : M) : H) = T x := fun x => rfl
  let Z₀ : M →ₗ[ℂ] H := M.subtype ∘ₗ (Ω - I • LinearMap.id) ∘ₗ T₀
  have hZ₀ : ∀ x : M, Z₀ x = (Ω (T₀ x) : H) - I • ((T₀ x : M) : H) := fun x => by
    simp [Z₀]
  have hb : ∀ x : M, ‖Z₀ x‖ ≤ 1 * ‖x‖ := by
    intro x
    set v := T₀ x with hvdef
    have hx : (v : H) + (Ω (Ω v) : H) = x := res_val h3 x v (hT₀ x)
    have him : (⟪(Ω v : H), (v : H)⟫_ℂ).im = 0 := by
      have h := hs v v
      rw [← inner_conj_symm (v : H) (Ω v : H)] at h
      exact Complex.conj_eq_iff_im.1 h.symm
    have hsq : ‖Z₀ x‖ ^ 2 = ‖(Ω v : H)‖ ^ 2 + ‖(v : H)‖ ^ 2 := by
      rw [hZ₀, ← hvdef, @norm_sub_sq ℂ, norm_smul, inner_smul_right]
      simp [him]
    have hre : (⟪(x : H), (v : H)⟫_ℂ).re = ‖(Ω v : H)‖ ^ 2 + ‖(v : H)‖ ^ 2 := by
      have a1 : ∀ a : H, (⟪a, a⟫_ℂ).re = ‖a‖ ^ 2 := fun a => inner_self_eq_norm_sq (𝕜 := ℂ) a
      rw [← hx, inner_add_left, hs (Ω v) v, Complex.add_re, a1, a1]
      ring
    have hcs : (⟪(x : H), (v : H)⟫_ℂ).re ≤ ‖(x : H)‖ * ‖(v : H)‖ :=
      (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
    have hN0 := norm_nonneg (Z₀ x)
    have hv0 := norm_nonneg (v : H)
    have hx0 := norm_nonneg (x : H)
    have hΩ0 := norm_nonneg (Ω v : H)
    have hvN : ‖(v : H)‖ ≤ ‖Z₀ x‖ := by
      by_contra h
      push_neg at h
      nlinarith
    rw [one_mul]
    change ‖Z₀ x‖ ≤ ‖(x : H)‖
    by_contra h
    push_neg at h
    nlinarith
  let Z₁ : M →L[ℂ] H := Z₀.mkContinuous 1 hb
  refine ⟨Z₁.extend M.subtypeL, fun x v hv => ?_⟩
  have h := Z₁.extend_eq (e := M.subtypeL) (by simpa using hd.denseRange_val) isUniformEmbedding_subtype_val.isUniformInducing x
  have hv' : T₀ x = v := Subtype.ext hv.symm
  simp only [Submodule.subtypeL_apply] at h
  rw [h]
  simp [Z₁, hZ₀, hv']

end Ops

section Ops2

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : Submodule ℂ H} {Ω : M →ₗ[ℂ] M} {T : H →L[ℂ] H}

theorem bdd_adjoint (hd : Dense (M : Set H)) (hs : ∀ x y : M, ⟪(Ω x : H), y⟫_ℂ = ⟪(x : H), Ω y⟫_ℂ)
    (h3 : ∀ x : M, ∃ v : M, (v : H) = T x ∧ (v : H) + (Ω (Ω v) : H) = x)
    (h4 : ∀ x : M, T ((x : H) + (Ω (Ω x) : H)) = x) (Z : H →L[ℂ] H)
    (hZ : ∀ x v : M, (v : H) = T x → Z x = (Ω v : H) - I • (v : H)) (x v : M) (hv : (v : H) = T x) :
    ContinuousLinearMap.adjoint Z x = (Ω v : H) + I • (v : H) := by
  refine ext_inner_left ℂ fun y => ?_
  have h : (fun y => ⟪y, ContinuousLinearMap.adjoint Z x⟫_ℂ) =
      fun y => ⟪y, (Ω v : H) + I • (v : H)⟫_ℂ := by
    refine Continuous.ext_on hd (by fun_prop) (by fun_prop) (fun y hy => ?_)
    obtain ⟨u, hu, -⟩ := h3 ⟨y, hy⟩
    have e1 : ⟪(u : H), (x : H)⟫_ℂ = ⟪y, (v : H)⟫_ℂ := by
      rw [hu, hv]
      exact res_symm hd hs h3 _ _
    have e2 : ⟪(Ω u : H), (x : H)⟫_ℂ = ⟪y, (Ω v : H)⟫_ℂ := by
      rw [hs, hu, ← res_omega h3 h4 x v hv]
      exact res_symm hd hs h3 _ _
    simp only [ContinuousLinearMap.adjoint_inner_right]
    rw [hZ ⟨y, hy⟩ u hu, inner_sub_left, inner_smul_left, inner_add_right, inner_smul_right, e1, e2]
    simp
  exact congrFun h y

theorem bdd_mul (hd : Dense (M : Set H)) (hs : ∀ x y : M, ⟪(Ω x : H), y⟫_ℂ = ⟪(x : H), Ω y⟫_ℂ)
    (h3 : ∀ x : M, ∃ v : M, (v : H) = T x ∧ (v : H) + (Ω (Ω v) : H) = x)
    (h4 : ∀ x : M, T ((x : H) + (Ω (Ω x) : H)) = x) (Z : H →L[ℂ] H)
    (hZ : ∀ x v : M, (v : H) = T x → Z x = (Ω v : H) - I • (v : H)) :
    ContinuousLinearMap.adjoint Z * Z = T ∧ Z * ContinuousLinearMap.adjoint Z = T ∧
      Z - ContinuousLinearMap.adjoint Z = (-2 * I) • T := by
  have hA := bdd_adjoint hd hs h3 h4 Z hZ
  have key : ∀ (S : H →L[ℂ] H), (∀ x : M, S x = T x) → S = T := fun S h =>
    ContinuousLinearMap.coeFn_injective (Continuous.ext_on hd S.continuous T.continuous
      (fun x hx => h ⟨x, hx⟩))
  refine ⟨key _ fun x => ?_, key _ fun x => ?_, ?_⟩
  · obtain ⟨v, hv, -⟩ := h3 x
    obtain ⟨u, hu, hvu⟩ := h3 v
    have hTa : ((Ω u - I • u : M) : H) = T ((Ω v - I • v : M) : H) := by
      simp [← res_omega h3 h4 v u hu, hu]
    have h1 : Z x = ((Ω v - I • v : M) : H) := by simpa using hZ x v hv
    rw [ContinuousLinearMap.mul_apply, h1, hA _ _ hTa, ← hv, ← hvu]
    simp only [map_sub, map_smul, Submodule.coe_sub, Submodule.coe_smul]
    have : I • I • (u : H) = -(u : H) := by rw [smul_smul]; simp
    rw [smul_sub, this]
    abel
  · obtain ⟨v, hv, -⟩ := h3 x
    obtain ⟨u, hu, hvu⟩ := h3 v
    have hTa : ((Ω u + I • u : M) : H) = T ((Ω v + I • v : M) : H) := by
      simp [← res_omega h3 h4 v u hu, hu]
    have h1 : ContinuousLinearMap.adjoint Z x = ((Ω v + I • v : M) : H) := by simpa using hA x v hv
    rw [ContinuousLinearMap.mul_apply, h1, hZ _ _ hTa, ← hv, ← hvu]
    simp only [map_add, map_smul, Submodule.coe_add, Submodule.coe_smul]
    have : I • I • (u : H) = -(u : H) := by rw [smul_smul]; simp
    rw [smul_add, this]
    abel
  · refine ContinuousLinearMap.coeFn_injective (Continuous.ext_on hd (by fun_prop) (by fun_prop)
      (fun x hx => ?_))
    obtain ⟨v, hv, -⟩ := h3 ⟨x, hx⟩
    have a := hZ ⟨x, hx⟩ v hv
    have b := hA ⟨x, hx⟩ v hv
    simp only [] at a b
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, a, b]
    rw [← hv.trans rfl]
    module

theorem bdd_omega (hd : Dense (M : Set H)) (hs : ∀ x y : M, ⟪(Ω x : H), y⟫_ℂ = ⟪(x : H), Ω y⟫_ℂ)
    (h3 : ∀ x : M, ∃ v : M, (v : H) = T x ∧ (v : H) + (Ω (Ω v) : H) = x)
    (h4 : ∀ x : M, T ((x : H) + (Ω (Ω x) : H)) = x) (Z : H →L[ℂ] H)
    (hZ : ∀ x v : M, (v : H) = T x → Z x = (Ω v : H) - I • (v : H)) (v : M) :
    Z ((Ω v : H) + I • (v : H)) = v := by
  have hA := bdd_adjoint hd hs h3 h4 Z hZ (v + Ω (Ω v)) v (by simpa using (h4 v).symm)
  have h2 := (bdd_mul hd hs h3 h4 Z hZ).2.1
  rw [← hA, ← ContinuousLinearMap.mul_apply, h2]
  simpa using h4 v

theorem bdd_comm (hd : Dense (M : Set H)) (hs : ∀ x y : M, ⟪(Ω x : H), y⟫_ℂ = ⟪(x : H), Ω y⟫_ℂ)
    (h3 : ∀ x : M, ∃ v : M, (v : H) = T x ∧ (v : H) + (Ω (Ω v) : H) = x)
    (h4 : ∀ x : M, T ((x : H) + (Ω (Ω x) : H)) = x) (Z : H →L[ℂ] H)
    (hZ : ∀ x v : M, (v : H) = T x → Z x = (Ω v : H) - I • (v : H)) (S : H →L[ℂ] H)
    (hS : ∀ x : M, ∃ v : M, (v : H) = S x ∧ (Ω v : H) = S (Ω x)) :
    Commute Z S ∧ Commute (ContinuousLinearMap.adjoint Z) S := by
  have hA := bdd_adjoint hd hs h3 h4 Z hZ
  have hST : ∀ (x p v s : M), (p : H) = S x → (v : H) = T x → (s : H) = S v → (s : H) = T p := by
    intro x p v s hp hv hs'
    obtain ⟨s', hs1, hs2⟩ := hS v
    have hss : s' = s := Subtype.ext (hs1.trans hs'.symm)
    subst hss
    obtain ⟨t, ht1, ht2⟩ := hS (Ω v)
    have hts : t = Ω s' := Subtype.ext (ht1.trans hs2.symm)
    subst hts
    have hx := res_val h3 x v hv
    have : (p : H) = (s' : H) + Ω (Ω s') := by
      rw [hp, ← hx, map_add, ← hs1, ht2]
    have h5 := h4 s'
    rw [← this] at h5
    exact h5.symm
  have key : ∀ (A B : H →L[ℂ] H), (∀ x : M, A x = B x) → A = B := fun A B h =>
    ContinuousLinearMap.coeFn_injective (Continuous.ext_on hd A.continuous B.continuous
      (fun x hx => h ⟨x, hx⟩))
  constructor
  · refine key _ _ fun x => ?_
    obtain ⟨v, hv, -⟩ := h3 x
    obtain ⟨p, hp, -⟩ := hS x
    obtain ⟨s, hs1, hs2⟩ := hS v
    have := hST x p v s hp hv hs1
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, ← hp, hZ _ _ this, hZ _ _ hv,
      map_sub, map_smul, hs2, hs1]
  · refine key _ _ fun x => ?_
    obtain ⟨v, hv, -⟩ := h3 x
    obtain ⟨p, hp, -⟩ := hS x
    obtain ⟨s, hs1, hs2⟩ := hS v
    have := hST x p v s hp hv hs1
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, ← hp, hA _ _ this, hA _ _ hv,
      map_add, map_smul, hs2, hs1]

end Ops2

section Calc

variable {A : Type*} [CStarAlgebra A]

def yOf (z : ℂ) : ℝ := (z⁻¹).re

def lift (g : C₀(ℝ, ℂ)) (z : ℂ) : ℂ := if z = 0 then 0 else g (yOf z)

theorem circ_inv {z : ℂ} (hz : z ≠ 0) (h : z - conj z = (-2 * I) * (conj z * z)) :
    z⁻¹ = (yOf z : ℂ) + I := by
  have hc : conj z ≠ 0 := (map_ne_zero _).2 hz
  have h1 : z⁻¹ - conj z⁻¹ = 2 * I := by
    rw [map_inv₀]
    field_simp
    linear_combination -h
  have h2 : (z⁻¹).im = 1 := by
    rw [Complex.sub_conj] at h1
    have := congrArg Complex.im h1
    simpa using this
  apply Complex.ext
  · simp [yOf]
  · simpa using h2

theorem spec_circle (Z : A) (hn : IsStarNormal Z)
    (hsp : Z - star Z = (-2 * I) • (star Z * Z)) :
    ∀ z ∈ spectrum ℂ Z, z - conj z = (-2 * I) * (conj z * z) := by
  have hcj : ContinuousOn (fun z : ℂ => conj z) (spectrum ℂ Z) := Complex.continuous_conj.continuousOn
  have h1 : cfc (fun z : ℂ => conj z) Z = star Z := cfc_star_id (R := ℂ) Z
  have h2 : cfc (fun z : ℂ => z) Z = Z := cfc_id' ℂ Z
  have e1 : cfc (fun z : ℂ => z - conj z) Z = Z - star Z := by
    rw [cfc_sub (fun z : ℂ => z) (fun z : ℂ => conj z) Z continuousOn_id hcj, h1, h2]
  have e2 : cfc (fun z : ℂ => (-2 * I) * (conj z * z)) Z = (-2 * I) • (star Z * Z) := by
    rw [cfc_const_mul (-2 * I) (fun z : ℂ => conj z * z) Z (hcj.mul continuousOn_id),
      cfc_mul (fun z : ℂ => conj z) (fun z : ℂ => z) Z hcj continuousOn_id, h1, h2]
  have h := (cfc_eq_cfc_iff_eqOn (R := ℂ) (a := Z) (f := fun z : ℂ => z - conj z)
    (g := fun z : ℂ => (-2 * I) * (conj z * z)) hn (continuousOn_id.sub hcj)
    (continuousOn_const.mul (hcj.mul continuousOn_id))).1 (by rw [e1, e2, hsp])
  exact fun z hz => h hz

theorem tendsto_yOf (K : Set ℂ) (hK : ∀ z ∈ K, z - conj z = (-2 * I) * (conj z * z)) :
    Tendsto yOf (𝓝[K \ {0}] 0) (cocompact ℝ) := by
  rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
  have h1 : Tendsto (fun z : ℂ => z⁻¹) (𝓝[K \ {0}] 0) (Bornology.cobounded ℂ) :=
    tendsto_inv₀_nhdsNE_zero.mono_left (nhdsWithin_mono _ fun z hz => hz.2)
  have h2 : Tendsto (fun z : ℂ => ‖z⁻¹‖ - 1) (𝓝[K \ {0}] 0) atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_norm_atTop_iff_cobounded.2 h1)
  refine tendsto_atTop_mono' _ ?_ h2
  filter_upwards [self_mem_nhdsWithin] with z hz
  have h3 := circ_inv (by simpa using hz.2) (hK z hz.1)
  have h4 : ‖z⁻¹‖ ≤ ‖yOf z‖ + 1 := by
    rw [h3]
    refine (norm_add_le _ _).trans ?_
    simp
  linarith

theorem lift_cont (K : Set ℂ) (hK : ∀ z ∈ K, z - conj z = (-2 * I) * (conj z * z))
    (g : C₀(ℝ, ℂ)) : ContinuousOn (lift g) K := by
  intro z0 hz0
  by_cases h0 : z0 = 0
  · subst h0
    rw [← continuousWithinAt_diff_self]
    have h1 : Tendsto (fun z => g (yOf z)) (𝓝[K \ {0}] 0) (𝓝 0) :=
      g.zero_at_infty'.comp (tendsto_yOf K hK)
    have h2 : lift g 0 = 0 := by simp [lift]
    rw [ContinuousWithinAt, h2]
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have : z ≠ 0 := by simpa using hz.2
    simp [lift, this]
  · have h1 : lift g =ᶠ[𝓝 z0] fun z => g (yOf z) := by
      filter_upwards [eventually_ne_nhds h0] with z hz
      simp [lift, hz]
    have h2 : ContinuousAt (fun z => g (yOf z)) z0 :=
      g.continuous.continuousAt.comp
        (Complex.continuous_re.continuousAt.comp (continuousAt_inv₀ h0))
    exact (h2.congr h1.symm).continuousWithinAt

theorem lift_norm_le (g : C₀(ℝ, ℂ)) (z : ℂ) : ‖lift g z‖ ≤ ‖g‖ := by
  unfold lift
  split_ifs
  · simp
  · rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    exact g.toBCF.norm_coe_le_norm _

theorem abs_calc (Z : A) (hn : IsStarNormal Z) (hsp : Z - star Z = (-2 * I) • (star Z * Z)) :
    ∃ Φ : C₀(ℝ, ℂ) →L[ℂ] A, (∀ g h, Φ (g * h) = Φ g * Φ h) ∧ (∀ g, Φ (star g) = star (Φ g)) ∧
      (∀ g, ‖Φ g‖ ≤ ‖g‖) ∧
      (∀ g : C₀(ℝ, ℂ), (∀ y, g y = ((1 + y ^ 2)⁻¹ : ℝ)) → Φ g = star Z * Z) ∧
      (∀ g h : C₀(ℝ, ℂ), (∀ y, h y = y * g y) → Z * (Φ h + I • Φ g) = Φ g) ∧
      (∀ S : A, Commute Z S → Commute (star Z) S → ∀ g, Commute (Φ g) S) := by
  have hK := spec_circle Z hn hsp
  have hc : ∀ g, ContinuousOn (lift g) (spectrum ℂ Z) := lift_cont _ hK
  have hcj : ContinuousOn (fun z : ℂ => conj z) (spectrum ℂ Z) := Complex.continuous_conj.continuousOn
  have hb : ∀ g, ‖cfc (lift g) Z‖ ≤ ‖g‖ := fun g =>
    norm_cfc_le (norm_nonneg g) fun z _ => lift_norm_le g z
  let L : C₀(ℝ, ℂ) →ₗ[ℂ] A :=
    { toFun := fun g => cfc (lift g) Z
      map_add' := fun g h => by
        rw [← cfc_add Z (lift g) (lift h) (hc g) (hc h)]
        congr 1
        funext z
        by_cases hz : z = 0 <;> simp [lift, hz]
      map_smul' := fun c g => by
        rw [RingHom.id_apply, ← cfc_smul c (lift g) Z (hc g)]
        congr 1
        funext z
        by_cases hz : z = 0 <;> simp [lift, hz] }
  have hL : ∀ g, L g = cfc (lift g) Z := fun g => rfl
  refine ⟨L.mkContinuous 1 (fun g => by rw [hL, one_mul]; exact hb g), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g h
    simp only [LinearMap.mkContinuous_apply, hL]
    rw [← cfc_mul (lift g) (lift h) Z (hc g) (hc h)]
    congr 1
    funext z
    by_cases hz : z = 0 <;> simp [lift, hz]
  · intro g
    simp only [LinearMap.mkContinuous_apply, hL]
    rw [← cfc_star (lift g) Z]
    congr 1
    funext z
    by_cases hz : z = 0 <;> simp [lift, hz]
  · intro g
    exact hb g
  · intro g hg
    simp only [LinearMap.mkContinuous_apply, hL]
    have h1 : cfc (fun z : ℂ => conj z * z) Z = star Z * Z := by
      rw [cfc_mul (fun z : ℂ => conj z) (fun z : ℂ => z) Z hcj continuousOn_id,
        show cfc (fun z : ℂ => conj z) Z = star Z from cfc_star_id (R := ℂ) Z, cfc_id' ℂ Z]
    rw [← h1]
    refine cfc_congr fun z hz => ?_
    by_cases h0 : z = 0
    · simp [lift, h0]
    · have h3 := circ_inv h0 (hK z hz)
      have hc0 : conj z ≠ 0 := (map_ne_zero _).2 h0
      have h4 : conj z⁻¹ = (yOf z : ℂ) - I := by
        rw [h3]
        simp [sub_eq_add_neg]
      have h5 : ((1 + (yOf z) ^ 2 : ℝ) : ℂ) = z⁻¹ * conj z⁻¹ := by
        rw [h4, h3]
        push_cast
        ring_nf
        simp
        ring
      simp only [lift, h0, if_false, hg]
      rw [Complex.ofReal_inv, h5, map_inv₀]
      field_simp
  · intro g h hh
    simp only [LinearMap.mkContinuous_apply, hL]
    have h1 : Z * (cfc (lift h) Z + I • cfc (lift g) Z) =
        cfc (fun z : ℂ => z * (lift h z + I • lift g z)) Z := by
      rw [cfc_mul (fun z : ℂ => z) (fun z : ℂ => lift h z + I • lift g z) Z continuousOn_id
        ((hc h).add ((hc g).const_smul I)), cfc_id' ℂ Z,
        cfc_add Z (lift h) (fun z : ℂ => I • lift g z) (hc h) ((hc g).const_smul I),
        cfc_smul I (lift g) Z (hc g)]
    rw [h1]
    refine cfc_congr fun z hz => ?_
    by_cases h0 : z = 0
    · simp [lift, h0]
    · have h3 := circ_inv h0 (hK z hz)
      simp only [lift, h0, if_false, hh, smul_eq_mul]
      have h4 : z * ((yOf z : ℂ) + I) = 1 := by
        rw [← h3]
        exact mul_inv_cancel₀ h0
      linear_combination (g (yOf z)) * h4
  · intro S h1 h2 g
    simp only [LinearMap.mkContinuous_apply, hL]
    exact Commute.cfc (𝕜 := ℂ) h1 h2 _

end Calc

theorem absFC : PositivityTheory.RgBcC.Fc.AbsFC := by
  intro H _ _ _ M Ω T hd hs h3 h4
  obtain ⟨Z, hZ⟩ := exists_bdd hd hs h3
  obtain ⟨m1, m2, m3⟩ := bdd_mul hd hs h3 h4 Z hZ
  have hstar : star Z = ContinuousLinearMap.adjoint Z := ContinuousLinearMap.star_eq_adjoint Z
  have hn : IsStarNormal Z := ⟨by
    change star Z * Z = Z * star Z
    rw [hstar, m1, m2]⟩
  have hsp : Z - star Z = (-2 * I) • (star Z * Z) := by rw [hstar, m1, m3]
  obtain ⟨Φ, p1, p2, p3, p4, p5, p6⟩ := abs_calc Z hn hsp
  have hinj : Function.Injective Z := fun x y hxy => res_inj hd hs h3 h4 (by
    rw [← m1, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, hxy])
  refine ⟨⟨Φ, p1, fun g => ?_, p3, fun g hg => ?_, ?_, ?_⟩⟩
  · rw [p2, ContinuousLinearMap.star_eq_adjoint]
  · rw [p4 g hg, hstar, m1]
  · intro g h hh x v hv
    have e1 := congrArg (fun A : H →L[ℂ] H => A x) (p5 g h hh)
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ← hv] at e1
    have e2 := bdd_omega hd hs h3 h4 Z hZ v
    have e3 := hinj (e1.trans e2.symm)
    exact (add_right_cancel e3).symm
  · intro S hS g
    obtain ⟨c1, c2⟩ := bdd_comm hd hs h3 h4 Z hZ S hS
    exact (p6 S c1 (hstar ▸ c2) g).eq.symm

end GlobalTheory.CompanionTheory.FuncCalc
