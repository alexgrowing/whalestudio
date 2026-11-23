import Formalism.SharpRestriction.GrowthBounds.RootWeights.ExistsHighestCoordinateFunctional

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section hw

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

theorem gl_operator_mem_integral_enveloping (E : GLOps n (KK O) V) (a b : Fin n) : E a b ∈ UZmon E := by
  rw [UZmon.eq_1]
  apply Submonoid.subset_closure
  simp only [UZgens.eq_1, Set.mem_setOf_eq]
  by_cases hab : a = b
  · subst hab
    right
    exact ⟨a, 1, by simp [binomE.eq_1]⟩
  · left
    exact ⟨a, b, 1, hab, by simp [divPowE.eq_1]⟩

theorem enveloping_le_integral_enveloping (E : GLOps n (KK O) V) : Umon E ≤ UZmon E := by
  rw [Umon.eq_1, Submonoid.closure_le]
  rintro _ ⟨⟨a, b⟩, rfl⟩
  exact gl_operator_mem_integral_enveloping E a b

theorem mem_nabla_iff_coordinate_integral {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} {xi : V →ₗ[KK O] KK O} (h1 : xi v = 1)
    (h2 : ∀ w ∈ otherWts E lam, xi w = 0) (h3 : ∀ x, x - xi x • v ∈ otherWts E lam) (x : V) :
    x ∈ Nabla (O := O) E lam v ↔ ∀ u ∈ UZmon E, ∃ c : O, xi (u x) = algebraMap O (KK O) c := by
  rw [Nabla.eq_1, Set.mem_setOf_eq]
  constructor
  · intro H u hu
    obtain ⟨c, hc⟩ := H u hu
    refine ⟨c, ?_⟩
    have h := h2 _ hc
    rw [map_sub, map_smul, h1, smul_eq_mul, mul_one, sub_eq_zero] at h
    exact h
  · intro H u hu
    obtain ⟨c, hc⟩ := H u hu
    refine ⟨c, ?_⟩
    have h := h3 (u x)
    rw [hc] at h
    exact h

theorem enveloping_coordinate_separates [NeZero n] [CharZero (KK O)] {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V}
    (hI : IsIrrHW E lam v)
    (hCR : ∀ W : Submodule (KK O) V, (∀ a b, ∀ x ∈ W, E a b x ∈ W) →
      ∃ W' : Submodule (KK O) V, IsCompl W W' ∧ ∀ a b, ∀ x ∈ W', E a b x ∈ W')
    {xi : V →ₗ[KK O] KK O} (h1 : xi v = 1) {x : V} (hx : ∀ u ∈ UZmon E, xi (u x) = 0) : x = 0 := by
  classical

  let W : Submodule (KK O) V := ⨅ u : UZmon E, LinearMap.ker (xi ∘ₗ (u : Module.End (KK O) V))
  have hmemW : ∀ y, y ∈ W ↔ ∀ u ∈ UZmon E, xi (u y) = 0 := by
    intro y
    rw [Submodule.mem_iInf]
    constructor
    · intro h u hu
      have h' := h ⟨u, hu⟩
      rwa [LinearMap.mem_ker, LinearMap.comp_apply] at h'
    · intro h u
      rw [LinearMap.mem_ker, LinearMap.comp_apply]
      exact h u.1 u.2
  have hxW : x ∈ W := (hmemW x).2 hx
  have hWst : ∀ a b, ∀ y ∈ W, E a b y ∈ W := by
    intro a b y hy
    rw [hmemW] at hy ⊢
    intro u hu
    have h' := hy (u * E a b) (Submonoid.mul_mem _ hu (gl_operator_mem_integral_enveloping E a b))
    rwa [Module.End.mul_apply] at h'
  have hvW : v ∉ W := by
    intro h
    have h' := (hmemW v).1 h 1 (Submonoid.one_mem _)
    rw [Module.End.one_apply, h1] at h'
    exact one_ne_zero h'
  obtain ⟨W', hC, hW'st⟩ := hCR W hWst
  have hv2 : v ∈ W ⊔ W' := by
    rw [hC.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨w, hw, w', hw', hvs⟩ := Submodule.mem_sup.mp hv2
  have hv := hI.2.2.1
  have hvw : ∀ a, E a a v = (lam a : KK O) • v := by
    intro a
    have h1' := (Submodule.mem_iInf _).mp hv.2.1 a
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h1'
    simpa using h1'

  have hww : w ∈ weightSp E lam := by
    unfold weightSp
    refine (Submodule.mem_iInf _).mpr fun a => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    have hd : E a a w - (lam a : KK O) • w ∈ W := sub_mem (hWst a a w hw) (Submodule.smul_mem W _ hw)
    have hd' : E a a w' - (lam a : KK O) • w' ∈ W' :=
      sub_mem (hW'st a a w' hw') (Submodule.smul_mem W' _ hw')
    have hsum : (E a a w - (lam a : KK O) • w) + (E a a w' - (lam a : KK O) • w') = 0 := by
      have h2 := hvw a
      rw [← hvs, map_add, smul_add] at h2
      rw [sub_add_sub_comm, h2, sub_self]
    have hneg : E a a w - (lam a : KK O) • w ∈ W' := by
      rw [eq_neg_of_add_eq_zero_left hsum]
      exact W'.neg_mem hd'
    exact (Submodule.disjoint_def.mp hC.disjoint) _ hd hneg

  have hmem := top_le_line_sup_higher_weights hI (Submodule.mem_top : w ∈ (⊤ : Submodule (KK O) V))
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have hzw : z ∈ weightSp E lam := by
    have e : z = w - c • v := by
      rw [← hyz]
      abel
    rw [e]
    exact sub_mem hww (Submodule.smul_mem _ c hv.2.1)
  have hz0 : z = 0 :=
    weight_support_sum_eq_zero E (fun nu => weightHeightAscending lam < weightHeightAscending nu) hzw hz (lt_irrefl _)
  have hwc : w = c • v := by
    rw [← hyz, hz0, add_zero]
  have hc0 : c = 0 := by
    by_contra hc
    apply hvW
    have e : v = c⁻¹ • w := by
      rw [hwc, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [e]
    exact Submodule.smul_mem W _ hw
  have hvW' : v ∈ W' := by
    rw [hwc, hc0, zero_smul, zero_add] at hvs
    rw [← hvs]
    exact hw'
  have htop := irreducible_stable_contains_eq_top hI hW'st hvW'
  have hxW' : x ∈ W' := by
    rw [htop]
    exact Submodule.mem_top
  exact (Submodule.disjoint_def.mp hC.disjoint) x hxW hxW'

theorem lattice_fg_of_integral_functionals {W : Type*} [AddCommGroup W] [Module (KK O) W] [Module O W] [IsScalarTower O (KK O) W]
    [FiniteDimensional (KK O) W] (N : Submodule O W) (Xi : Set (W →ₗ[KK O] KK O))
    (hsep : ∀ w, (∀ ξ ∈ Xi, ξ w = 0) → w = 0)
    (hint : ∀ ξ ∈ Xi, ∀ w ∈ N, ∃ c : O, ξ w = algebraMap O (KK O) c) : N.FG := by
  classical
  obtain ⟨b, hbXi, hbspan, hbli⟩ := exists_linearIndependent (KK O) Xi
  have hbfin : b.Finite := hbli.setFinite
  haveI : Fintype b := hbfin.fintype
  have hbsep : ∀ w : W, (∀ ξ ∈ b, ξ w = 0) → w = 0 := by
    intro w hw
    apply hsep
    intro ξ hξ
    have hle' : Submodule.span (KK O) b ≤ LinearMap.ker (Module.Dual.eval (KK O) W w) := by
      rw [Submodule.span_le]
      intro η hη
      simp only [SetLike.mem_coe, LinearMap.mem_ker, Module.Dual.eval_apply]
      exact hw η hη
    have hmem : ξ ∈ Submodule.span (KK O) b := by
      rw [hbspan]
      exact Submodule.subset_span hξ
    have h := hle' hmem
    simpa using h
  let Φ : W →ₗ[O] (b → KK O) := LinearMap.pi fun ξ => (ξ.1).restrictScalars O
  have hΦ : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).2 ?_
    intro w hw
    apply hbsep
    intro ξ hξ
    have h := congrFun hw ⟨ξ, hξ⟩
    simpa [Φ] using h
  let g : (b → O) →ₗ[O] (b → KK O) :=
    LinearMap.pi fun i => (Algebra.linearMap O (KK O)).comp (LinearMap.proj i)
  have hle : N.map Φ ≤ LinearMap.range g := by
    rintro _ ⟨w, hw, rfl⟩
    choose c hc using fun ξ : b => hint ξ.1 (hbXi ξ.2) w hw
    rw [LinearMap.mem_range]
    refine ⟨c, ?_⟩
    funext ξ
    simp [g, Φ, hc]
  apply Submodule.fg_of_fg_map_injective Φ hΦ
  have hQ : ((N.map Φ).comap g).FG := IsNoetherian.noetherian _
  have h := hQ.map g
  rwa [Submodule.map_comap_eq, inf_eq_right.mpr hle] at h

end hw

end Formalism.MainNotions.G.GLWeightTheory
