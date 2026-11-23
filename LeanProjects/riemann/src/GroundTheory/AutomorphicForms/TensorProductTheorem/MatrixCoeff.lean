import Mathlib

noncomputable section

namespace GroundTheory.Automorphic

open Set

namespace RestrictedTensor

variable {G : Type*} [Group G] {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W]

def orbitSpan (ρ : Representation ℂ G V) (v : V) : Subrepresentation ρ where
  toSubmodule := Submodule.span ℂ (range fun g => ρ g v)
  apply_mem_toSubmodule g x hx := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      exact Submodule.subset_span ⟨g * h, by simp [map_mul]⟩
    | zero => simp
    | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
    | smul c x _ hx => simpa using Submodule.smul_mem _ c hx

theorem mem_orbitSpan_self (ρ : Representation ℂ G V) (v : V) : v ∈ (orbitSpan ρ v).toSubmodule :=
  Submodule.subset_span ⟨1, by simp⟩

theorem orbitSpan_eq_top {ρ : Representation ℂ G V} [ρ.IsIrreducible] {v : V} (hv : v ≠ 0) :
    orbitSpan ρ v = ⊤ := by
  rcases IsSimpleOrder.eq_bot_or_eq_top (orbitSpan ρ v) with h | h
  · exfalso
    apply hv
    have := mem_orbitSpan_self ρ v
    rw [h] at this
    exact this
  · exact h

theorem mem_span_orbit {ρ : Representation ℂ G V} [ρ.IsIrreducible] {v : V} (hv : v ≠ 0) (x : V) :
    x ∈ Submodule.span ℂ (range fun g => ρ g v) := by
  have := orbitSpan_eq_top (ρ := ρ) hv
  have hx : x ∈ (⊤ : Subrepresentation ρ).toSubmodule := trivial
  rw [← this] at hx
  exact hx

theorem eq_zero_of_forall_apply {ρ : Representation ℂ G V} [ρ.IsIrreducible] {v : V} (hv : v ≠ 0)
    {l : Module.Dual ℂ V} (h : ∀ g, l (ρ g v) = 0) : l = 0 := by
  ext x
  have hx := mem_span_orbit (ρ := ρ) hv x
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact h g
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

theorem eq_zero_of_forall_apply_act {ρ : Representation ℂ G V} [ρ.IsIrreducible]
    {l : Module.Dual ℂ V} (hl : l ≠ 0) {x : V} (h : ∀ g, l (ρ g x) = 0) : x = 0 := by
  by_contra hx
  exact hl (eq_zero_of_forall_apply (ρ := ρ) hx h)

def orbitMap (ρ : Representation ℂ G V) (v : V) : (G →₀ ℂ) →ₗ[ℂ] V :=
  Finsupp.linearCombination ℂ fun g => ρ g v

theorem orbitMap_apply (ρ : Representation ℂ G V) (v : V) (c : G →₀ ℂ) :
    orbitMap ρ v c = c.sum fun g a => a • ρ g v := by
  rw [orbitMap, Finsupp.linearCombination_apply]

theorem orbitMap_single (ρ : Representation ℂ G V) (v : V) (g : G) (a : ℂ) :
    orbitMap ρ v (Finsupp.single g a) = a • ρ g v := by
  rw [orbitMap, Finsupp.linearCombination_single]

theorem orbitMap_mapDomain (ρ : Representation ℂ G V) (v : V) (h : G) (c : G →₀ ℂ) :
    orbitMap ρ v (Finsupp.mapDomain (h * ·) c) = ρ h (orbitMap ρ v c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp [orbitMap]
  | add c d hc hd => rw [Finsupp.mapDomain_add, map_add, hc, hd, map_add, map_add]
  | single g a => simp [Finsupp.mapDomain_single, orbitMap_single, map_mul]

theorem range_orbitMap (ρ : Representation ℂ G V) (v : V) :
    LinearMap.range (orbitMap ρ v) = Submodule.span ℂ (range fun g => ρ g v) := by
  rw [orbitMap, Finsupp.range_linearCombination]

theorem linearForm_orbitMap (ρ : Representation ℂ G V) (v : V) (l : Module.Dual ℂ V) (h : G)
    (c : G →₀ ℂ) : l (ρ h (orbitMap ρ v c)) = c.sum fun g a => a * l (ρ (h * g) v) := by
  rw [orbitMap_apply, map_finsuppSum, map_finsuppSum]
  refine Finsupp.sum_congr fun g _ => ?_
  rw [map_smul, map_smul, smul_eq_mul, map_mul, Module.End.mul_apply]

theorem nonempty_equiv_of_matrixCoeff_eq {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    [ρ.IsIrreducible] [σ.IsIrreducible] {v : V} {l : Module.Dual ℂ V} {w : W}
    {m : Module.Dual ℂ W} (h : ∀ g, l (ρ g v) = m (σ g w)) (hne : ∃ g, l (ρ g v) ≠ 0) :
    Nonempty (ρ.Equiv σ) := by
  obtain ⟨g₀, hg₀⟩ := hne
  have hv : v ≠ 0 := by rintro rfl; simp at hg₀
  have hm : m ≠ 0 := by rintro rfl; exact hg₀ (by rw [h]; rfl)

  have hker : LinearMap.ker (orbitMap ρ v) ≤ LinearMap.ker (orbitMap σ w) := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    refine eq_zero_of_forall_apply_act (ρ := σ) hm fun k => ?_
    rw [linearForm_orbitMap]
    have := linearForm_orbitMap ρ v l k c
    rw [hc, map_zero, map_zero] at this
    rw [this]
    exact Finsupp.sum_congr fun g _ => by rw [h]
  have hsurj : Function.Surjective (orbitMap ρ v) := by
    rw [← LinearMap.range_eq_top, range_orbitMap]
    exact eq_top_iff.2 fun x _ => mem_span_orbit hv x
  let e := LinearMap.quotKerEquivOfSurjective (orbitMap ρ v) hsurj
  let F : V →ₗ[ℂ] W := ((LinearMap.ker (orbitMap ρ v)).liftQ (orbitMap σ w) hker).comp
    e.symm.toLinearMap
  have hF : ∀ c, F (orbitMap ρ v c) = orbitMap σ w c := by
    intro c
    have : e.symm (orbitMap ρ v c) = Submodule.Quotient.mk c := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [F, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
  have hFint : ∀ g x, F (ρ g x) = σ g (F x) := by
    intro g x
    obtain ⟨c, rfl⟩ := hsurj x
    rw [← orbitMap_mapDomain, hF, hF, orbitMap_mapDomain]
  let Fi : Representation.IntertwiningMap ρ σ := ⟨F, fun g => LinearMap.ext fun x => hFint g x⟩
  have hFi0 : Fi ≠ 0 := by
    intro h0
    have h1 : F v = w := by
      have := hF (Finsupp.single 1 1)
      rwa [orbitMap_single, orbitMap_single, one_smul, one_smul, map_one,
        Module.End.one_apply, map_one, Module.End.one_apply] at this
    have h2 : F v = 0 := by
      have : Fi v = 0 := by rw [h0]; rfl
      exact this
    apply hg₀
    rw [h, ← h1, h2, map_zero, map_zero]
  rcases Representation.IsIrreducible.bijective_or_eq_zero Fi with hb | h0
  · exact ⟨Representation.Equiv.mk (LinearEquiv.ofBijective F hb)
      fun g => LinearMap.ext fun x => hFint g x⟩
  · exact absurd h0 hFi0

end RestrictedTensor

end GroundTheory.Automorphic
