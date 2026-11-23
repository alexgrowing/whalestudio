import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EntireApplyEqOfPeriodicOfSpanReal

open Set Filter Topology Complex

namespace GlobalTheory

section Log

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem exists_continuous_cexp_eq {f : V → ℂ} (hf : Continuous f) (h0 : ∀ v, f v ≠ 0) :
    ∃ q : V → ℂ, Continuous q ∧ ∀ v, cexp (q v) = f v := by
  have hU : IsSimplyConnected (univ : Set V) := by
    haveI : ContractibleSpace (univ : Set V) := (convex_univ (𝕜 := ℝ)).contractibleSpace ⟨0, trivial⟩
    exact (inferInstance : SimplyConnectedSpace (univ : Set V))
  obtain ⟨q, hq, hq'⟩ := Complex.exists_continuousOn_eqOn_exp_comp hU isOpen_univ
    hf.continuousOn (by rintro ⟨v, -, hv⟩; exact h0 v hv)
  exact ⟨q, continuousOn_univ.1 hq, fun v => hq' (mem_univ v)⟩

theorem differentiable_of_continuous_of_cexp {q : V → ℂ} (hq : Continuous q)
    (hf : Differentiable ℂ fun v => cexp (q v)) : Differentiable ℂ q := by
  intro x
  have hc : Continuous fun v => (q v - q x).im := by fun_prop
  have hev : ∀ᶠ v in 𝓝 x, (q v - q x).im ∈ Ioo (-Real.pi) Real.pi :=
    hc.continuousAt.eventually_mem (isOpen_Ioo.mem_nhds (by simp [Real.pi_pos]))
  have he : q =ᶠ[𝓝 x] fun v => q x + log (cexp (q v) * cexp (-q x)) := by
    filter_upwards [hev] with v hv
    rw [← exp_add, ← sub_eq_add_neg, log_exp hv.1 hv.2.le]
    ring
  refine DifferentiableAt.congr_of_eventuallyEq ?_ he
  refine DifferentiableAt.const_add _ (DifferentiableAt.clog ((hf x).mul_const _) ?_)
  simp [← exp_add]

theorem exists_differentiable_cexp_eq {f : V → ℂ} (hf : Differentiable ℂ f) (h0 : ∀ v, f v ≠ 0) :
    ∃ q : V → ℂ, Differentiable ℂ q ∧ ∀ v, cexp (q v) = f v := by
  obtain ⟨q, hq, hq'⟩ := exists_continuous_cexp_eq hf.continuous h0
  exact ⟨q, differentiable_of_continuous_of_cexp hq (by simpa only [hq'] using hf), hq'⟩

theorem apply_eq_of_continuous_of_cexp_eq_one {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] {φ : X → ℂ} (hφ : Continuous φ) (h : ∀ x, cexp (φ x) = 1) (x y : X) :
    φ x = φ y := by
  have hc : (range φ).Countable := by
    refine (countable_range fun n : ℤ => (n : ℂ) * (2 * Real.pi * I)).mono ?_
    rintro _ ⟨z, rfl⟩
    obtain ⟨n, hn⟩ := exp_eq_one_iff.1 (h z)
    exact ⟨n, hn.symm⟩
  exact hc.isTotallyDisconnected _ Subset.rfl (isPreconnected_range hφ) ⟨x, rfl⟩ ⟨y, rfl⟩

end Log

section Factor

variable {V G : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

theorem sub_eq_of_equivalent_factors (p : G → V) (lin₁ lin₂ : G → V →ₗ[ℂ] ℂ) (c₁ c₂ : G → ℂ)
    {q : V → ℂ} (hq : Continuous q)
    (h : ∀ g v, cexp (lin₁ g v + c₁ g) * cexp (q v) =
      cexp (lin₂ g v + c₂ g) * cexp (q (v + p g))) (g : G) (v : V) :
    q (v + p g) - q v = lin₁ g v - lin₂ g v + (q (p g) - q 0) := by
  have h1 := (lin₁ g).continuous_of_finiteDimensional
  have h2 := (lin₂ g).continuous_of_finiteDimensional
  have := apply_eq_of_continuous_of_cexp_eq_one
    (φ := fun v => lin₁ g v + c₁ g + q v - (lin₂ g v + c₂ g + q (v + p g))) (by fun_prop)
    (fun v => by rw [← exp_eq_exp_iff_exp_sub_eq_one, exp_add _ (q v), h, ← exp_add]) v 0
  simp only [map_zero, zero_add] at this
  linear_combination -this

theorem alternating_eq_of_equivalent_factors (p : G → V) (lin₁ lin₂ : G → V →ₗ[ℂ] ℂ)
    (c₁ c₂ : G → ℂ) {f : V → ℂ} (hf : Continuous f) (h0 : ∀ v, f v ≠ 0)
    (h : ∀ g v, cexp (lin₁ g v + c₁ g) * f v = cexp (lin₂ g v + c₂ g) * f (v + p g)) (g g' : G) :
    lin₁ g (p g') - lin₁ g' (p g) = lin₂ g (p g') - lin₂ g' (p g) := by
  obtain ⟨q, hq, hq'⟩ := exists_continuous_cexp_eq hf h0
  have key := sub_eq_of_equivalent_factors p lin₁ lin₂ c₁ c₂ hq (by simpa only [hq'] using h)
  have h1 := key g (p g')
  have h2 := key g' (p g)
  rw [add_comm (p g)] at h2
  linear_combination h2 - h1

variable [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]

end Factor

section Unimodular

theorem bijective_of_isometry_of_bijective_form {R L L' : Type*} [CommRing R] [Nontrivial R]
    [AddCommGroup L] [Module R L] [Module.Free R L] [Module.Finite R L]
    [AddCommGroup L'] [Module R L'] [Module.Free R L'] [Module.Finite R L']
    (hrk : Module.finrank R L = Module.finrank R L')
    (E : LinearMap.BilinForm R L) (E' : LinearMap.BilinForm R L') (hE : Function.Bijective E)
    (g : L →ₗ[R] L') (hg : ∀ a b, E' (g a) (g b) = E a b) : Function.Bijective g := by
  let e : L ≃ₗ[R] Module.Dual R L := LinearEquiv.ofBijective E hE
  let r : L' →ₗ[R] L := e.symm.toLinearMap ∘ₗ g.dualMap ∘ₗ E'
  have hr : Function.LeftInverse r g := fun a => by
    change e.symm (g.dualMap (E' (g a))) = a
    rw [LinearEquiv.symm_apply_eq]
    ext b
    exact hg a b
  have hi : Function.Injective r :=
    OrzechProperty.injective_of_surjective_of_injective
      (LinearEquiv.ofFinrankEq L' L hrk.symm).toLinearMap r (LinearEquiv.injective _) hr.surjective
  exact ⟨hr.injective, fun y => ⟨r y, hi (hr _)⟩⟩

variable {L L' : Type*} [AddCommGroup L] [AddCommGroup L']

theorem free_finite_finrank_of_lattice_embedding {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (P : L →+ V) (hP : Function.Injective P)
    (hd : DiscreteTopology (range P)) (hs : Submodule.span ℝ (range P) = ⊤) :
    Module.Free ℤ L ∧ Module.Finite ℤ L ∧ Module.finrank ℤ L = Module.finrank ℝ V := by
  let Λ : Submodule ℤ V := LinearMap.range P.toIntLinearMap
  haveI : DiscreteTopology Λ := hd
  haveI : IsZLattice ℝ Λ := ⟨hs⟩
  let e : L ≃ₗ[ℤ] Λ := LinearEquiv.ofInjective P.toIntLinearMap hP
  exact ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm,
    e.finrank_eq.trans (ZLattice.rank ℝ Λ)⟩

theorem bijective_of_image_range_eq {V V' : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
    [Module ℝ V'] [IsScalarTower ℝ ℂ V'] (hdim : Module.finrank ℂ V = Module.finrank ℂ V')
    (h : V →ₗ[ℂ] V') {S : Set V'} (hS : Submodule.span ℝ S = ⊤) (hh : S ⊆ range h) :
    Function.Bijective h := by
  have hs : Function.Surjective h := fun y => by
    have : Submodule.span ℝ S ≤ (LinearMap.range h).restrictScalars ℝ := Submodule.span_le.2 hh
    exact this (hS ▸ Submodule.mem_top)
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hs, hs⟩

variable {V V' : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]
  [NormedAddCommGroup V'] [NormedSpace ℂ V'] [FiniteDimensional ℂ V']
  [NormedSpace ℝ V'] [IsScalarTower ℝ ℂ V']

end Unimodular

end GlobalTheory
