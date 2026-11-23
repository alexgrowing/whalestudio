import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatMobiusBasicLawsStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
open Filter Topology

namespace GlobalTheory.KZ.Germ

theorem isOpen_Hs : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

theorem isPreconnected_Hs : IsPreconnected Hs := (convex_halfSpace_im_gt 0).isPreconnected

theorem eventually_of_germ_eq {φ ψ : ℂ → ℂ} (h : (φ : Mero) = (ψ : Mero)) :
    ∀ τ ∈ Hs, ∀ᶠ z in 𝓝[≠] τ, φ z = ψ z := by
  intro τ hτ
  have h1 := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 (Filter.Germ.coe_eq.mp h)) τ hτ
  have h2 : Hs ∈ 𝓝[≠] τ := mem_nhdsWithin_of_mem_nhds (isOpen_Hs.mem_nhds hτ)
  filter_upwards [h1, h2] with z hz1 hz2
  rcases hz1 with hz | hz
  · exact hz
  · exact absurd hz2 hz

theorem eq_zero_or_eq_zero {a b : ℂ → ℂ} (ha : DifferentiableOn ℂ a Hs) (hb : DifferentiableOn ℂ b Hs)
    (h : ∀ z ∈ Hs, a z * b z = 0) : (∀ z ∈ Hs, a z = 0) ∨ (∀ z ∈ Hs, b z = 0) := by
  by_cases hA : ∀ z ∈ Hs, a z = 0
  · exact Or.inl hA
  · right
    push_neg at hA
    obtain ⟨z₀, hz₀, hne⟩ := hA
    have hcont : ContinuousAt a z₀ := (ha.continuousOn).continuousAt (isOpen_Hs.mem_nhds hz₀)
    have hev : ∀ᶠ z in 𝓝 z₀, a z ≠ 0 := hcont.eventually_ne hne
    have hb0 : b =ᶠ[𝓝 z₀] 0 := by
      filter_upwards [hev, isOpen_Hs.mem_nhds hz₀] with z hz1 hz2
      have := h z hz2
      simpa [hz1] using this
    intro z hz
    exact (hb.analyticOnNhd isOpen_Hs).eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Hs hz₀ hb0 hz

theorem exists_eq_zero_of_prod {ι : Type} [DecidableEq ι] (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, DifferentiableOn ℂ (f i) Hs) (h : ∀ z ∈ Hs, ∏ i ∈ s, f i z = 0) :
    ∃ i ∈ s, ∀ z ∈ Hs, f i z = 0 := by
  induction s using Finset.induction_on with
  | empty =>
    exfalso
    have hI : Complex.I ∈ Hs := by show (0 : ℝ) < Complex.I.im; simp
    simpa using h _ hI
  | insert j s hj ih =>
    have hP : DifferentiableOn ℂ (fun z => ∏ i ∈ s, f i z) Hs := by
      have := DifferentiableOn.finset_prod (u := s) (f := f) (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      rw [show (fun z => ∏ i ∈ s, f i z) = ∏ i ∈ s, f i from by funext z; simp [Finset.prod_apply]]
      exact this
    rcases eq_zero_or_eq_zero (hf j (Finset.mem_insert_self j s)) hP
        (fun z hz => by have := h z hz; rwa [Finset.prod_insert hj] at this) with h1 | h1
    · exact ⟨j, Finset.mem_insert_self j s, h1⟩
    · obtain ⟨i, hi, hi'⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) h1
      exact ⟨i, Finset.mem_insert_of_mem hi, hi'⟩

theorem tendsto_mob (g : GQ) {x : ℂ} (hx : x ∈ Hs) : Tendsto (mob g) (𝓝[≠] x) (𝓝[≠] (mob g x)) := by
  obtain ⟨hH, hmul, hone, hdiff, -, -⟩ := GlobalTheory.T.glTwoPosRatMobius_basic_laws
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · exact ((hdiff g).continuousOn.continuousAt (isOpen_Hs.mem_nhds hx)).tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (isOpen_Hs.mem_nhds hx)] with z hz1 hz2
    intro heq
    apply hz1
    show z = x
    have e1 : mob g⁻¹ (mob g z) = z := by rw [← hmul _ _ z hz2, inv_mul_cancel, hone]
    have e2 : mob g⁻¹ (mob g x) = x := by rw [← hmul _ _ x hx, inv_mul_cancel, hone]
    have : mob g z = mob g x := heq
    rw [← e1, this, e2]

theorem germ_comp (g : GQ) (φ ψ : ℂ → ℂ) (h : (φ : Mero) = (ψ : Mero)) :
    ((fun z => φ (mob g z) : ℂ → ℂ) : Mero) = ((fun z => ψ (mob g z) : ℂ → ℂ) : Mero) := by
  obtain ⟨hH, -, -, -, -, -⟩ := GlobalTheory.T.glTwoPosRatMobius_basic_laws
  apply Filter.Germ.coe_eq.mpr
  apply mem_codiscreteWithin_iff_forall_mem_nhdsNE.2
  intro x hx
  have h1 := (tendsto_mob g hx).eventually (eventually_of_germ_eq h (mob g x) (hH g x hx))
  filter_upwards [h1] with z hz
  exact Or.inl hz

theorem main : (∀ a b : ℂ → ℂ, DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (((a : Mero) = (b : Mero)) ↔ ∀ z ∈ Hs, a z = b z)) ∧ (∀ a b : ℂ → ℂ, DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (∀ z ∈ Hs, a z * b z = 0) → (∀ z ∈ Hs, a z = 0) ∨ (∀ z ∈ Hs, b z = 0)) ∧ (∀ (g : GQ) (φ ψ : ℂ → ℂ), (φ : Mero) = (ψ : Mero) → ((fun z => φ (mob g z) : ℂ → ℂ) : Mero) = ((fun z => ψ (mob g z) : ℂ → ℂ) : Mero)) ∧ (∀ (φ ψ : ℂ → ℂ), (φ : Mero) = (ψ : Mero) → ∀ τ ∈ Hs, ∀ᶠ z in nhdsWithin τ {τ}ᶜ, φ z = ψ z) ∧ (∀ (m : ℕ) (a b : ℂ → ℂ), 0 < m → DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (∀ z ∈ Hs, a z ^ m = b z ^ m) → ∃ k : ℕ, ∀ z ∈ Hs, a z = Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / (m : ℂ)) * b z) := by
  refine ⟨?_, fun a b ha hb h => eq_zero_or_eq_zero ha hb h, germ_comp, fun φ ψ h => eventually_of_germ_eq h, ?_⟩
  · intro a b ha hb
    constructor
    · intro hab z hz
      have hI : Complex.I ∈ Hs := by show (0 : ℝ) < Complex.I.im; simp
      exact (ha.analyticOnNhd isOpen_Hs).eqOn_of_preconnected_of_frequently_eq (hb.analyticOnNhd isOpen_Hs)
        isPreconnected_Hs hI (eventually_of_germ_eq hab _ hI).frequently hz
    · intro h
      apply Filter.Germ.coe_eq.mpr
      filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz
      exact h z hz
  · intro m a b hm ha hb h
    have hm0 : m ≠ 0 := hm.ne'
    haveI : NeZero m := ⟨hm0⟩
    have hζ := Complex.isPrimitiveRoot_exp m hm0
    obtain ⟨ξ, hξ, hξ'⟩ := exists_eq_zero_of_prod (Polynomial.nthRootsFinset m (1 : ℂ)) (fun ξ z => a z - ξ * b z)
      (fun ξ _ => ha.sub (hb.const_mul ξ))
      (fun z hz => by rw [← hζ.pow_sub_pow_eq_prod_sub_mul (a z) (b z) hm, h z hz, sub_self])
    have hξm : ξ ^ m = 1 := (Polynomial.mem_nthRootsFinset hm (1 : ℂ)).1 hξ
    obtain ⟨k, -, hk⟩ := hζ.eq_pow_of_pow_eq_one hξm
    refine ⟨k, fun z hz => ?_⟩
    have e : Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / (m : ℂ)) = ξ := by
      rw [← hk, ← Complex.exp_nat_mul]; congr 1; ring
    rw [e]
    exact sub_eq_zero.mp (hξ' z hz)

end GlobalTheory.KZ.Germ
