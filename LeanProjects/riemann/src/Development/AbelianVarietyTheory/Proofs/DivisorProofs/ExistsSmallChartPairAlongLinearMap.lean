import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer.ChartPair

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
  {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V}

theorem exists_affine_pt (y : Sp ℂ ⟶ X) : ∃ U : X.Opens, IsAffineOpen U ∧ ⊤ ≤ y ⁻¹ᵁ U := by
  obtain ⟨U, hU, hy, -⟩ := exists_isAffineOpen_mem_and_subset (x := y (default : PrimeSpectrum ℂ)) (U := ⊤) trivial
  refine ⟨U, hU, fun p _ ↦ ?_⟩
  have : p = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  subst this
  exact hy

theorem isOpen_dom (u : Unif F s σ) (U : X.Opens) : IsOpen {p : Tot I g | p.1 ∈ F.V ∧ ⊤ ≤ u.E p ⁻¹ᵁ U} :=
  (u.hol U 0).1

def Good (u : Unif F s σ) (W : Opens (Tot I g)) : Prop :=
  (∀ p ∈ W, p.1 ∈ F.V) ∧ ∃ U : X.Opens, IsAffineOpen U ∧ ∀ p ∈ W, ⊤ ≤ u.E p ⁻¹ᵁ U

def charts (u : Unif F s σ) : Charts F where
  K := {W : Opens (Tot I g) // Good u W}
  W k := k.1
  base k := k.2.1
  le l k' k := ∀ p ∈ k'.1, F.shift l p ∈ k.1
  le_refl k p hp := by rwa [F.shift_zero]
  le_trans {l m k k' k''} h h' p hp := by rw [F.shift_add]; exact h _ (h' p hp)
  maps h := h

end GlobalTheory.AnPer.ChartPair

namespace GlobalTheory.AnPer.ChartPair

variable {I₁ : Type} [Fintype I₁] {g₁ : ℕ} {Λ₁ : Type} [AddCommGroup Λ₁] {F₁ : Fam I₁ g₁ Λ₁}
  {B₁ : Type} [CommRing B₁] {X₁ : Scheme.{0}} {s₁ : X₁ ⟶ Sp B₁} {σ₁ : B₁ →+* Hol F₁.V}
  {I₂ : Type} [Fintype I₂] {g₂ : ℕ} {Λ₂ : Type} [AddCommGroup Λ₂] {F₂ : Fam I₂ g₂ Λ₂}
  {B₂ : Type} [CommRing B₂] {X₂ : Scheme.{0}} {s₂ : X₂ ⟶ Sp B₂} {σ₂ : B₂ →+* Hol F₂.V}

def pairCharts (u₁ : Unif F₁ s₁ σ₁) (u₂ : Unif F₂ s₂ σ₂) (b : (I₁ → ℂ) → I₂ → ℂ)
    (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) (A : Λ₁ →+ Λ₂) : Charts F₁ where
  K := {q : Opens (Tot I₁ g₁) × Opens (Tot I₂ g₂) //
    Good u₁ q.1 ∧ Good u₂ q.2 ∧ ∀ p ∈ q.1, ((b p.1, M p.2) : Tot I₂ g₂) ∈ q.2}
  W k := k.1.1
  base k := k.2.1.1
  le l k' k := (∀ p ∈ k'.1.1, F₁.shift l p ∈ k.1.1) ∧ ∀ p ∈ k'.1.2, F₂.shift (A l) p ∈ k.1.2
  le_refl k := ⟨fun p hp ↦ by rwa [F₁.shift_zero], fun p hp ↦ by rwa [map_zero, F₂.shift_zero]⟩
  le_trans {l m k k' k''} h h' := ⟨fun p hp ↦ by rw [F₁.shift_add]; exact h.1 _ (h'.1 p hp),
    fun p hp ↦ by rw [map_add, F₂.shift_add]; exact h.2 _ (h'.2 p hp)⟩
  maps h := h.1

theorem exists_pair (u₁ : Unif F₁ s₁ σ₁) (u₂ : Unif F₂ s₂ σ₂) (b : (I₁ → ℂ) → I₂ → ℂ)
    (hb : AnalyticOnNhd ℂ b F₁.V) (hbV : ∀ z ∈ F₁.V, b z ∈ F₂.V)
    (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) (A : Λ₁ →+ Λ₂)
    (hτ : ∀ l, ∀ z ∈ F₁.V, F₂.τ (A l) (b z) = M (F₁.τ l z)) :
    ∃ (K₁ : Charts F₁) (K₂ : Charts F₂) (κ : K₁.K → K₂.K), K₁.Rich ∧
      (∀ k, ∃ U, IsAffineOpen U ∧ ∀ p ∈ K₁.W k, ⊤ ≤ u₁.E p ⁻¹ᵁ U) ∧
      (∀ k, ∃ U, IsAffineOpen U ∧ ∀ p ∈ K₂.W k, ⊤ ≤ u₂.E p ⁻¹ᵁ U) ∧
      (∀ k, ∀ p ∈ K₁.W k, ((b p.1, M p.2) : Tot I₂ g₂) ∈ K₂.W (κ k)) ∧
      ∀ l k' k, K₁.le l k' k → K₂.le (A l) (κ k') (κ k) := by
  let Φ : Tot I₁ g₁ → Tot I₂ g₂ := fun p ↦ (b p.1, M p.2)
  have hΦ : ∀ l (p : Tot I₁ g₁), p.1 ∈ F₁.V → Φ (F₁.shift l p) = F₂.shift (A l) (Φ p) := by
    intro l p hp
    simp only [Φ, Fam.shift, map_add, hτ l p.1 hp]
  have hcont : ContinuousOn Φ {p : Tot I₁ g₁ | p.1 ∈ F₁.V} :=
    (hb.continuousOn.comp continuous_fst.continuousOn fun p hp ↦ hp).prodMk
      (M.continuous_of_finiteDimensional.comp continuous_snd).continuousOn
  refine ⟨pairCharts u₁ u₂ b M A, charts u₂, fun k ↦ ⟨k.1.2, k.2.2.1⟩, ⟨?_, ?_⟩,
    fun k ↦ k.2.1.2, fun k ↦ k.2.2, fun k ↦ k.2.2.2, fun l k' k h ↦ h.2⟩
  · intro p hp
    obtain ⟨U₁, hU₁, h₁⟩ := exists_affine_pt (u₁.E p)
    obtain ⟨U₂, hU₂, h₂⟩ := exists_affine_pt (u₂.E (Φ p))
    let O₁ := {q : Tot I₁ g₁ | q.1 ∈ F₁.V ∧ ⊤ ≤ u₁.E q ⁻¹ᵁ U₁}
    let O₂ := {q : Tot I₂ g₂ | q.1 ∈ F₂.V ∧ ⊤ ≤ u₂.E q ⁻¹ᵁ U₂}
    have hO₂ : IsOpen O₂ := isOpen_dom u₂ U₂
    have hO₁ : IsOpen (O₁ ∩ Φ ⁻¹' O₂) :=
      (hcont.mono fun q hq ↦ hq.1).isOpen_inter_preimage (isOpen_dom u₁ U₁) hO₂
    refine ⟨⟨(⟨O₁ ∩ Φ ⁻¹' O₂, hO₁⟩, ⟨O₂, hO₂⟩),
      ⟨fun q hq ↦ hq.1.1, U₁, hU₁, fun q hq ↦ hq.1.2⟩, ⟨fun q hq ↦ hq.1, U₂, hU₂, fun q hq ↦ hq.2⟩,
      fun q hq ↦ hq.2⟩, ?_⟩
    exact ⟨⟨hp, h₁⟩, hbV _ hp, h₂⟩
  · intro l k₁ k₂ p hp hp'
    have hb₁ := k₁.2.1.1
    have hb₂ := k₁.2.2.1.1
    have o₁ : IsOpen ((k₁.1.1 : Set (Tot I₁ g₁)) ∩ F₁.shift l ⁻¹' k₂.1.1) :=
      (F₁.shift_analytic l hb₁).continuousOn.isOpen_inter_preimage k₁.1.1.isOpen k₂.1.1.isOpen
    have o₂ : IsOpen ((k₁.1.2 : Set (Tot I₂ g₂)) ∩ F₂.shift (A l) ⁻¹' k₂.1.2) :=
      (F₂.shift_analytic (A l) hb₂).continuousOn.isOpen_inter_preimage k₁.1.2.isOpen k₂.1.2.isOpen
    obtain ⟨U₁, hU₁, h₁⟩ := k₁.2.1.2
    obtain ⟨U₂, hU₂, h₂⟩ := k₁.2.2.1.2
    refine ⟨⟨(⟨_, o₁⟩, ⟨_, o₂⟩), ⟨fun q hq ↦ hb₁ q hq.1, U₁, hU₁, fun q hq ↦ h₁ q hq.1⟩,
      ⟨fun q hq ↦ hb₂ q hq.1, U₂, hU₂, fun q hq ↦ h₂ q hq.1⟩, fun q hq ↦ ⟨k₁.2.2.2 q hq.1, ?_⟩⟩,
      ⟨hp, hp'⟩, ⟨fun q hq ↦ ?_, fun q hq ↦ ?_⟩, ⟨fun q hq ↦ hq.2, fun q hq ↦ hq.2⟩⟩
    · show F₂.shift (A l) (Φ q) ∈ k₂.1.2
      rw [← hΦ l q (hb₁ q hq.1)]
      exact k₂.2.2.2 _ hq.2
    · rw [F₁.shift_zero]; exact hq.1
    · rw [map_zero, F₂.shift_zero]; exact hq.1

end GlobalTheory.AnPer.ChartPair
