import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe

namespace GlobalTheory.DoubleCosetIndicatorSum

theorem mul_mem_doubleCoset {G : Type} [Group G] {K : Subgroup G} {a g k : G}
    (hg : g ∈ DoubleCoset.doubleCoset a (K : Set G) (K : Set G)) (hk : k ∈ K) :
    g * k ∈ DoubleCoset.doubleCoset a (K : Set G) (K : Set G) := by
  obtain ⟨h, hh, k', hk', rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
  exact DoubleCoset.mem_doubleCoset.2 ⟨h, hh, k' * k, K.mul_mem hk' hk, mul_assoc _ _ _⟩

private theorem dosetInd_smul_eq_sum_filter {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} {K : Subgroup G} {x : V} (hx : x ∈ GlobalTheory.PRep.fixed ρ K) {a : G} {R : Finset G}
    (hR : ∀ γ ∈ R, γ ∈ DoubleCoset.doubleCoset a (K : Set G) (K : Set G))
    (hU : ∀ g ∈ DoubleCoset.doubleCoset a (K : Set G) (K : Set G), ∃! γ : G, γ ∈ R ∧ γ⁻¹ * g ∈ K)
    [DecidableEq (G ⧸ K)] (c : G ⧸ K) :
    Formalism.UG.dosetInd ℂ K a (Quotient.out c) • ρ (Quotient.out c) x =
      ∑ γ ∈ R.filter (fun γ : G => (γ : G ⧸ K) = c), ρ γ x := by
  have hfix : ∀ k ∈ K, ρ k x = x := GlobalTheory.LGrp.mem_fixed.1 hx

  have hmk : ∀ γ : G, ((γ : G ⧸ K) = c ↔ γ⁻¹ * Quotient.out c ∈ K) := by
    intro γ
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
  by_cases hc : Quotient.out c ∈ DoubleCoset.doubleCoset a (K : Set G) (K : Set G)
  ·
    rw [Formalism.UG.P.dosetInd_of_mem ℂ K a _ hc, one_smul]
    obtain ⟨γ₀, ⟨hγ₀R, hγ₀K⟩, huniq⟩ := hU _ hc
    have hfil : R.filter (fun γ : G => (γ : G ⧸ K) = c) = {γ₀} := by
      ext γ
      simp only [Finset.mem_filter, Finset.mem_singleton, hmk]
      constructor
      · rintro ⟨hγR, hγK⟩
        exact huniq γ ⟨hγR, hγK⟩
      · rintro rfl
        exact ⟨hγ₀R, hγ₀K⟩
    rw [hfil, Finset.sum_singleton]
    calc ρ (Quotient.out c) x = ρ (γ₀ * (γ₀⁻¹ * Quotient.out c)) x := by rw [mul_inv_cancel_left]
      _ = ρ γ₀ (ρ (γ₀⁻¹ * Quotient.out c) x) := by rw [map_mul, Module.End.mul_apply]
      _ = ρ γ₀ x := by rw [hfix _ hγ₀K]
  ·
    rw [Formalism.UG.P.dosetInd_of_not_mem ℂ K a _ hc, zero_smul]
    refine (Finset.sum_eq_zero fun γ hγ => ?_).symm
    rw [Finset.mem_filter, hmk] at hγ
    refine absurd ?_ hc
    have h := mul_mem_doubleCoset (hR γ hγ.1) hγ.2
    rwa [mul_inv_cancel_left] at h

theorem main : (let d1 : {G V : Type} → [inst : Group G] → [inst_1 : AddCommGroup V] → [inst_2 : Module ℂ V] → Representation ℂ G V → Subgroup G → (G → ℂ) → V → V := @(fun {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G) (h : G → ℂ) (x : V) ↦ ∑ᶠ (c : G ⧸ K), h (Quotient.out c) • ((ρ : G → V →ₗ[ℂ] V) (Quotient.out c) : V → V) x); ∀ {G V : Type} [inst : Group G] [inst_1 : AddCommGroup V] [inst_2 : Module ℂ V] {ρ : Representation ℂ G V} {K : Subgroup G} {x : V}, x ∈ GlobalTheory.PRep.fixed ρ K → ∀ {a : G} {R : Finset G}, (∀ γ ∈ R, γ ∈ DoubleCoset.doubleCoset a (↑K : Set G) (↑K : Set G)) → (∀ g ∈ DoubleCoset.doubleCoset a (↑K : Set G) (↑K : Set G), ∃! γ : G, γ ∈ R ∧ γ⁻¹ * g ∈ K) → d1 ρ K (Formalism.UG.dosetInd ℂ K a) x = ∑ γ ∈ R, ((ρ : G → V →ₗ[ℂ] V) γ : V → V) x) := by
  intro d1 G V _ _ _ ρ K x hx a R hR hU
  classical
  show ∑ᶠ c : G ⧸ K, Formalism.UG.dosetInd ℂ K a (Quotient.out c) • ρ (Quotient.out c) x = ∑ γ ∈ R, ρ γ x
  rw [finsum_congr (dosetInd_smul_eq_sum_filter hx hR hU)]
  rw [finsum_eq_sum_of_support_subset (s := R.image fun γ : G => (γ : G ⧸ K))]
  · exact Finset.sum_fiberwise_of_maps_to (fun γ hγ => Finset.mem_image_of_mem _ hγ) _
  · intro c hc
    obtain ⟨γ, hγ, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero (Function.mem_support.1 hc)
    rw [Finset.mem_filter] at hγ
    exact Finset.mem_image.2 ⟨γ, hγ.1, hγ.2⟩

end GlobalTheory.DoubleCosetIndicatorSum
