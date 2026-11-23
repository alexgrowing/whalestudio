import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLiftIsLiftPrincipalLevelDatumRealisation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypePlacesIsSplitNonconjugateOfAdmissible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumSmallerLevel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqVolMulSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.ClassRefineBridge

open GlobalTheory.ClassRefine
open scoped Classical

variable {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G)

theorem injective_of_isReps {J : Subgroup G} {I : Type} {y : I → G} (hy : Bridge.IsReps ι J y) :
    Function.Injective y := by
  intro i j hij
  have h1 : ∃ (γ : Γ) (k : J), y i = ι γ * y i * k := ⟨1, 1, by simp⟩
  have h2 : ∃ (γ : Γ) (k : J), y i = ι γ * y j * k := ⟨1, 1, by simp [hij]⟩
  exact (hy (y i)).unique h1 h2

theorem image_reps {J : Subgroup G} {I : Type} [Fintype I] {y : I → G} (hy : Bridge.IsReps ι J y) :
    ∀ g : G, ∃! t, t ∈ Finset.univ.image y ∧ ∃ (γ : ι.range) (κ : G), κ ∈ J ∧ g = (γ : G) * t * κ := by
  intro g
  obtain ⟨i, ⟨γ, k, e⟩, hu⟩ := hy g
  refine ⟨y i, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ⟨ι γ, γ, rfl⟩, k, k.2, e⟩, ?_⟩
  rintro t ⟨ht, ⟨_, δ, rfl⟩, κ, hκ, e'⟩
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 ht
  rw [hu j ⟨δ, ⟨κ, hκ⟩, e'⟩]

theorem card_stab_eq (hι : Function.Injective ι) (J : Subgroup G) (t : G) :
    Nat.card (Bridge.stab ι J t) = Nat.card (stabQ ι.range J t) := by
  refine Nat.card_congr (Equiv.ofBijective (fun γ => ⟨⟨ι γ, γ, rfl⟩, ?_⟩) ⟨?_, ?_⟩)
  · rw [mem_stabQ]; exact (Bridge.mem_stab ι).1 γ.2
  · intro a b h
    apply Subtype.ext
    apply hι
    have := congrArg (fun x : stabQ ι.range J t => ((x : ι.range) : G)) h
    simpa using this
  · rintro ⟨⟨_, γ, rfl⟩, hq⟩
    refine ⟨⟨γ, (Bridge.mem_stab ι).2 (mem_stabQ.1 hq)⟩, rfl⟩

theorem sum_image_eq {I : Type} [Fintype I] {y : I → G} (hy : Function.Injective y) (f : G → ℂ) :
    ∑ i, f (y i) = ∑ t ∈ Finset.univ.image y, f t := by
  rw [Finset.sum_image (fun a _ b _ h => hy h)]

theorem sum_isReps_refine : ∀ {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G), Function.Injective ι → ∀ {J J₀ : Subgroup G}, J₀ ≤ J →
    ∀ {F : Finset G}, (∀ u ∈ F, u ∈ J) → (∀ κ ∈ J, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ J₀) →
    ∀ {I₀ : Type} [Fintype I₀] (y₀ : I₀ → G), Bridge.IsReps ι J₀ y₀ → ∀ {I : Type} [Fintype I] (y : I → G), Bridge.IsReps ι J y →
    ∀ (Φ : G → ℂ), (∀ γ g, Φ (ι γ * g) = Φ g) → (∀ k ∈ J₀, ∀ g, Φ (g * k) = Φ g) →
    ∑ i, ((Nat.card (Bridge.stab ι J₀ (y₀ i)) : ℂ))⁻¹ * Φ (y₀ i) =
      ∑ i, ((Nat.card (Bridge.stab ι J (y i)) : ℂ))⁻¹ * ∑ u ∈ F, Φ (y i * u) := by
  intro G Γ _ _ ι hι J J₀ hJ F hF hFu I₀ _ y₀ hy₀ I _ y hy Φ hl hr
  have key := sum_classReps_refine (Q := ι.range) hJ (image_reps ι hy) (image_reps ι hy₀) Φ
    (by rintro ⟨_, γ, rfl⟩ g; exact hl γ g) hr hF hFu
  simp only [card_stab_eq ι hι]
  rw [sum_image_eq (injective_of_isReps ι hy₀) (fun t => ((Nat.card (stabQ ι.range J₀ t) : ℂ))⁻¹ * Φ t),
    sum_image_eq (injective_of_isReps ι hy) (fun t => ((Nat.card (stabQ ι.range J t) : ℂ))⁻¹ * ∑ u ∈ F, Φ (t * u))]
  exact key

end GlobalTheory.ClassRefineBridge
