import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.Bridge
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
open MeasureTheory

namespace GlobalTheory

section
variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
  [BorelSpace H] {μ : Measure H} [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
  {Γ : Subgroup H} [Countable Γ] {𝓕 : Set H}

omit [μ.IsMulLeftInvariant] [Countable Γ] in

theorem isFundamentalDomain_image_mul_right (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (y : H) :
    IsFundamentalDomain Γ ((fun h => h * y) '' 𝓕) μ := by
  refine h𝓕.image_of_equiv (Equiv.mulRight y) ?_ (Equiv.refl _) ?_
  · exact (measurePreserving_mul_right μ y⁻¹).quasiMeasurePreserving
  · intro γ h
    simp [Subgroup.smul_def, mul_assoc]

theorem setIntegral_fundamentalDomain_mul_right (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (y : H)
    (u : H → ℂ) (hu : ∀ γ ∈ Γ, ∀ h, u (γ * h) = u h) :
    ∫ h in 𝓕, u (h * y) ∂μ = ∫ h in 𝓕, u h ∂μ := by
  rw [h𝓕.setIntegral_eq (isFundamentalDomain_image_mul_right h𝓕 y) (f := u)
    (fun γ h => hu γ γ.2 h)]
  exact ((measurePreserving_mul_right μ y).setIntegral_image_emb
    (measurableEmbedding_mulRight y) u 𝓕).symm

theorem integrableOn_fundamentalDomain_mul_right (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (y : H)
    (u : H → ℂ) (hu : ∀ γ ∈ Γ, ∀ h, u (γ * h) = u h) (hi : IntegrableOn u 𝓕 μ) :
    IntegrableOn (fun h => u (h * y)) 𝓕 μ := by
  rw [h𝓕.integrableOn_iff (isFundamentalDomain_image_mul_right h𝓕 y) (f := u)
    (fun γ h => hu γ γ.2 h)] at hi
  exact ((measurePreserving_mul_right μ y).integrableOn_image
    (measurableEmbedding_mulRight y)).1 hi

end

theorem setIntegral_kernel_doubleCoset_adjoint :
    ∀ {G H : Type} [Group G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (Γ K : Subgroup H) [Countable Γ] (𝓕 : Set H) (x : H) (A A' : Finset H) (Kn : G → H → ℂ) (F : H → ℂ) (n : ℕ) (c : ℕ → ℂ) (B : ℕ → Finset G), IsFundamentalDomain Γ 𝓕 μ → (∀ a ∈ A, ∃ k₁ ∈ K, ∃ k₂ ∈ K, a = k₁ * x * k₂) → (∀ a ∈ A', ∃ k₁ ∈ K, ∃ k₂ ∈ K, a = k₁ * x⁻¹ * k₂) → A.card = A'.card → (∀ γ ∈ Γ, ∀ h, F (γ * h) = F h) → (∀ k ∈ K, ∀ h, F (h * k) = F h) → (∀ g, ∀ γ ∈ Γ, ∀ h, Kn g (γ * h) = Kn g h) → (∀ g, ∀ k ∈ K, ∀ h, Kn g (h * k) = Kn g h) → (∀ g y, IntegrableOn (fun h => Kn g h * F (h * y)) 𝓕 μ) → (∀ g h, ∑ a ∈ A', Kn g (h * a) = ∑ j ∈ Finset.range n, c j * ∑ b ∈ B j, Kn (g * b) h) → ∀ g, ∫ h in 𝓕, Kn g h * ∑ a ∈ A, F (h * a) ∂μ = ∑ j ∈ Finset.range n, c j * ∑ b ∈ B j, ∫ h in 𝓕, Kn (g * b) h * F h ∂μ := by
  intro G H _ _ _ _ _ _ μ _ _ Γ K _ 𝓕 x A A' Kn F n c B h𝓕 hA hA' hcard hFl hFr hKl hKr hint hker g
  have hu : ∀ γ ∈ Γ, ∀ h, (fun h => Kn g h * F (h * x)) (γ * h) = (fun h => Kn g h * F (h * x)) h := by
    intro γ hγ h
    simp only [hKl g γ hγ, mul_assoc, hFl γ hγ]
  have h1 : ∀ a ∈ A, ∫ h in 𝓕, Kn g h * F (h * a) ∂μ = ∫ h in 𝓕, Kn g h * F (h * x) ∂μ := by
    intro a ha
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hA a ha
    refine Eq.trans ?_ (setIntegral_fundamentalDomain_mul_right h𝓕 k₁ (fun h => Kn g h * F (h * x)) hu)
    congr 1
    funext h
    rw [hKr g k₁ hk₁, ← mul_assoc, hFr k₂ hk₂, ← mul_assoc]
  have h2e : ∀ a ∈ A', ∃ y, (fun h => Kn g (h * a) * F h)
      = fun h => (fun h => Kn g h * F (h * x)) (h * y) := by
    intro a ha
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hA' a ha
    refine ⟨k₁ * x⁻¹, funext fun h => ?_⟩
    have : h * (k₁ * x⁻¹) * x = h * k₁ := by group
    simp only [this]
    rw [hFr k₁ hk₁, ← mul_assoc, hKr g k₂ hk₂]
  have h2 : ∀ a ∈ A', ∫ h in 𝓕, Kn g (h * a) * F h ∂μ = ∫ h in 𝓕, Kn g h * F (h * x) ∂μ := by
    intro a ha
    obtain ⟨y, hy⟩ := h2e a ha
    rw [hy]
    exact setIntegral_fundamentalDomain_mul_right h𝓕 y (fun h => Kn g h * F (h * x)) hu
  have h2i : ∀ a ∈ A', IntegrableOn (fun h => Kn g (h * a) * F h) 𝓕 μ := by
    intro a ha
    obtain ⟨y, hy⟩ := h2e a ha
    rw [hy]
    exact integrableOn_fundamentalDomain_mul_right h𝓕 y (fun h => Kn g h * F (h * x)) hu (hint g x)
  have hi1 : ∀ g, IntegrableOn (fun h => Kn g h * F h) 𝓕 μ := fun g => by
    simpa using hint g 1
  calc ∫ h in 𝓕, Kn g h * ∑ a ∈ A, F (h * a) ∂μ
      = ∑ a ∈ A, ∫ h in 𝓕, Kn g h * F (h * a) ∂μ := by
        simp_rw [Finset.mul_sum]
        exact integral_finset_sum _ fun a _ => hint g a
    _ = ∑ a ∈ A', ∫ h in 𝓕, Kn g (h * a) * F h ∂μ := by
        rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_const, Finset.sum_const,
          hcard]
    _ = ∫ h in 𝓕, ∑ a ∈ A', Kn g (h * a) * F h ∂μ := (integral_finset_sum _ h2i).symm
    _ = ∫ h in 𝓕, ∑ j ∈ Finset.range n, c j * ∑ b ∈ B j, Kn (g * b) h * F h ∂μ := by
        congr 1
        funext h
        rw [← Finset.sum_mul, hker, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_assoc, Finset.sum_mul]
    _ = _ := by
        rw [integral_finset_sum]
        · refine Finset.sum_congr rfl fun j _ => ?_
          rw [integral_const_mul, integral_finset_sum _ fun b _ => hi1 (g * b)]
        · intro j _
          exact (integrable_finset_sum _ fun b _ => hi1 (g * b)).const_mul _

end GlobalTheory
