import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi

theorem exists_cInd_restrict : ∀ {G G' W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group G'] [TopologicalSpace G']
    [IsTopologicalGroup G'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (H : Subgroup G) (H' : Subgroup G') (ι : G' →* G) (σ : Representation ℂ H W) (σ' : Representation ℂ H' W')
    (q : W →ₗ[ℂ] W'), Continuous ι → (∀ x, x ∈ H' ↔ ι x ∈ H) →
    (∀ (h : H') (hh : ι h ∈ H) (w : W), q (σ ⟨ι h, hh⟩ w) = σ' h (q w)) →
    IsClosed {g : G | ∃ h ∈ H, ∃ x : G', g = h * ι x} →
    (∀ K' ∈ 𝓝 (1 : G'), ∃ K ∈ 𝓝 (1 : G), ∀ x : G', ∀ h ∈ H, ∀ κ ∈ K, ι x = h * κ →
      ∃ h' ∈ H', ∃ κ' ∈ K', x = h' * κ') →
    (∃ K' ∈ 𝓝 (1 : G'), IsCompact K') →
    ∀ f : cIndSpace H σ, ∃ F : cIndSpace H' σ', ∀ x, F.1.1.1 x = q (f.1.1.1 (ι x)) := by
  intro G G' W W' _ _ _ _ _ _ _ _ _ _ H H' ι σ σ' q hι hH hq hS hemb hcomp f
  obtain ⟨K', hK'n, hK'c⟩ := hcomp
  obtain ⟨L, hLo, hL⟩ := cInd_right_inv H σ f
  let b : G' → W' := fun x => q (f.1.1.1 (ι x))
  have hind : b ∈ indSpace H' σ' := by
    intro h x
    have hh : ι (h : G') ∈ H := (hH _).1 h.2
    have e : f.1.1.1 (((⟨ι h, hh⟩ : H) : G) * ι x) = σ ⟨ι h, hh⟩ (f.1.1.1 (ι x)) := f.1.1.2 ⟨ι h, hh⟩ (ι x)
    show q (f.1.1.1 (ι ((h : G') * x))) = σ' h (q (f.1.1.1 (ι x)))
    rw [map_mul, ← hq h hh]
    exact congrArg q e
  have hsm : (⟨b, hind⟩ : indSpace H' σ') ∈ smoothPart (ind H' σ') := by
    refine GlobalTheory.CompanionTheory.BZMirOnto.isOpen_fixed_of_subgroup (ind H' σ') (L.comap ι)
      (hLo.preimage hι) _ fun x hx => ?_
    apply Subtype.ext
    funext g
    show q (f.1.1.1 (ι (g * x))) = q (f.1.1.1 (ι g))
    rw [map_mul, hL (ι g) (ι x) hx]
  have hc : (⟨⟨b, hind⟩, hsm⟩ : smoothPart (ind H' σ')) ∈ cIndSpace H' σ' := by
    obtain ⟨C, hC, hf⟩ := f.2
    have hD : IsCompact (C ∩ {g : G | ∃ h ∈ H, ∃ x : G', g = h * ι x}) := hC.inter_right hS
    have key : ∃ C' : Set G', IsCompact C' ∧ ∀ (x : G'), ∀ a ∈ H,
        ∀ n ∈ C ∩ {g : G | ∃ h ∈ H, ∃ x : G', g = h * ι x}, ι x = a * n →
        ∃ h' ∈ H', ∃ c' ∈ C', x = h' * c' := by
      refine hD.induction_on
        (p := fun A => ∃ C' : Set G', IsCompact C' ∧ ∀ (x : G'), ∀ a ∈ H, ∀ n ∈ A, ι x = a * n →
          ∃ h' ∈ H', ∃ c' ∈ C', x = h' * c') ?_ ?_ ?_ ?_
      · exact ⟨∅, isCompact_empty, fun _ _ _ n hn => absurd hn (Set.notMem_empty n)⟩
      · rintro A B hAB ⟨C', hC', h⟩
        exact ⟨C', hC', fun x a ha n hn e => h x a ha n (hAB hn) e⟩
      · rintro A B ⟨C₁, hC₁, h₁⟩ ⟨C₂, hC₂, h₂⟩
        refine ⟨C₁ ∪ C₂, hC₁.union hC₂, fun x a ha n hn e => ?_⟩
        rcases hn with hn | hn
        · obtain ⟨h', hh', c', hc', e'⟩ := h₁ x a ha n hn e
          exact ⟨h', hh', c', Or.inl hc', e'⟩
        · obtain ⟨h', hh', c', hc', e'⟩ := h₂ x a ha n hn e
          exact ⟨h', hh', c', Or.inr hc', e'⟩
      · rintro c ⟨-, h₀, hh₀, s, rfl⟩
        obtain ⟨K, hK, hKe⟩ := hemb K' hK'n
        have hcont : Continuous fun n : G => h₀⁻¹ * n * (ι s)⁻¹ := by fun_prop
        have hN : (fun n : G => h₀⁻¹ * n * (ι s)⁻¹) ⁻¹' K ∈ 𝓝 (h₀ * ι s) := by
          apply hcont.continuousAt.preimage_mem_nhds
          have e : h₀⁻¹ * (h₀ * ι s) * (ι s)⁻¹ = 1 := by group
          rw [e]
          exact hK
        refine ⟨_, mem_nhdsWithin_of_mem_nhds hN, (fun y => y * s) '' K',
          hK'c.image (by fun_prop), fun x a ha n hn e => ?_⟩
        have hn' : h₀⁻¹ * n * (ι s)⁻¹ ∈ K := hn
        have e2 : ι (x * s⁻¹) = (a * h₀) * (h₀⁻¹ * n * (ι s)⁻¹) := by
          rw [map_mul, map_inv, e]
          group
        obtain ⟨h', hh', κ', hκ', e3⟩ := hKe _ _ (mul_mem ha hh₀) _ hn' e2
        refine ⟨h', hh', κ' * s, ⟨κ', hκ', rfl⟩, ?_⟩
        rw [← mul_assoc, ← e3]
        group
    obtain ⟨C', hC', hkey⟩ := key
    refine ⟨C', hC', fun x hx => ?_⟩
    have hne : f.1.1.1 (ι x) ≠ 0 := by
      intro h0
      apply hx
      show q (f.1.1.1 (ι x)) = 0
      rw [h0, map_zero]
    obtain ⟨a, ha, c, hcC, e⟩ := hf (ι x) hne
    refine hkey x a ha c ⟨hcC, a⁻¹, inv_mem ha, x, ?_⟩ e
    rw [e]
    group
  exact ⟨⟨⟨⟨b, hind⟩, hsm⟩, hc⟩, fun x => rfl⟩

end GlobalTheory.CompanionTheory.LeibPhi

end
