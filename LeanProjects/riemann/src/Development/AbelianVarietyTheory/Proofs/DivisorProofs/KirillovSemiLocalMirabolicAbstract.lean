import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerInfMemLocSpan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiLocalKirillovArchimedeanKernelComplexPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqOnMirabolicOfSlicesFinitePlacesStatement

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

namespace GlobalTheory.JSW.MirSemi

set_option maxHeartbeats 1000000 in

theorem kirillov_semiLocal : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (b : GA E (m + 1) → ℂ), (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ GlobalTheory.JSW.mirS E S m, b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), u⁻¹ * p ∈ C) → (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (m + 1) u) = b g) → (∀ g, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chart b g) (invSet E (m + 1))) → ∀ 𝒲 : Submodule ℂ (GA E (m + 1) → ℂ), (∀ W ∈ 𝒲, ∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ W ∈ 𝒲, ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S, (fun g => W (g * h)) ∈ 𝒲) → (∀ W ∈ 𝒲, ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin (m + 1)) (Cinf E)), GlobalTheory.JSW.IsRapidInf ν k γ → GlobalTheory.JSW.kerInf ν k γ W ∈ 𝒲) → (∀ W ∈ 𝒲, ∀ g, Continuous (fun y : GL (Fin (m + 1)) (Cinf E) => W (g * infGL E (m + 1) y)) ∧ ∃ (C : ℝ) (N : ℕ), ∀ y, ‖W (g * infGL E (m + 1) y)‖ ≤ C * height y ^ N) → (∀ W ∈ 𝒲, ∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, W (g * finGL E (m + 1) u) = W g) → (∃ W ∈ 𝒲, ∃ p ∈ GlobalTheory.JSW.mirS E S m, W p ≠ 0) → ∃ W ∈ 𝒲, ∀ p ∈ GlobalTheory.JSW.mirS E S m, W p = b p := by
  intro E _ _ _ m S b hb hC hU hsm 𝒲 h1 h2 h3 h4 h5 hne
  obtain ⟨W₀, hW₀, p₀, hp₀, hne₀⟩ := hne
  refine GlobalTheory.T.exists_eq_on_mirabolic_of_slices_finitePlaces E m S b 𝒲 hb hC hU h1 h2 h5 fun q hq hq1 => ?_
  have hh : q⁻¹ * p₀ ∈ GlobalTheory.JSW.supS E (m + 1) S := by
    intro w hw
    rw [map_mul, map_inv, hq.1 w hw, hp₀.1 w hw, inv_one, one_mul]
  have hW' := h2 W₀ hW₀ _ hh
  have hq0 : (fun g => W₀ (g * (q⁻¹ * p₀))) q ≠ 0 := by
    simpa [← mul_assoc] using hne₀
  obtain ⟨X, _, ν, _, k, γ, hk, hK⟩ :=
    GlobalTheory.T.semiLocal_kirillov_archimedean_kernel_complexPlaces E m S b _ q hb hC (hsm q) (h1 _ hW') (h4 _ hW' q).1 (h4 _ hW' q).2 hq1 hq0
  exact ⟨_, h3 _ hW' X ν k γ hk, hK⟩

end GlobalTheory.JSW.MirSemi
