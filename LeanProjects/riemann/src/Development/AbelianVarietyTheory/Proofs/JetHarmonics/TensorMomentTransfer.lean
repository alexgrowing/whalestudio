import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuotientMeasureAeMemAndMeasurableBesselModelStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsometricBesselSideBoundStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsometricBesselCompareStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorBesselTransferStatement

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselPairing

theorem integrable_inner_of_memLp {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {f g : α → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => ⟪f x, g x⟫_ℂ) μ := by
  refine (L2.integrable_inner (𝕜 := ℂ) (hf.toLp f) (hg.toLp g)).congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2]

theorem pairing : Hyps → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (om : ι → ℂ) (Bm : R.H → Wp) (BI : ∀ I, (RI I).H → Wp) (β : κ → ℂ), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → Function.Injective muI → TensRaw ρ R RI io pr → SideG k r z π u μW μN μG νq → IsBes R z π Bm → (∀ I, IsIsoB (RI I) z π νq (BI I) ∨ β I = 0) → (∀ I, ∀ y ∈ (RI I).sm, Bm (ev Γ R om (fun c => io I c y)) = β I • BI I y) → ∀ I, IsIsoB (RI I) z π νq (BI I) → ∀ y ∈ (RI I).sm, ∀ (a : ι → ℂ), ∀ w ∈ R.sm, ∫ x, ⟪BI I ((RI I).σ (Matrix.of x) y), Formalism.QuantumDeterminants.herm Γ (ρ (Matrix.of x) *ᵥ a) om • Bm (R.σ (Matrix.of x) w)⟫_ℂ ∂νq = β I * ⟪y, ∑ c, pr I c (tm R a w c)⟫_ℂ := by
  intro hH k r ι κ _ _ _ _ ρ Γ d R RI io pr ε mu muI Wp _ _ _ _ z π u μW μN μG νq om Bm BI β hR hRI hinj hT hS hB
    hiso hev I hI y hy a w hw
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hmem : ∀ J, (∑ c, pr J c (tm R a w c)) ∈ (RI J).sm := by
    intro J
    refine (RI J).smSub.sum_mem (fun c _ => ?_)
    exact (hT.pr_sm J c).mem _ (R.smSub.smul_mem (a c) hw)
  have hae := (GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hK k r ε mu R Wp z π u μW μN μG νq hR hS).1
  have hexp := GlobalTheory.T.tensor_bessel_transfer hK k r ι κ ρ Γ d R RI io pr ε mu muI Wp om Bm BI β hR hRI hT hB.1 hB.2.1 hev a w hw
  have hpolI := GlobalTheory.T.isometric_bessel_memLp_and_integral_inner_eq hK k r ε (muI I) (RI I) Wp z π u μW μN μG νq (BI I) (hRI I) hS hI
  have h1 : ∫ x, ⟪BI I ((RI I).σ (Matrix.of x) y),
        Formalism.QuantumDeterminants.herm Γ (ρ (Matrix.of x) *ᵥ a) om • Bm (R.σ (Matrix.of x) w)⟫_ℂ ∂νq
      = ∫ x, ∑ J, β J * ⟪BI I ((RI I).σ (Matrix.of x) y),
        BI J ((RI J).σ (Matrix.of x) (∑ c, pr J c (tm R a w c)))⟫_ℂ ∂νq := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hexp _ hx, inner_sum]
    simp only [inner_smul_right]
  rw [h1, integral_finset_sum]
  · simp only [integral_const_mul]
    rw [Finset.sum_eq_single I]
    · rw [hpolI.2 _ (hmem I) y hy]
    · intro J _ hJ
      rcases hiso J with hJ' | hJ'
      · rw [GlobalTheory.T.isometric_bessel_compare hH k r ε (muI J) (muI I) (RI J) (RI I) Wp z π u μW μN μG νq (BI J) (BI I) (hRI J) (hRI I)
          (fun h => hJ (hinj h)) hS hJ' hI _ (hmem J) y hy, mul_zero]
      · rw [hJ', zero_mul]
    · intro h
      exact absurd (Finset.mem_univ I) h
  · intro J _
    rcases hiso J with hJ' | hJ'
    · exact (integrable_inner_of_memLp (hpolI.1 y hy)
        ((GlobalTheory.T.isometric_bessel_memLp_and_integral_inner_eq hK k r ε (muI J) (RI J) Wp z π u μW μN μG νq (BI J) (hRI J) hS hJ').1 _ (hmem J))).const_mul _
    · simp only [hJ', zero_mul]
      exact integrable_zero _ _ _

end GlobalTheory.BesselPairing
