import Mathlib
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.QuotientMeasureAeMemAndMeasurableBesselModelStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsometricBesselSideBoundStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsometricBesselCompareStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TensorBesselTransferStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselPairing

theorem integrable_inner_of_memLp {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {f g : α → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => ⟪f x, g x⟫_ℂ) μ := by
  have h := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (hf.toLp f) (hg.toLp g)
  refine h.congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  rw [hfx, hgx]

private theorem add_mem_sm {k r : ℕ} (R : BranchingSupport.Rep k r) {v w : R.H} (hv : v ∈ R.sm) (hw : w ∈ R.sm) :
    v + w ∈ R.sm := by
  simp only [BranchingSupport.Rep.sm, PI.UpqRep.smoothVecs, Set.mem_setOf_eq, PI.UpqRep.IsSmoothVec] at hv hw ⊢
  letI : NormedAddCommGroup (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := Matrix.normedSpace
  intro g₀ h₀
  obtain ⟨U1, F1, hU1, h1, hF1, e1⟩ := hv g₀ h₀
  obtain ⟨U2, F2, hU2, h2, hF2, e2⟩ := hw g₀ h₀
  refine ⟨U1 ∩ U2, fun x => F1 x + F2 x, hU1.inter hU2, ⟨h1, h2⟩,
    (hF1.mono Set.inter_subset_left).add (hF2.mono Set.inter_subset_right), fun g hg hgH => ?_⟩
  show (R.σ g) (v + w) = F1 g + F2 g
  rw [map_add]
  exact congrArg₂ (· + ·) (e1 g hg.1 hgH) (e2 g hg.2 hgH)

private theorem smul_mem_sm' {k r : ℕ} (R : BranchingSupport.Rep k r) (c : ℂ) {v : R.H} (hv : v ∈ R.sm) :
    c • v ∈ R.sm := by
  simp only [BranchingSupport.Rep.sm, PI.UpqRep.smoothVecs, Set.mem_setOf_eq, PI.UpqRep.IsSmoothVec] at hv ⊢
  letI : NormedAddCommGroup (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := Matrix.normedSpace
  intro g₀ h₀
  obtain ⟨U1, F1, hU1, h1, hF1, e1⟩ := hv g₀ h₀
  refine ⟨U1, fun x => c • F1 x, hU1, h1, hF1.const_smul c, fun g hg hgH => ?_⟩
  show (R.σ g) (c • v) = c • F1 g
  rw [map_smul]
  exact congrArg (c • ·) (e1 g hg hgH)

private theorem zero_mem_sm {k r : ℕ} (R : BranchingSupport.Rep k r) : (0 : R.H) ∈ R.sm := by
  simp only [BranchingSupport.Rep.sm, PI.UpqRep.smoothVecs, Set.mem_setOf_eq, PI.UpqRep.IsSmoothVec]
  letI : NormedAddCommGroup (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := Matrix.normedSpace
  intro g₀ _
  refine ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun g _ _ => ?_⟩
  show (R.σ g) 0 = 0
  exact map_zero _

theorem pairing : HypsG → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (om : ι → ℂ) (Bm : R.H → Wp) (BI : ∀ I, (RI I).H → Wp) (β : κ → ℂ), R.IsDG ε mu → (∀ I, (RI I).IsDG ε (muI I)) → Function.Injective muI → TensRaw ρ R RI io pr → SideG k r z π u μW μN μG νq → IsBes R z π Bm → (∀ I, IsIsoB (RI I) z π νq (BI I) ∨ β I = 0) → (∀ I, ∀ y ∈ (RI I).sm, Bm (ev Γ R om (fun c => io I c y)) = β I • BI I y) → ∀ I, IsIsoB (RI I) z π νq (BI I) → ∀ y ∈ (RI I).sm, ∀ (a : ι → ℂ), ∀ w ∈ R.sm, ∫ x, ⟪BI I ((RI I).σ (Matrix.of x) y), Formalism.QuantumDeterminants.herm Γ (ρ (Matrix.of x) *ᵥ a) om • Bm (R.σ (Matrix.of x) w)⟫_ℂ ∂νq = β I * ⟪y, ∑ c, pr I c (tm R a w c)⟫_ℂ := by
  intro hyp k r ι κ _ _ _ _ ρ Γ d R RI io pr ε mu muI Wp _ _ _ _ z π u μW μN μG νq om Bm BI β hR hRI hinj hT hS
    hB hOr hev I hIso y hy a w hw
  have hK : PI.KFinSmooth := hyp.1.2.2.1
  have hpr : ∀ J c, BranchingSupport.SmMap R (RI J) (pr J c) := by
    cases hT
    assumption
  have hv : ∀ J, (∑ c, pr J c (BranchingSupport.tm R a w c)) ∈ (RI J).sm := by
    intro J
    refine Finset.sum_induction _ (· ∈ (RI J).sm) (fun p q hp hq => add_mem_sm (RI J) hp hq)
      (zero_mem_sm (RI J)) ?_
    intro c _
    obtain ⟨hmem, -, -, -⟩ := hpr J c
    exact hmem _ (smul_mem_sm' R (a c) hw)
  have hae := (Gp91.GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hK k r ε mu R Wp z π u μW μN μG νq hR hS).1
  have hpt : ∀ᵐ x ∂νq, ⟪BI I ((RI I).σ (Matrix.of x) y), Formalism.QuantumDeterminants.herm Γ (ρ (Matrix.of x) *ᵥ a) om • Bm (R.σ (Matrix.of x) w)⟫_ℂ =
      ∑ J, β J * ⟪BI I ((RI I).σ (Matrix.of x) y), BI J ((RI J).σ (Matrix.of x) (∑ c, pr J c (BranchingSupport.tm R a w c)))⟫_ℂ := by
    filter_upwards [hae] with x hx
    rw [Gp91.GlobalTheory.T.tensor_bessel_transfer hK k r ι κ ρ Γ d R RI io pr ε mu muI Wp om Bm BI β hR hRI hT hB.1 hB.2.1 hev a w hw
      (Matrix.of x) hx, inner_sum]
    simp only [inner_smul_right]
  refine (MeasureTheory.integral_congr_ae hpt).trans ?_
  rw [MeasureTheory.integral_finset_sum]
  · rw [Finset.sum_eq_single I]
    · rw [MeasureTheory.integral_const_mul,
        (Gp91.GlobalTheory.T.isometric_bessel_memLp_and_integral_inner_eq hK k r ε (muI I) (RI I) Wp z π u μW μN μG νq (BI I) (hRI I) hS hIso).2 _ (hv I) y hy]
    · intro J _ hJI
      rw [MeasureTheory.integral_const_mul]
      rcases hOr J with hJ | hJ
      · rw [Gp91.GlobalTheory.T.isometric_bessel_compare hyp k r ε (muI J) (muI I) (RI J) (RI I) Wp z π u μW μN μG νq (BI J) (BI I)
          (hRI J) (hRI I) (fun h => hJI (hinj h)) hS hJ hIso _ (hv J) y hy, mul_zero]
      · rw [hJ, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ I) h
  · intro J _
    rcases hOr J with hJ | hJ
    · exact (integrable_inner_of_memLp
        ((Gp91.GlobalTheory.T.isometric_bessel_memLp_and_integral_inner_eq hK k r ε (muI I) (RI I) Wp z π u μW μN μG νq (BI I) (hRI I) hS hIso).1 y hy)
        ((Gp91.GlobalTheory.T.isometric_bessel_memLp_and_integral_inner_eq hK k r ε (muI J) (RI J) Wp z π u μW μN μG νq (BI J) (hRI J) hS hJ).1 _
          (hv J))).const_mul (β J)
    · simp only [hJ, zero_mul]
      exact MeasureTheory.integrable_zero _ _ _

end GlobalTheory.BesselPairing
