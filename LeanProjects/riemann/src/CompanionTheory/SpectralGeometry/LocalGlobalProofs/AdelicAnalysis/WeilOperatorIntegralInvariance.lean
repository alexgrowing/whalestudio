import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StandardAdelicCharacterStatement

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.FstarPer

theorem oh_mul {F : Type} [Field F] [NumberField F] {x y : A F} (hx : x ∈ Oh F) (hy : y ∈ Oh F) :
    x * y ∈ Oh F :=
  fun v => mul_mem (hx v) (hy v)

theorem continuous_qf {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
    (h : A F) (B : Matrix ι ι (A F)) : Continuous (qf h B) := by
  unfold qf
  exact continuous_const.mul (continuous_id.dotProduct ((continuous_const (y := B)).matrix_mulVec continuous_id))

theorem fstar_periodic : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ φ : (ι → A F) → ℂ, SB φ → ∃ N : ℕ, 0 < N ∧ ∀ x ∈ Oh F, opU ψ (hf F) (Bf B) ((N : A F) * x) φ = φ ∧ ∀ y : A F, fstar ψ (hf F) (Bf B) (muF B lf) φ (y + (N : A F) * x) = fstar ψ (hf F) (Bf B) (muF B lf) φ y := by
  intro F _ _ _ _ lf _ _ ψ hψ ι _ _ M B ρ P _ φ hφ
  have hK : IsCompact (qf (hf F) (Bf B) '' tsupport φ) :=
    IsCompact.image hφ.2 (continuous_qf _ _)
  obtain ⟨N, hN, hNK⟩ := (GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.2.2.2.2.2.2.2.1 _ hK
  have htriv := ((GlobalTheory.T.standard_adelic_character F).2 ψ hψ).2.1
  have key : ∀ x ∈ Oh F, opU ψ (hf F) (Bf B) ((N : A F) * x) φ = φ := by
    intro x hx
    funext u
    by_cases hu : u ∈ tsupport φ
    · have h1 := hNK _ (Set.mem_image_of_mem _ hu)
      have h2 : (N : A F) * x * qf (hf F) (Bf B) u ∈ Oh F := by
        have h3 := oh_mul hx h1
        have h4 : (N : A F) * x * qf (hf F) (Bf B) u = x * ((N : A F) * qf (hf F) (Bf B) u) := by
          ring
        rwa [h4]
      simp [opU, htriv _ h2]
    · have h0 : φ u = 0 := image_eq_zero_of_notMem_tsupport hu
      simp [opU, h0]
  refine ⟨N, hN, fun x hx => ⟨key x hx, fun y => ?_⟩⟩
  unfold fstar
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have h5 := congrFun (key x hx) u
  simp only [opU] at h5 ⊢
  rw [add_mul, AddChar.map_add_eq_mul, mul_assoc, h5]

end GlobalTheory.CompanionTheory.SW.FstarPer
