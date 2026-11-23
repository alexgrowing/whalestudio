import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryPartnerDiagStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrArchPairAdeleJoin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorArchimedeanMemAdelicSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzHaarWeilStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicL2LimitZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicL2EqZeroImpEqZeroStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section
open MeasureTheory

namespace GlobalTheory.WeilL2Words

theorem dS_om_eq : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), GlobalTheory.WeilL2Words.IsStdInf F ψ →
    ∀ {G : Type} [Group G] (om : G →* Module.End ℂ ((κ → AdeleRing (𝓞 F) F) → ℂ)),
      (∀ p, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, om p φ ∈ GlobalTheory.WeilM.schA F κ) →
      ∀ (M : G → ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))),
      (∀ p h, ∀ φ ∈ GlobalTheory.WeilM.schA F κ,
        om p (GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F (M p h)) φ) = GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F h) (om p φ)) →
      ∀ (μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _)), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      (∀ p, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, GlobalTheory.WeilL2Words.l2A F μ (om p φ) = GlobalTheory.WeilL2Words.l2A F μ φ) →
      ∀ p h, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, GlobalTheory.WeilL2Words.dS F ψ h (om p φ) = om p (GlobalTheory.WeilL2Words.dS F ψ (M p h) φ) := by
  intro F _ _ _ κ _ ψ hψ G _ om hpres M himpl μ hμ hiso p h φ hφ
  set h' := M p h with hh'
  have hOm : om p φ ∈ GlobalTheory.WeilM.schA F κ := hpres p φ hφ
  have hD1 : GlobalTheory.WeilL2Words.dS F ψ h' φ ∈ GlobalTheory.WeilM.schA F κ := GlobalTheory.WeilL2Words.dS_mem_schA F hψ h' hφ

  set Qr : ℕ → (κ → AdeleRing (𝓞 F) F) → ℂ := fun n => ((n : ℂ) + 1) •
      (GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F (((n : ℝ) + 1)⁻¹ • h')) φ - φ) - GlobalTheory.WeilL2Words.dS F ψ h' φ with hQr
  have hQr_mem : ∀ n, Qr n ∈ GlobalTheory.WeilM.schA F κ := fun n =>
    Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.sub_mem _ (GlobalTheory.T.schroedingerOperator_archimedean_mem_adelicSchwartz F κ ψ hψ _ φ hφ) hφ)) hD1
  set Gn : ℕ → (κ → AdeleRing (𝓞 F) F) → ℂ := fun n a => ((n : ℂ) + 1) *
      (GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F (((n : ℝ) + 1)⁻¹ • h)) (om p φ) a - om p φ a) -
        om p (GlobalTheory.WeilL2Words.dS F ψ h' φ) a with hGn
  have hGQ : ∀ n, Gn n = om p (Qr n) := by
    intro n
    have e := himpl p (((n : ℝ) + 1)⁻¹ • h) φ hφ
    rw [map_smul] at e
    rw [hQr, map_sub, map_smul, map_sub, e]
    funext a
    simp [hGn, smul_eq_mul]
  have hGmem : ∀ n, Gn n ∈ GlobalTheory.WeilM.schA F κ := fun n => by rw [hGQ]; exact hpres p _ (hQr_mem n)
  have hGl2 : Filter.Tendsto (fun n => GlobalTheory.WeilL2Words.l2A F μ (Gn n)) Filter.atTop (nhds 0) := by
    have e : (fun n => GlobalTheory.WeilL2Words.l2A F μ (Gn n)) = fun n => GlobalTheory.WeilL2Words.l2A F μ (Qr n) := by
      funext n; rw [hGQ, hiso p _ (hQr_mem n)]
    rw [e]
    have := GlobalTheory.T.adelic_schwartz_haar_weil F κ ψ hψ μ hμ h' φ hφ
    refine this.congr fun n => ?_
    congr 1
  set D : (κ → AdeleRing (𝓞 F) F) → ℂ := GlobalTheory.WeilL2Words.dS F ψ h (om p φ) - om p (GlobalTheory.WeilL2Words.dS F ψ h' φ) with hD
  have hDmem : D ∈ GlobalTheory.WeilM.schA F κ :=
    Submodule.sub_mem _ (GlobalTheory.WeilL2Words.dS_mem_schA F hψ h hOm) (hpres p _ hD1)
  have hpt : ∀ a, Filter.Tendsto (fun n => Gn n a) Filter.atTop (nhds (D a)) := by
    intro a
    have hd := (GlobalTheory.WeilL2Words.differentiableAt_schr F hψ h hOm a).hasDerivAt
    rw [hasDerivAt_iff_tendsto_slope_zero] at hd
    have ht : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) Filter.atTop (nhdsWithin 0 {0}ᶜ) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Filter.Eventually.of_forall fun n => ?_⟩
      · have h1 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        simpa only [one_div] using h1
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, inv_eq_zero]; positivity
    have h0 : ∀ Ψ : (κ → AdeleRing (𝓞 F) F) → ℂ, GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F ((0 : ℝ) • h)) Ψ a = Ψ a := by
      intro Ψ
      have : GlobalTheory.WeilL2Words.archPair F ((0 : ℝ) • h) = (0, 0) := by
        rw [zero_smul]
        refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> exact GlobalTheory.WeilL2Words.adeleOfMixedSpaceComponent_zero F
      rw [this]
      simp [GlobalTheory.WeilM.schr]
    have := (hd.comp ht).sub_const (om p (GlobalTheory.WeilL2Words.dS F ψ h' φ) a)
    refine this.congr fun n => ?_
    simp only [Function.comp, zero_add, h0, hGn, inv_inv, Complex.real_smul]
    push_cast
    ring
  have hl := GlobalTheory.T.adelic_l2_limit_zero F κ μ D Gn hGmem hpt hGl2
  have hz := GlobalTheory.T.adelic_l2_eq_zero_imp_eq_zero F κ μ hμ D hDmem hl
  exact sub_eq_zero.mp hz

end GlobalTheory.WeilL2Words
