import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsProjOnOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormLeOfMeanZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CuspidalSubspaceClosedRightTranslationStableStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RepresentativeValuesVectorVariationUnipotentOrbiStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousRepresentativePropertiesStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.DeepStep

theorem step_bound (B : RowsAut) (b ρ M : ℝ) (P : ℕ) (D : ℕ)
    (T : Fin D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund)) (Fr : Fin D → B.Hs → B.I.GA → ℂ) (x : B.I.GA)
    (W : Submodule B.I.E (Fin B.I.n → B.I.E)) (hg : 1 ≤ B.g) (hW : B.I.IsIsot W)
    (hcov : ∀ ν : B.I.Ginf, ((ν, 1) : B.I.GA) ∈ B.I.NA W → ∃ γ ∈ B.I.GFset, ∃ k ∈ B.I.Kg B.g,
      ∃ y ∈ omega B.I x W ρ, ((ν, 1) : B.I.GA) * x = γ * y * (1, k))
    (hS : StepBoundAt B b P) (hR : ∀ i, IsReps B (T i) (Fr i))
    (hC : ∀ i u, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (T i u))) (hM : 0 ≤ M)
    (hb : ∀ y ∈ omega B.I x W ρ, ∀ u ∈ VP B (P + 1), ‖vv B Fr u y‖ ≤ M * ‖u‖) :
    ∀ y ∈ omega B.I x W ρ, ∀ u ∈ VP B P,
      ‖vv B Fr u y‖ ≤ 2 * ρ * Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖ := by
  intro y hy u hu
  have hvv : ∀ z : B.I.GA, ‖vv B Fr u z‖ = Real.sqrt (∑ i, ‖Fr i u z‖ ^ 2) := by
    intro z
    simp [vv, EuclideanSpace.norm_eq]
  have hvvs : ∀ z : B.I.GA, ‖vv B Fr u z - vv B Fr u x‖ = Real.sqrt (∑ i, ‖Fr i u z - Fr i u x‖ ^ 2) := by
    intro z
    simp [vv, EuclideanSpace.norm_eq]
  have hnear := GlobalTheory.T.representativeValuesVector_variation_unipotentOrbit B b ρ M P D T Fr x W hS hR hM hb
  have hcusp := GlobalTheory.T.cuspidalSubspace_closed_rightTranslation_stable B
  obtain ⟨L, hL, -, -, hLf⟩ := hcusp
  have hrep : ∀ i, GlobalTheory.Dec.IsContRep B (T i u) (Fr i u) := fun i => (hR i P u hu).1
  have hx : ‖vv B Fr u x‖ ≤ ρ * Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖ := by
    rw [hvv]
    refine GlobalTheory.MeanZero.norm_le_of_cusp B.I B.μf B.g W D (fun i => Fr i u) x (fun i => Fr i u x) _ hg hW ?_ ?_
    · intro i
      obtain ⟨hc, hl, hae⟩ := hrep i
      refine ⟨hc, hl, (hR i P u hu).2.1, ?_⟩
      have h1 := ((GlobalTheory.T.continuous_representative_properties B).2.2.2 _ _ (hrep i)).1
      exact (hLf (T i u) (Fr i u) hl hc h1).1 ((hL _).2 (hC i u))
    · intro ν hν
      obtain ⟨γ, hγ, k, hk, z, hz, he⟩ := hcov ν hν
      have hval : ∀ i, Fr i u (((ν, 1) : B.I.GA) * x) = Fr i u z := by
        intro i
        rw [he, (hR i P u hu).2.1 k hk, (hrep i).2.1 γ hγ]
      simp only [hval]
      rw [← hvvs]
      exact hnear z hz u hu
  calc ‖vv B Fr u y‖ = ‖(vv B Fr u y - vv B Fr u x) + vv B Fr u x‖ := by rw [sub_add_cancel]
    _ ≤ ‖vv B Fr u y - vv B Fr u x‖ + ‖vv B Fr u x‖ := norm_add_le _ _
    _ ≤ ρ * Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖ + ρ * Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖ :=
        add_le_add (hnear y hy u hu) hx
    _ = 2 * ρ * Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖ := by ring

end GlobalTheory.DeepStep
