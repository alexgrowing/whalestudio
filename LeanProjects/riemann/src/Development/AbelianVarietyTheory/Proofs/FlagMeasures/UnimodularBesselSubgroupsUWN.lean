import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupsClosedUnitaryWCompact
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MatGroupHaarUniqueFiniteCompactOpenPos
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LintegralInvEqOfBiInvariantMatGroup
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.EqSmulOfTwoSided
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupProductMeasureIsHaar

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

variable {k r : ℕ}

theorem IsClosedSub.isMatGroup_of_unitary {S : Set (Mat k r)} (hS : IsClosedSub k r S) : PI.IsMatGroup S := by
  obtain ⟨hG, hcl, h1, hmul, hinv⟩ := hS
  refine ⟨hcl, h1, hmul, fun a ha => ⟨hinv a ha, ?_⟩⟩

  have e : aᴴ * Hpk k r * a = Hpk k r := hG ha
  have hH := Formalism.FourierDecayAlt.P.B2x2.hpk_unit k r
  have hd := congrArg Matrix.det e
  rw [Matrix.det_mul, Matrix.det_mul] at hd
  have hdet : IsUnit a.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, mul_zero] at hd
    exact hH.ne_zero hd.symm
  exact Matrix.mul_nonsing_inv a hdet

theorem map_invM_eq {S : Set (Mat k r)} (hS : PI.IsMatGroup S) {μ : Measure (Mt k r)}
    (hμ : IsHaarOn S μ) (hR : ∀ s ∈ S, μ.map (rmulM s) = μ) : μ.map invM = μ := by
  have hL : PI.IsHaarOnM S μ := hμ
  have hR' : PI.IsRightInvM S μ := hR
  ext B hB
  rw [Measure.map_apply measurable_invM hB]

  have h := GlobalTheory.HaarInversion.lintegral_inv_eq _ S μ hS hL hR' (B.indicator 1)
    (measurable_one.indicator hB)
  rw [lintegral_indicator_one hB] at h
  rw [← h, ← lintegral_indicator_one (measurable_invM hB)]
  rfl

theorem rightInv_of_multiple {S : Set (Mat k r)} (hS : PI.IsMatGroup S) {μ ν : Measure (Mt k r)}
    (hμ : IsHaarOn S μ) (hν : PI.IsHaarOnM S ν) (hR : PI.IsRightInvM S ν) :
    ∀ s ∈ S, μ.map (rmulM s) = μ := by
  intro s hs
  have hL : PI.IsHaarOnM S μ := hμ

  obtain ⟨c, -, -, hc⟩ := (GlobalTheory.MatHaar.haar_unique_locFinite_openPos _ S ν hS hν).1 μ hL
  have hνs : ν.map (rmulM s) = ν := hR s hs
  rw [hc, Measure.map_smul, hνs]

private theorem exists_isHaarOnM_of_isMatGroup {m : ℕ} {G : Set (Matrix (Fin m) (Fin m) ℂ)} (hG : PI.IsMatGroup G) :
    ∃ μ : Measure (PI.MtM m), PI.IsHaarOnM G μ := by
  have he := GlobalTheory.MatHaar.inc_memb (G := G) (hG := hG)
  refine ⟨(GlobalTheory.MatHaar.haar0 hG).map GlobalTheory.MatHaar.inc, he.sigmaFinite_map, ?_, ?_, ?_⟩
  · intro h0
    rw [Measure.map_eq_zero_iff he.measurable.aemeasurable] at h0
    exact (NeZero.ne (GlobalTheory.MatHaar.haar0 hG)) h0
  · rw [he.map_apply]
    have : (GlobalTheory.MatHaar.inc (G := G) (hG := hG)) ⁻¹' {x | Matrix.of x ∉ G} = ∅ := by
      ext g
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact GlobalTheory.MatHaar.inc_mem g
    rw [this, measure_empty]
  · intro a ha
    let g0 : GlobalTheory.MatHaar.Grp G hG := ⟨a, ha⟩
    have hcomp : PI.lmulQ a ∘ GlobalTheory.MatHaar.inc (G := G) (hG := hG) =
        GlobalTheory.MatHaar.inc ∘ (fun g => g0 * g) := by
      funext g
      exact (GlobalTheory.MatHaar.inc_mul g0 g).symm
    rw [Measure.map_map (GlobalTheory.MatHaar.lmulQ_cont a).measurable he.measurable, hcomp,
      ← Measure.map_map he.measurable (measurable_const_mul g0), map_mul_left_eq_self]

theorem unimodular_S_N_UW : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z → ∀ μ : Measure (Mt k r), (IsHaarOn (Sset k r z) μ → IsUnimod (Sset k r z) μ) ∧ (IsHaarOn (Nset k r) μ → IsUnimod (Nset k r) μ ∧ ∀ h ∈ UWset k r z, μ.map (conjM h) = μ) ∧ (IsHaarOn (UWset k r z) μ → IsUnimod (UWset k r z) μ ∧ μ Set.univ < ⊤) := by
  intro k r z hz hT μ
  obtain ⟨-, hNc, hWc, -, -⟩ := closedSub_groups k r z hz hT
  have hN := hNc.isMatGroup_of_unitary
  have hW := hWc.isMatGroup_of_unitary
  obtain ⟨μN0, hμN0⟩ := exists_isHaarOnM_of_isMatGroup hN
  obtain ⟨μW0, hμW0⟩ := exists_isHaarOnM_of_isMatGroup hW
  refine ⟨fun hμ => ?_, fun hμ => ?_, fun hμ => ?_⟩
  ·
    obtain ⟨hSg, -, hSH, hSR⟩ := GlobalTheory.muSof_isHaar k r z μW0 μN0 hz hT hμW0 hμN0
    have hR := rightInv_of_multiple hSg hμ hSH hSR
    exact ⟨hR, map_invM_eq hSg hμ hR⟩
  · obtain ⟨-, -, hNR, -, hconj⟩ :=
      GlobalTheory.UnipotentRadicalHaar.unimodular_normal k r z μW0 μ hz hT hμW0 hμ
    have hR : ∀ s ∈ Nset k r, μ.map (rmulM s) = μ := hNR
    exact ⟨⟨hR, map_invM_eq hN hμ hR⟩, fun h hh => hconj h hh⟩
  · obtain ⟨hWR, hfin, -, -, -⟩ :=
      GlobalTheory.UnipotentRadicalHaar.unimodular_normal k r z μ μN0 hz hT hμ hμN0
    have hR : ∀ s ∈ UWset k r z, μ.map (rmulM s) = μ := hWR
    exact ⟨⟨hR, map_invM_eq hW hμ hR⟩, measure_lt_top μ _⟩

end GlobalTheory.SgInf
