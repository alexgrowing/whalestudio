import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankSB
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaIntegralIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization

open MeasureTheory Matrix Topology

namespace GlobalTheory.RankFibre

theorem X0_mul_X0_transpose (k : Type) [Field k] (a b : ℕ) :
    GlobalTheory.SplitFlip.X0 k (finSumFinEquiv (m := a) (n := b)) * (GlobalTheory.SplitFlip.X0 k (finSumFinEquiv (m := a) (n := b)))ᵀ = 1 := by
  ext i j
  rw [GlobalTheory.SplitFlip.frameMatrixFirstColumnBlock_mul_apply]
  simp [GlobalTheory.SplitFlip.X0, Matrix.one_apply, eq_comm]

theorem isUnit_of_rank_mul_X0 {k : Type} [Field k] {a b : ℕ} (A : Matrix (Fin a) (Fin a) k)
    (h : (A * GlobalTheory.SplitFlip.X0 k (finSumFinEquiv (m := a) (n := b))).rank = a) : IsUnit A := by
  have h1 : A.rank = Fintype.card (Fin a) := by
    refine le_antisymm (by simpa using A.rank_le_width) ?_
    simpa [h] using Matrix.rank_mul_le_left A (GlobalTheory.SplitFlip.X0 k (finSumFinEquiv (m := a) (n := b)))
  have hli : LinearIndependent k A.row := by
    rw [rank_eq_finrank_span_row] at h1
    rw [linearIndependent_iff_card_eq_finrank_span, eq_comm]; exact h1
  exact Matrix.linearIndependent_rows_iff_isUnit.1 hli

theorem integrable_fibre_integrand : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : ℕ) (ν : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → ∀ Φ ∈ GlobalTheory.RankFibre.fullRankSB k a (a + b), MeasureTheory.Integrable (fun g : GL (Fin a) k => Φ (g.val * GlobalTheory.SplitFlip.X0 k finSumFinEquiv) * (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) * GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) (((a + b : ℕ) : ℂ) / 2)) (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) := by
  intro k _ _ _ _ _ _ a b ν hν Φ hΦ
  obtain ⟨⟨hl, hK⟩, hrk⟩ := hΦ
  set X0 := GlobalTheory.SplitFlip.X0 k (finSumFinEquiv (m := a) (n := b)) with hX0
  have hc1 : IsLocallyConstant fun g : GL (Fin a) k => Φ (g.val * X0) :=
    hl.comp_continuous (Units.continuous_val.matrix_mul continuous_const)
  have hc2 := GlobalTheory.GodementJacquet.isLocallyConstant_char_det (k := k) (n := Fin a) hν
  have hc3 : IsLocallyConstant fun g : GL (Fin a) k =>
      GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) (((a + b : ℕ) : ℂ) / 2) :=
    ((GlobalTheory.SplitWeil.isLocallyConstant_nabs k).comp_continuous GeneralLinearGroup.continuous_det).comp
      fun x => ((x : ℝ) : ℂ) ^ (((a + b : ℕ) : ℂ) / 2)
  have hcont := ((hc1.mul hc2).mul hc3).continuous

  set D : Set (Matrix (Fin a) (Fin a) k) := {A | Φ (A * X0) ≠ 0} with hD
  have hDc : IsClosed D := by
    exact (hl.isOpen_fiber 0).isClosed_compl.preimage
      (show Continuous fun A : Matrix (Fin a) (Fin a) k => A * X0 from continuous_id.matrix_mul continuous_const)
  have hDsub : D ⊆ (fun M : Matrix (Fin a) (Fin (a + b)) k => M * X0ᵀ) '' tsupport Φ := by
    intro A hA
    refine ⟨A * X0, subset_tsupport _ hA, ?_⟩
    show A * X0 * X0ᵀ = A
    rw [Matrix.mul_assoc, hX0, X0_mul_X0_transpose, Matrix.mul_one]
  have hDcpt : IsCompact D :=
    (hK.image (show Continuous fun M : Matrix (Fin a) (Fin (a + b)) k => M * X0ᵀ from
      continuous_id.matrix_mul continuous_const)).of_isClosed_subset hDc hDsub
  have hDr : D ⊆ Set.range fun g : GL (Fin a) k => g.val := by
    intro A hA
    have hr : (A * X0).rank = a := by
      by_contra hne
      exact hA (hrk _ hne)
    exact ⟨(isUnit_of_rank_mul_X0 A hr).unit, rfl⟩
  have hS : IsCompact ((fun g : GL (Fin a) k => g.val) ⁻¹' D) :=
    GlobalTheory.SplitFlip.isEmbedding_val_GL.isInducing.isCompact_preimage' hDcpt hDr
  have hcs : HasCompactSupport fun g : GL (Fin a) k => Φ (g.val * X0) * (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) *
      GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) (((a + b : ℕ) : ℂ) / 2) := by
    refine HasCompactSupport.intro hS fun g hg => ?_
    have : Φ (g.val * X0) = 0 := not_not.1 hg
    simp [this]
  exact hcont.integrable_of_hasCompactSupport hcs

end GlobalTheory.RankFibre
