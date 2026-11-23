import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConvolutionRangeCuspidalOfLowestKTypeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocDecOfDecGapGapGe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeCompressionFormulaOfStrictLowestKType
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeDecayGapOfCompressionFormulaGap
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeMultiplicityOneLargeGaps
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalConvolutionOrthogonalProjectorProof
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesCoefficientIntegrableMajorant

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.Dec.ProjCuspGap

theorem rank_le_dim {n : ℕ} (ε : Fin n → Bool) : rkR ε ≤ n := by
  refine (min_le_left _ _).trans ((Finset.card_filter_le _ _).trans ?_)
  simp

theorem gap_numeric {n : ℕ} (ε : Fin n → Bool) (h : ℝ)
    (hh : 120 * (n : ℝ) * ((rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) :
    rkR ε = 0 ∨ 8 * Real.sqrt (rkR ε) * (0 + 4 * n * rkR ε) < h := by
  rcases Nat.eq_zero_or_pos (rkR ε) with h0 | h0
  · exact Or.inl h0
  right
  have hq : (0 : ℝ) < rkR ε := by exact_mod_cast h0
  have hn : (0 : ℝ) < n := by exact_mod_cast h0.trans_le (rank_le_dim ε)
  have e : ((rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) = Real.sqrt (rkR ε) * rkR ε := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add_one hq.ne']
    norm_num
  rw [e] at hh
  have hp : 0 < (n : ℝ) * (Real.sqrt (rkR ε) * rkR ε) := by positivity
  nlinarith

theorem rank_pos_of_ne {n : ℕ} (ε : Fin n → Bool) {a b : Fin n} (hab : ε a ≠ ε b) : 0 < rkR ε := by
  unfold rkR
  refine lt_min (Finset.card_pos.2 ?_) (Finset.card_pos.2 ?_)
  · by_cases ha : ε a = true
    · exact ⟨a, by simp [ha]⟩
    · exact ⟨b, by revert hab ha; cases ε a <;> cases hb : ε b <;> simp [hb]⟩
  · by_cases ha : ε a = true
    · exact ⟨b, by revert hab ha; cases ε a <;> cases hb : ε b <;> simp [hb]⟩
    · exact ⟨a, by simp [ha]⟩

theorem two_mul_lt {n : ℕ} (ε : Fin n → Bool) (h : ℝ)
    (hh : 120 * (n : ℝ) * ((rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) (h0 : 0 < rkR ε) : 2 * (n : ℝ) < h := by
  have hq : (1 : ℝ) ≤ rkR ε := by exact_mod_cast h0
  have hn : (0 : ℝ) < n := by exact_mod_cast h0.trans_le (rank_le_dim ε)
  have h1 : (1 : ℝ) ≤ ((rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) := Real.one_le_rpow hq (by norm_num)
  nlinarith

theorem isStarProjection_of_isOrthProjOnto {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {T : H →L[ℂ] H} {S : Submodule ℂ H} (hT : IsOrthProjOnto T S) : IsStarProjection T :=
  ⟨hT.1, ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2 fun x y => hT.2.1 x y⟩

theorem projector_rank_cuspidal : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → GapGe B h → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → Integrable (ph B d) (muInf B.I) ∧ (HBig B 40 h → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T → IsStarProjection T ∧ FiniteDimensional ℂ (LinearMap.range (T : B.I.L2 B.μf B.fund →ₗ[ℂ] B.I.L2 B.μf B.fund)) ∧ Module.finrank ℂ (LinearMap.range (T : B.I.L2 B.μf B.fund →ₗ[ℂ] B.I.L2 B.μf B.fund)) = B.D ∧ ∀ Fv ∈ LinearMap.range (T : B.I.L2 B.μf B.fund →ₗ[ℂ] B.I.L2 B.μf B.fund), B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext Fv)) := by
  intro B d h hds hgap hh
  have hD : DecGap := GlobalTheory.DecGapBound.decGap_of_formulaGap GlobalTheory.Jet.FormGapFree.formulaGap
  have hloc : LocDec B h := GlobalTheory.Dec.locDec_of_decGap_gapGe hD B d h hds hgap hh
  have hK : ∀ v, IsKTypeOf (B.I.ε v) (B.σ v) (lowK (B.I.ε v) (B.lam v))
      (lowKSub (B.I.ε v) (B.lam v) (B.σ v)) := fun v =>
    GlobalTheory.Jet.MultGap.isKTypeOf_lowKSub _ _ _ _ _ (hds v).1 (hds v).2.1 fun a b hab =>
      (two_mul_lt _ h (hh v) (rank_pos_of_ne _ hab)).trans_le (hgap v a b hab)
  obtain ⟨hc, hle, hint⟩ := GlobalTheory.Dec.PhMajProof.phMaj B d h hds hloc
  have hI := hint 0 le_rfl fun v => gap_numeric _ h (hh v)
  have hph : Integrable (ph B d) (muInf B.I) := by
    refine hI.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)
    simpa using hle g
  refine ⟨hph, fun hb hfin T hT => ?_⟩
  obtain ⟨h1, -, -, h4, h5⟩ := (GlobalTheory.GlobProj.globalProj_holds B d hds hph).2.2.2 T hT
  refine ⟨isStarProjection_of_isOrthProjOnto h1, h4 hfin, h5, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact (GlobalTheory.T.convolution_range_cuspidal_of_lowestKType B d h hds hK hh hloc hb hfin T hT y).2

end GlobalTheory.Dec.ProjCuspGap
