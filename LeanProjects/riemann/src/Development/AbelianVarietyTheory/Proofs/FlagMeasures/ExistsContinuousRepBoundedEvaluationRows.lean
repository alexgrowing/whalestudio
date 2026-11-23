import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsClosedEmbeddingEntriesInf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepUnitaryStronglyContinuous
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AbsOpIntIntegrable
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConvolutionSmoothL2Statement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.EvalBound

theorem tens_mem_VP (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (hB : IsDSData B d) :
    B.tens B.w ∈ VP B 0 :=
  (tens_w_mem B hB 0).1

noncomputable def realRep (B : RowsAut) : B.I.Ginf →* (B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund) where
  toFun x := B.R (x, 1)
  map_one' := (GlobalTheory.RightRegFund.rightReg_unitary_continuous B).1
  map_mul' x y := by
    rw [← (GlobalTheory.RightRegFund.rightReg_unitary_continuous B).2.1, Prod.mk_mul_mk, mul_one]

theorem exists_contRep_bound : GlobalTheory.DSId.StrictLow → ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d → 1 ≤ B.I.n → 1 ≤ B.g → ∃ C : ℝ, ∀ A ∈ B.I.HomS B.σs B.μf B.fund B.R, (∀ k ∈ B.I.Kg B.g, B.R (1, k) (A (B.tens B.w)) = A (B.tens B.w)) → ∃ f : B.I.GA → ℂ, IsContRep B (A (B.tens B.w)) f ∧ ∀ x, ‖f x‖ ≤ C * (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) * ‖A (B.tens B.w)‖ := by
  intro hSL B d hB hn hg
  obtain ⟨hU, -, -, hw1, -⟩ := GlobalTheory.Dec.tensorRep B d hB
  obtain ⟨F, hF, hFc, hFeq⟩ :=
    GlobalTheory.StepAverage.exists_smooth_average hSL B d hB 0 _ (tens_mem_VP B d hB)
  set a : B.I.Ginf → ℂ := fun g => F (fun v i j => uMat (g v) i j) with ha
  have hemb := GlobalTheory.StepAverage.isClosedEmbedding_entries_inf B.I
  have hac : Continuous a := hF.continuous.comp hemb.continuous
  have haS : HasCompactSupport a := hFc.comp_isClosedEmbedding hemb
  have hsm : SmoothInf B.I a := fun x =>
    ⟨F, hF.contDiffAt, Filter.Eventually.of_forall fun _ => rfl⟩
  have hvi : Integrable (fun g => a g • B.σs g (B.tens B.w)) (muInf B.I) := by
    by_contra hni
    have h0 : B.tens B.w = 0 := by rw [hFeq]; exact integral_undef hni
    rw [h0, norm_zero] at hw1
    exact zero_ne_one hw1
  have hai : Integrable a (muInf B.I) := by
    refine hvi.norm.mono' hac.aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)
    rw [norm_smul, hU.2.2.1, hw1, mul_one]
  obtain ⟨C, hC⟩ := GlobalTheory.T.convolutionSmoothL2_of_def B B.g hn hg a hsm haS
  refine ⟨C, fun A hA hK => ?_⟩
  have hRU := GlobalTheory.RightRegFund.rightReg_unitary_continuous B
  obtain ⟨P, hP1, hP2⟩ := GlobalTheory.absOpInt B.I.Ginf (muInf B.I) (B.I.L2 B.μf B.fund) (realRep B)
    (fun g x => hRU.2.2.1 (g, 1) x)
    (fun x => (hRU.2.2.2.1 x).comp (continuous_id.prodMk continuous_const)) a hai
  have hA' : ∀ g, A.comp (B.σs g) = (B.R (g, 1)).comp A := hA
  have hPy : P (A (B.tens B.w)) = A (B.tens B.w) := by
    rw [hP1]
    symm
    calc A (B.tens B.w) = A (∫ g, a g • B.σs g (B.tens B.w) ∂(muInf B.I)) := congrArg A hFeq
      _ = ∫ g, A (a g • B.σs g (B.tens B.w)) ∂(muInf B.I) := (A.integral_comp_comm hvi).symm
      _ = ∫ g, a g • realRep B g (A (B.tens B.w)) ∂(muInf B.I) := by
        congr 1
        funext g
        rw [map_smul]
        congr 1
        exact congrArg (fun T => T (B.tens B.w)) (hA' g)
  obtain ⟨f, hsmg, hfc, hfb, hfae⟩ := hC (A (B.tens B.w)) hK P ⟨hai, fun x y => hP2 x y⟩
  refine ⟨f, ?_, hfb⟩
  rw [hPy] at hfae
  unfold IsSmoothMG at hsmg
  unfold IsContRep
  exact ⟨hfc, hsmg.1, hfae⟩

end GlobalTheory.EvalBound
