import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsBlockProd
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaWeightBounds
import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IntegralityBoundOfFamilyContainingScaledThetaRulStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HalfLevelGeneratorNorm
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaRunParametersAtTypePrimesProductStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NotIsBlockProdZero
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightExponentsEmbeddingsDegree

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DegreeInterpolationBounds

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn GlobalTheory.BlockTh GlobalTheory.EtaAn ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem totalDegree_eq_DF {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} (c : Coeff l) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmA c a n) (h0 : P ≠ 0) :
    P.totalDegree = Formalism.L2.Pj.DF Dw a := by
  have key : ∀ m ∈ P.support, (m.sum fun _ e => e) = Formalism.L2.Pj.DF Dw a := by
    intro m hm
    rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma, Formalism.L2.Pj.DF]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => hP.1.2.2 m hm τ i
  obtain ⟨m, hm⟩ := Finset.nonempty_iff_ne_empty.2 (mt MvPolynomial.support_eq_empty.1 h0)
  apply le_antisymm
  · exact Finset.sup_le fun m' hm' => (key m' hm').le
  · exact (key m hm) ▸ MvPolynomial.le_totalDegree hm

theorem pow_le_sq_of_log {M x : ℝ} {d : ℕ} (hM : 1 < M) (hd : 1 ≤ d) (hx : 0 ≤ x)
    (h : (d : ℝ) / 2 * Real.log M ≤ Real.log x) : M ^ d ≤ x ^ 2 := by
  have hl : 0 < Real.log M := Real.log_pos hM
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hx0 : 0 < x := by
    rcases hx.eq_or_lt with h0 | h0
    · rw [← h0, Real.log_zero] at h
      nlinarith
    · exact h0
  rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  push_cast
  linarith

theorem i2iAt_record : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T) (_EX : ErrX D) (j : ℕ) (hj : InR D j) (K : KAdm) (Ch Ah Cq Aq : ℝ) (S : Scal (recB h.toLawsCore)) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0 → TieC K H Ch Ah Cq Aq C2 A2 CR → PageAt large₂ C2 A2 → EtaleWeightGaps.PageSupp D large₂ (recB h.toLawsCore) C2 A2 nW S wL → ∀ (P₁ : MvPolynomial (LtN (T.Q.Dw j) wL.n) T.Q.c.F), P₁ ∈ harmA T.Q.c (wtA wL) wL.n → IsBlockProd P₁ → ∀ (N : ℕ) (w : Fin (N + 1) → (recB h.toLawsCore).Cusp j wL), ContainsTh (T.Q.Xo j) T.Q.c (T.nab j) ((S.sW : (recB h.toLawsCore).KO) : T.Q.c.F) P₁ (fun k => ((w k).1 : T.R j)) → ∀ tableLineDegreeFive : ℝ, p14 D.host.E D.R.r wL.n D.R.m ≤ tableLineDegreeFive → I2AtFramePoints (T.U j) (xiR D) (fun k => ((w k).1 : T.R j)) (wtA wL, wL.n) (I2.th (E := D.host.E) (D.host.g 0 * D.host.g 1) (Real.sqrt (90 * (D.R.f * D.R.r + WeightAlgebra.DF wL)))) tableLineDegreeFive (WeightAlgebra.DF wL) (cc D large₂ C2 A2 CR wL) := by
  intro hCI D T h EX j hj K Ch Ah Cq Aq S large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hHP hTie hPage hSupp P₁ hP hB N w hC
    tableLineDegreeFive hP14
  obtain ⟨inst, hnab⟩ := h.nabPin j hj
  obtain ⟨α, hα1, hα2⟩ := GlobalTheory.RunIn.half_level_generator_norm D T h EX
  obtain ⟨hrun, hcc, -, -⟩ := GlobalTheory.T.thetaRunParameters_at_typePrimes_product D _ _ j (recPJ h j hj) K Ch Ah Cq Aq S large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0
    hHP hTie hPage hSupp
  have hM : T.Q.l.M = D.host.g 0 * D.host.g 1 := h.pins.2.1.1
  have hP0 : P₁ ≠ 0 := fun e => GlobalTheory.BlockThInhab.not_isBlockProd_zero (T.Q.Dw j) wL.n T.Q.c.F (e ▸ hB)
  have hdeg : P₁.totalDegree = WeightAlgebra.DF wL :=
    (totalDegree_eq_DF T.Q.c hP hP0).trans (GlobalTheory.WeightExponents.weight_exponents D T.Q h.pins j hj wL).1
  have hq : (T.Q.Dw j).q ≤ D.R.m := by
    rw [(h.pins.2.2.2 j hj).2.1]
    exact Nat.sub_le _ _
  have hs : ∀ σ : T.Q.c.F →+* ℂ,
      (T.Q.l.M : ℝ) ^ P₁.totalDegree ≤ ‖σ ((S.sW : (recB h.toLawsCore).KO) : T.Q.c.F)‖ ^ 2 := by
    intro σ
    have h3 : (3 : ℝ) ≤ T.Q.l.M := by exact_mod_cast T.Q.l.three_le
    refine pow_le_sq_of_log (by linarith) (by rw [hdeg]; have := hSupp.2.2.2.2; omega) (norm_nonneg _) ?_
    rw [hdeg, hM, Nat.cast_mul]
    exact hSupp.2.1 σ
  have key := GlobalTheory.T.integralityBound_of_family_containing_scaled_thetaRules hCI D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r (T.U j) (xiR D) (T.nab j) hnab
    (fun σ hσ => ⟨h.unf j hj σ hσ, h.unTest j hj σ hσ, h.xiAbs j hj σ hσ⟩) α hα1 hα2 (wtA wL) wL.n P₁ (dom_wtA wL) hP hB
    _ hs N (fun k => ((w k).1 : T.R j)) (fun k => cusp_le_sec _ _ _ _ _ (cutR_le T.C j wL (w k).2)) hC
    (Real.sqrt (90 * (D.R.f * D.R.r + WeightAlgebra.DF wL))) D.R.m (by rw [hdeg, hM]; exact hrun) (Or.inr hq) tableLineDegreeFive
    (cc D large₂ C2 A2 CR wL) hP14 (by rw [hM]; exact hcc)
  rw [hdeg, hM] at key
  exact key

end GlobalTheory.DegreeInterpolationBounds
