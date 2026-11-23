import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.SumSingleEmbeddingExtendLe
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.LocalToGlobal.ProjectiveLattices.HostSize
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HarmAMemSpanShort
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaGeneratorsNoCommonZeroOfChartIndependenceStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaRulesLinearAndLevelCongruenceStatement

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NoBase

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections

theorem dom_nonempty {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) : ∃ x, x ∈ X.dom := by
  choose P hP hg using X.signature
  have hs : ∀ a : ℕ, sgn X.p0 a ≠ 0 := fun a => by unfold sgn; split_ifs <;> norm_num
  refine ⟨fun τ => P τ, fun τ => ⟨hP τ, fun i => ?_⟩⟩
  have e : dmin X.Gm (fun τ => P τ) τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    unfold dmin lminor
    rw [show gram τ.1 X.Gm (mat (fun τ => P τ) τ) = gram τ.1 X.Gm (P τ) from rfl, hg τ,
      Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    unfold psgn
    push_cast
    exact Fin.prod_univ_eq_prod_range (fun a => ((sgn X.p0 a : ℝ) : ℂ)) (i : ℕ)
  rw [e, Complex.ofReal_re]
  have h0 : psgn X.p0 i ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hs a
  exact mul_self_pos.2 h0

theorem rank_of_pins {D : D7} {Q : Par D} (h : Q.Pins) {j : ℕ} (hj : InR D j) :
    (Q.Dw j).p + (Q.Dw j).q = D.R.r := by
  obtain ⟨hp, hq, -⟩ := h.2.2.2 j hj
  obtain ⟨h1, h2⟩ := hj
  rw [hp, hq]
  have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity)
  simp only [Ranks.sigW, Ranks.r, Ranks.k]
  omega

theorem log_rdE (D : D7) : Real.log (FD.rdE D.host.E) = lrd D := by
  have hpos : 0 < dE D.host.E := abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E)
  unfold FD.rdE lrd
  rw [Real.log_rpow hpos, hostSize_finrank D]
  unfold dE
  push_cast
  ring

theorem mem_span_short (D : D7) (T : Top D) (h : LawsP T) (large₂ : SizeData₂ D) (j : ℕ) (hj : InR D j)
    (w : WeightFamilies.Wt D j) (hrows : PullbackSections.SupBoundPageRows D large₂ w) (hL : 2 ≤ large₂.sc.L) (hr : D.R.r ≤ w.n)
    (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F) (hP : P ∈ harmA T.Q.c (wtA w) w.n) :
    P ∈ Submodule.span T.Q.c.F {Q | Q ∈ harmA (Dw := T.Q.Dw j) T.Q.c (wtA w) w.n ∧
      ∀ σ' : T.Q.c.F →+* ℂ, Real.log (∑ m ∈ Q.support, ‖σ' (Q.coeff m)‖) ≤ 140 * D.R.r * large₂.sc.L * absA w} := by
  have hrk := rank_of_pins h.pins hj
  have h2 := PfTies1.DF_wtA_le (T.Q.Dw j) w
  have h3 : (((∑ t, ((∑ i, w.aP t i) + ∑ i, w.aM t i) : ℕ)) : ℝ) = absA w := by simp [absA]
  have hDF : (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℝ) ≤ absA w := by rw [← h3]; exact_mod_cast h2
  have hDF' : (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℝ) ≤ (WeightAlgebra.DF w : ℝ) := by exact_mod_cast h2
  have hfd : FD.fdeg D.host.E = D.R.f := by unfold FD.fdeg; rw [hostSize_finrank D]; omega
  obtain ⟨-, r1, -, -, r4, -, -, r7, r8⟩ := hrows
  have key := (GlobalTheory.StdHarm.harmA_mem_span_short D.host.E T.Q.H (T.Q.Dw j) T.Q.l T.Q.c w.n).2
    (hrk ▸ hr) (wtA w) large₂.sc.L hL (by rw [log_rdE]; exact r1) (by rw [hfd]; exact r4)
    (le_trans (Real.log_le_log (by positivity) (by linarith)) r7) r8 P hP
  refine Submodule.span_mono ?_ key
  intro Q hQ
  refine ⟨hQ.1, fun σ' => (hQ.2 σ').trans ?_⟩
  rw [hrk]
  have : (0 : ℝ) ≤ large₂.sc.L := by linarith
  gcongr

theorem noBase : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ReciprocityTheory.ChartRestriction.G.PullbackSections.NoBaseSt := by
  intro hC D T h large₂ j hj w hrows hL hr hlast hDF hα σ hσ k
  obtain ⟨inst, hnab⟩ := h.nabPin j hj
  letI := inst
  have hT := h.thTot j hj
  obtain ⟨x0, hx0⟩ := dom_nonempty ((T.U j σ).X k)
  have hM : 4 * WeightAlgebra.DF w + 4 ≤ T.Q.l.M := by
    rw [h.pins.2.1.1]
    have e0 : WeightAlgebra.DF w + 2 ≤ D.host.g 0 := le_trans hDF (min_le_left _ _)
    have e1 : WeightAlgebra.DF w + 2 ≤ D.host.g 1 := le_trans hDF (min_le_right _ _)
    nlinarith [Nat.mul_le_mul e0 e1]
  obtain ⟨f, ⟨x, P, hP, hfP⟩, hf0⟩ := GlobalTheory.T.thetaGenerators_noCommonZero_of_chartIndependence hC D T h j hj w hr hlast hM hα σ hσ k x0 hx0
  by_contra hno
  push_neg at hno
  obtain ⟨N, cf, g, hsum⟩ := Submodule.mem_span_set'.1 (mem_span_short D T h large₂ j hj w hrows hL hr P hP)
  choose gi hgi using fun i => (existsUnique_thRule _ _ _ hT x (g i).2.1).exists
  have hlin := (GlobalTheory.T.theta_rules_linear_and_level_congruence hC D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c (T.nab j) hnab (wtA w) w.n).1
    x N cf (fun i => (g i : _)) f gi (fun i => (g i).2.1) (by rw [hsum]; exact hP) (by rw [hsum]; exact hfP) hgi
  apply hf0
  have hz : ∀ i, rdU (T.U j σ) (gi i) k x0 = 0 := fun i =>
    hno x (g i) (gi i) (g i).2.1 (g i).2.2 (hgi i) x0 hx0
  rw [hlin, map_sum]
  simp only [LinearMap.map_smulₛₗ, Finset.sum_apply, Pi.smul_apply, hz, smul_zero, Finset.sum_const_zero]

end GlobalTheory.NoBase
