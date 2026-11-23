import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.KerExistsStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NonemptyTorusAt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsRankOneCuspDataLogBounds
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ThetaBound
import Formalism.LocalToGlobal.ProjectiveLattices.DatTheta
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsSmulMemLattice
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Parity
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConjHalfIntegralGenerator

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

namespace GlobalTheory.ExtraWeight

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem exists_multiple_mem (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (v : Fin r → E) :
    ∃ c : 𝓞 E, c ≠ 0 ∧ (c : E) • v ∈ X.Λ :=
  _root_.GlobalTheory.SmulMemOfSpan.exists_smul_mem_lattice X v

theorem herm_smul_smul (G : Matrix (Fin r) (Fin r) E) (a b : E) (x y : Fin r → E) :
    herm G (a • x) (b • y) = a * ReciprocityTheory.ChartRestriction.G.FD.cc b * herm G x y := by
  simp only [herm, ReciprocityTheory.ChartRestriction.G.FD.cc, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem exists_isIso (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) {ρ : ℕ} (cu : FJ.CuspFD X ρ) (hρ : 0 < ρ) :
    ∃ ξ : Fin r → E, X.IsIso ξ := by
  obtain ⟨c, hc, hm⟩ := exists_multiple_mem X (cu.e ⟨0, hρ⟩)
  refine ⟨_, hm, by rw [herm_smul_smul, cu.iso, mul_zero], ?_⟩
  exact smul_ne_zero (by simpa using hc) (cu.ind.ne_zero _)

theorem conj_cmHalfIntegralGenerator_eq_one_sub (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : ReciprocityTheory.ChartRestriction.G.FD.cc (H.w0 : E) = 1 - (H.w0 : E) :=
  _root_.GlobalTheory.CMConjugationOfSquareRoot.main H

theorem even_im_hermitian_sub (X : DataX E r) (w0 : 𝓞 E) (hw : ReciprocityTheory.ChartRestriction.G.FD.cc (w0 : E) = 1 - (w0 : E)) :
    ∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ,
      Algebra.trace ℚ E (X.ξ0 * herm X.Gm u (((w0 : E) - ReciprocityTheory.ChartRestriction.G.FD.cc (w0 : E)) • v)) -
        Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v) = 2 * k :=
  _root_.UpperTheory.Reformulated.B.Ue6.even_im_hermitian_sub X w0 hw

end General

theorem extra_weight_exists : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (w : WeightFamilies.Wt D j), GamAt T.toCore → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → j < D.R.m → (D.R.f : ℝ) ^ 2 ≤ D.host.rdE → 16 ≤ D.host.rdE → D.R.m ^ 4 ≤ D.R.f → ∀ k : (T.U j T.σ₀).Comp, BasePotentialExistence ((T.U j T.σ₀).X k) (de2W ((T.U j T.σ₀).X k)) D.R.r (1 / (2 * (5 : ℝ) ^ 4 * |(NumberField.discr D.host.E : ℝ)| ^ ((1 : ℝ) / D.R.f))) := by
  intro D T h j hj large₂ w hG hP hL hrn hjm hf2 hrd hm4 k
  obtain ⟨e, -⟩ := GlobalTheory.CuspDataBounds.cusp_data_bounds D T h hG large₂ j hj w hP hL hrn T.σ₀ T.good_σ₀
  have hfr : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField, Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]
    ring
  have hcard : ((T.U j T.σ₀).X k).Ψ.card = D.R.f := by
    have h2c := Formalism.L2.Pj.DatLin.two_card ((T.U j T.σ₀).X k).cmType
    rw [hfr] at h2c
    omega
  have hPf : ReciprocityTheory.ChartRestriction.G.I2.PT.f D.host.E = D.R.f := by
    unfold ReciprocityTheory.ChartRestriction.G.I2.PT.f
    omega
  have hPr : ReciprocityTheory.ChartRestriction.G.I2.PT.rd D.host.E = D.host.rdE := rfl
  have hp0 : ((T.U j T.σ₀).X k).p0 = D.R.m - j :=
    ((h.unf j hj T.σ₀ T.good_σ₀).2.1 k).1.trans (h.pins.2.2.2 j hj).2.1
  have hf1 : (1 : ℝ) ≤ D.R.f := by
    have : 0 < D.R.f := by unfold Ranks.f Ranks.n; positivity
    exact_mod_cast this
  obtain ⟨cu⟩ := h.cuNe j hj k
  have hρ : 0 < WeightFamilies.rho D j := by
    show 0 < D.R.m - j
    omega
  have key := GlobalTheory.ThetaWeight.exists_weight GlobalTheory.theta_bound_tStatement D.host.E D.R.r (e k).toX
    (exists_isIso _ cu hρ)
    ⟨⟨T.Q.H.w0, even_im_hermitian_sub _ _ (conj_cmHalfIntegralGenerator_eq_one_sub T.Q.H)⟩, by rw [hPf, hPr]; nlinarith, by rw [hPf, hPr]; exact hf2,
      by rw [hPr]; exact hrd, D.R.m, by omega, by rw [hPf]; exact hm4,
      Or.inl (by show ((T.U j T.σ₀).X k).p0 ≤ _; omega)⟩
  rw [← hcard]
  exact key

end GlobalTheory.ExtraWeight
