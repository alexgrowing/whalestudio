import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.H1algDefStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.RPfVal
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ConjugateMinimaInstance
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GramSpace
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.QBound
import Formalism.LocalToGlobal.ProjectiveLattices.DepRun
import Formalism.LocalToGlobal.ProjectiveLattices.RegXInst
import Formalism.LocalToGlobal.ProjectiveLattices.Adm3OfExtension
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocalAndSum
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaLatticeDepthLeUnscaledAddBoundaryStatement
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

namespace GlobalTheory.PtTie

theorem combBound_of_depth_le {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : WeightAlgebra.PJ D B P j}
    {ka wL wF : WeightFamilies.Wt D j} {S : WeightAlgebra.Scal B} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ}
    (G : GlobalFamilyData X ka wL wF) (c : ℝ) (hc0 : 0 ≤ c)
    (hH1 : ∀ la (y : X.Pt la), X.depth S.sW wL la y ≤ ((nus la + c * X.phiC la y : ℝ) : EReal))
    (hEt : j < D.R.m → 0 < G.iet ∧
      ∀ la (y : X.Pt la), ((2 * G.iet * X.phiC la y : ℝ) : EReal) ≤ X.vAt la y (X.inc _ G.et)) :
    Formalism.MainNotions.Gaps.EtaleWeightGaps.CombBound G S c nus := by
  intro la y
  have hφ := Formalism.MainNotions.Gaps.T0.phiC_nonneg X la y
  have hd := hH1 la y
  refine ⟨fun hj => ?_, fun hj => ?_⟩
  · obtain ⟨hi, h⟩ := hEt hj
    have hi' : (0 : ℝ) < 2 * (G.iet : ℝ) := by positivity
    have h1 := h la y
    have h0 : (0 : ℝ) ≤ 2 * G.iet * X.phiC la y := mul_nonneg hi'.le hφ
    refine ⟨le_trans (by exact_mod_cast h0) h1, fun hfin => hd.trans ?_⟩
    rw [← EReal.coe_toReal hfin (X.vAt_ne_bot la y _), EReal.coe_le_coe_iff] at h1
    rw [EReal.coe_le_coe_iff]
    have h2 : X.phiC la y ≤ (X.vAt la y (X.inc _ G.et)).toReal / (2 * (G.iet : ℝ)) := by
      rw [le_div_iff₀ hi']; linarith
    have h4 : c * X.phiC la y ≤ c * ((X.vAt la y (X.inc _ G.et)).toReal / (2 * (G.iet : ℝ))) :=
      mul_le_mul_of_nonneg_left h2 hc0
    have h5 : c / (2 * (G.iet : ℝ)) * (X.vAt la y (X.inc _ G.et)).toReal =
        c * ((X.vAt la y (X.inc _ G.et)).toReal / (2 * (G.iet : ℝ))) := by ring
    rw [h5]
    linarith
  · have h0 : X.phiC la y = 0 := by
      unfold WeightAlgebra.PJ.phiC
      rw [if_neg (not_lt.2 hj)]
    rw [h0, mul_zero, add_zero] at hd
    exact hd

theorem combBound_alg : (∀ (p : ℕ) [Fact p.Prime], Pdiv.ChartF.HTFSt p) → ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (w : WeightFamilies.Wt D j) (c : ℝ), Oriented T EX → RunNum D w c → ∀ (ka wF : WeightFamilies.Wt D j) (S : WeightAlgebra.Scal (recB h.toLawsCore)) (G : GlobalFamilyData (recPJ h j hj) ka w wF), S.sW = sWt (recB h.toLawsCore) hinj EX w → (j < D.R.m → 0 < G.iet ∧ EtVal h j hj G.iet G.et) → CombBound G S c (nusOf (recB h.toLawsCore) w (nuWt T w)) := by
  intro hH D T h j hj hinj EX w c hO hR ka wF S G hS hEt
  refine combBound_of_depth_le G c hR.2.2.2.1 (fun la y => ?_) hEt
  rw [hS]
  exact GlobalTheory.T.thetaLattice_depth_le_unscaled_add_boundary hH D T h j hj hinj EX w c hO hR la y

end GlobalTheory.PtTie
