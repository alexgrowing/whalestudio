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
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SaturationChartsHolds
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ErealLeMulOfForallLe
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIntegralChartIntegralFramedPoint
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.NuAlgLeOfCharts
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightOnDatum
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

namespace GlobalTheory.DepthBd

section Gen
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]

theorem nuW_eq_zero (hE : IntChartEx Xo c) (hS : ChartSaturated Xo c) (la : HeightOneSpectrum (𝓞 c.F)) (k : ℕ)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (ha : DomW Dw a) (hn : Fintype.card (Lt1 Dw) ≤ n)
    (hl : Formalism.L2.Pj.DF Dw a < resCharOf la) : nuW Xo c la k a n = 0 := by
  refine max_eq_left ?_
  refine iSup_le fun T => iSup_le fun io => iSup_le fun e => iSup_le fun ho => iSup_le fun y => iSup_le fun hy => ?_
  obtain ⟨C⟩ := hE T io y hy
  letI := io.toAlgebra
  exact (iInf_le _ C).trans ((crude_inf C.ch.B C.ch.h C.ch.gauge H.w0 k C.ch.uvec (satDir_of hS C) a n ha hn ho).2 hl)

theorem nuLocC_le_nuW (hI : ChartIndep Xo c) (la : HeightOneSpectrum (𝓞 c.F)) (k : ℕ)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (ho : OverLa la T.V io e)
    (z : IntFr Xo c T io) (hz : z.IsAlg) (C : IntegralChartA3 Xo c T io z) :
    nuLocC C e k a n ≤ nuW Xo c la k a n := by
  have h1 : nuLocC C e k a n ≤ nuLoc z e k a n := le_iInf fun C' => (hI T io z C C' e k a n).le
  refine h1.trans (le_trans ?_ (le_max_right _ _))
  unfold nuSup
  exact le_iSup_of_le T (le_iSup_of_le io (le_iSup_of_le e (le_iSup_of_le ho (le_iSup_of_le z
    (le_iSup_of_le hz le_rfl)))))
end Gen

theorem ereal_unit {x : EReal} {r d q : ℝ} (hr : 0 < r) (hd : 0 ≤ d) (hq : 0 < q) (h0 : 0 ≤ x)
    (h1 : x ≤ max 0 ((r * d / q : ℝ) : EReal)) :
    x = ((r * (x.toReal / r) : ℝ) : EReal) ∧ 0 ≤ x.toReal / r ∧ x.toReal / r ≤ d / q := by
  have hb : (0 : ℝ) ≤ r * d / q := by positivity
  rw [max_eq_right (by exact_mod_cast hb)] at h1
  have ht : x ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) h1
  have hb' : x ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) h0
  lift x to ℝ using ⟨ht, hb'⟩
  have h0' : 0 ≤ x := by exact_mod_cast h0
  have h1' : x ≤ r * d / q := by exact_mod_cast h1
  rw [EReal.toReal_coe]
  refine ⟨by rw [mul_div_cancel₀ _ hr.ne'], by positivity, ?_⟩
  rw [div_le_iff₀ hr]
  calc x ≤ r * d / q := h1'
    _ = d / q * r := by ring

theorem nuWt_bounds : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j), 2 * D.R.f * D.R.r ≤ w.n → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)), letI := T.Q.H.starRing; nuW (T.Q.Xo j) T.Q.c la T.Q.l.M (wtA w) w.n = (((ramOverZ la : ℝ) * nuWt T w la : ℝ) : EReal) ∧ 0 ≤ nuWt T w la ∧ nuWt T w la ≤ (WeightAlgebra.DF w : ℝ) / ((resCharOf la : ℝ) - 1) ∧ (WeightAlgebra.DF w < resCharOf la → nuWt T w la = 0) ∧ ∀ (T' : CDVR) (io : T.Q.c.F →+* T'.Fr) (e : ℕ), OverLa la T'.V io e → ∀ z : IntFr (T.Q.Xo j) T.Q.c T' io, z.IsAlg → ∀ C : IntegralChartA3 (T.Q.Xo j) T.Q.c T' io z, nuLocC C e T.Q.l.M (wtA w) w.n ≤ (((ramOverZ la : ℝ) * nuWt T w la : ℝ) : EReal) := by
  intro D T h j hj w hn la
  letI := T.Q.H.starRing
  have hst : ∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a := fun _ => rfl
  obtain ⟨hDF, hdom, -, -, hcard, -⟩ := GlobalTheory.WeightOnDatum.weight_on_datum D T.toCore h.pins j hj w
  have hE : IntChartEx (T.Q.Xo j) T.Q.c :=
    (GlobalTheory.IntChartExists.intChart_exists _ _ _ _ (T.Q.Xo j) T.Q.c).2.1 hst
  have hI : ChartIndep (T.Q.Xo j) T.Q.c := GlobalTheory.ChartCmp.chartIndep_holds _ _ _ _ (T.Q.Xo j) T.Q.c hst
  have hS : ChartSaturated (T.Q.Xo j) T.Q.c := SaturatedCharts.saturation_charts_holds _ _
  have hn' := hcard.trans hn
  have hr : (0 : ℝ) < (ramOverZ la : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (GlobalTheory.GoodDepth.ramOverZ_ne_zero' la)
  have hq : (0 : ℝ) < (resCharOf la : ℝ) - 1 := by
    have : (1 : ℝ) < resCharOf la := by exact_mod_cast (Crude.resCharOf_prime la).one_lt
    linarith
  have hle := nuW_le_crude hE hS la T.Q.l.M (wtA w) w.n hdom hn'
  rw [hDF] at hle
  obtain ⟨a1, a2, a3⟩ := ereal_unit hr (Nat.cast_nonneg (WeightAlgebra.DF w)) hq (le_max_left _ _) hle
  refine ⟨a1, a2, a3, fun hl => ?_, fun T' io e ho z hz C => ?_⟩
  · unfold nuWt
    rw [nuW_eq_zero hE hS la T.Q.l.M (wtA w) w.n hdom hn' (hDF ▸ hl)]
    simp
  · exact (nuLocC_le_nuW hI la T.Q.l.M (wtA w) w.n T' io e ho z hz C).trans a1.le

end GlobalTheory.DepthBd
