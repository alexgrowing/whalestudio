import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsIntIffOfNatural
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FieldOfDatumAbelian
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianCmCompLawsBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodDatumParametersStatement
import Development.AutomorphicArithmetic.PrimeDiscriminants.BadPrimes
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

namespace GlobalTheory.CompanionTheory.Ar.Plug

theorem deepStR_of_volume : GlobalTheory.CompanionTheory.Ar.Pub.NefRR → Top.Given → ArithIntersectionSystemStatement → BirationalPullbackPushforwardFormula → Top.GoodTowerExistsX →
    Top.VolumeTheoremX → DeepStR := by
  intro hN hG hA hG6 hTw hV
  obtain ⟨C, hC0, hC⟩ := GlobalTheory.T.abelian_cm_comp_laws_bound hN hG hA hG6 hTw hV
  refine ⟨C, hC0, ?_⟩
  intro D T hT hmk j hj1 hjm Y e o hY hcard
  obtain ⟨⟨h, e', hCL⟩, hgood, hq, hpq, hf, hrd, hL⟩ := GlobalTheory.T.good_datum_parameters hG D T hT j hj1 hjm Y e o hY
  haveI := GlobalTheory.CompanionTheory.Ar.Rec.field_of_datum_abelian D
  have hm2 := D.R.two_le_m
  have h2m : 2 * D.R.m ≤ D.R.m ^ 2 := by nlinarith
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hq1 : 1 ≤ (T.Q.Dw j).q := by omega
  have hq3 : 3 * (T.Q.Dw j).q + 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by omega
  have hf2 : 2 ≤ Fintype.card (CMType T.Q.H) := by
    rw [hf]
    show 2 ≤ 2 * D.R.ord
    have := D.R.ord_pos
    omega
  have hcard' : (Nat.primeFactors (2 * (discr D.host.E).natAbs) ∪ Y.d.l₂.M'.primeFactors).card ≤
      4 * Fintype.card (CMType T.Q.H) * ((T.Q.Dw j).p + (T.Q.Dw j).q) ^ 2 := by
    classical
    have h1 := D.host.card_bad_gt_le Y.d.l₂.M'.primeFactors (B := (D.R.n : ℝ)) le_rfl
    set S := Nat.primeFactors (2 * (discr D.host.E).natAbs) ∪ Y.d.l₂.M'.primeFactors
    have h2 := Finset.card_filter_add_card_filter_not (s := S) (fun p : ℕ => (D.R.n : ℝ) < (p : ℝ))
    have h3 : (S.filter fun p : ℕ => ¬ (D.R.n : ℝ) < (p : ℝ)).card ≤ D.R.n + 1 := by
      refine (Finset.card_le_card (t := Finset.range (D.R.n + 1)) fun p hp => ?_).trans (by simp)
      have : (p : ℝ) ≤ D.R.n := not_lt.1 (Finset.mem_filter.1 hp).2
      have : p ≤ D.R.n := by exact_mod_cast this
      exact Finset.mem_range.2 (by omega)
    have h4 : Fintype.card (CMType T.Q.H) = 2 * D.R.n := hf
    have h5 : 16 ≤ ((T.Q.Dw j).p + (T.Q.Dw j).q) ^ 2 := by nlinarith
    have h6 : 4 * Fintype.card (CMType T.Q.H) * 16 ≤ 4 * Fintype.card (CMType T.Q.H) * ((T.Q.Dw j).p + (T.Q.Dw j).q) ^ 2 :=
      Nat.mul_le_mul_left _ h5
    omega
  have key := hC D.host.E T.Q.H (T.Q.Dw j) Y.d.l₂ Y.d.Xo₂ Y.d.c₂ D.R.r Y.U h e' hCL
    (GlobalTheory.CompanionTheory.Ar.Ref.unifAll_holds _ _) hY.geo hgood hY.lev.2 hq1 hq3 hf2 hcard' (xiR D) hY.xiAbs
  rw [hrd, hL] at key
  exact key

end GlobalTheory.CompanionTheory.Ar.Plug
