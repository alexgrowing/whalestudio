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
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SpanResCharNeBot
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsReducedBasisLePhiCy
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEqSmulOne
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

namespace GlobalTheory.ShortBasisAt

theorem rootDiscriminantDegreeRatio_eq (D : D7) : rr0 D = D.host.rdE ^ 2 / (4 * D.R.f) := by
  unfold rr0 Formalism.BasicNotions.Host.rdE
  rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _), GlobalTheory.PinNum.finrank_host]
  push_cast
  congr 1
  · congr 1
    ring
  · ring

theorem exists_shortBasis : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (T' : CDVR) (io : T.Q.c.F →+* T'.Fr) (e : ℕ) (ho : OverLa la T'.V io e) (z : IntFr (T.Q.Xo j) T.Q.c T' io) (hz : z.IsAlg) (η : T.G.PY j (WeightAlgebra.resCh la)) (hl : T.G.lies j la T' io z η), letI := T.Q.H.starRing; ∀ (C : IntegralChartA3 (T.Q.Xo j) T.Q.c T' io z) (P : PELUnif (maximalIdeal T'.V) C.I.G) (ϖ : T'.V), Irreducible ϖ → ∀ Q : P.D.toPre.X → ℤ, IsQ P.D.toPre ϖ Q → ∃ (r : ℕ) (Φ M0 : ℝ), ShortBasis Q r Φ M0 ∧ r ≤ 2 * D.R.f * D.R.m ∧ M0 ≤ 2 * Real.sqrt (2 * D.R.f * D.R.m) ∧ (D.R.m ≤ j → M0 = 0 ∧ Φ = 0) ∧ Φ ≤ e * (rr0 D * (2 * D.R.f * D.R.m : ℝ) ^ 3 * (recPJ h j hj).phiC la (PtV.mk la ho z hz η hl)) := by
  intro D T h j hj la T' io e ho z hz η hl C P ϖ hϖ Q hQ
  by_cases hm : j < D.R.m
  · obtain ⟨h0, r, b, hr, h1, h2⟩ :=
      GlobalTheory.PhiTie.exists_reduced_basis_le_phiCy D T h j hj hm la T' io e z ho hz η hl C P ϖ hϖ Q hQ
    have hφ : (recPJ h j hj).phiC la (PtV.mk la ho z hz η hl) =
        (ramOverZ la : ℝ) * (T.G.P.loc (T.G.dat j) (WeightAlgebra.resCh la)).phiCy η := by
      rw [← H1algLink.eWL_eq la]
      exact ConjugateMinimaInstance.phiC_rec_eq (recPJ h j hj) hm la _
    rw [hφ, rootDiscriminantDegreeRatio_eq]
    have hr' : (r : ℝ) ≤ 2 * D.R.f * D.R.m := by exact_mod_cast hr
    refine ⟨r, _, _, ⟨by positivity, b, h1, h2⟩, hr, by push_cast; exact le_rfl, fun h' => absurd hm (not_lt.2 h'), ?_⟩
    gcongr
  · letI := io.toAlgebra
    letI := T.Q.H.starRing
    obtain ⟨ρ, hρ, -, hq⟩ := GlobalTheory.ToricRank.rank_le_signature D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T'.V C.I.G P
      C.I.t' C.I.m2 z.1.x C.I.m1 inferInstance
    have hq' : ρ ≤ D.R.m - j := hq.trans_eq (h.toLawsCore.pins.2.2.2 j hj).2.1
    have h0 : Module.finrank ℤ P.D.toPre.X = 0 := by
      rw [hρ, show ρ = 0 by omega, mul_zero]
    have hφ : (recPJ h j hj).phiC la (PtV.mk la ho z hz η hl) = 0 := if_neg hm
    refine ⟨0, 0, 0, ⟨le_rfl, Module.finBasisOfFinrankEq ℤ _ h0, fun i => i.elim0, fun i => i.elim0⟩, Nat.zero_le _,
      by positivity, fun _ => ⟨rfl, rfl⟩, ?_⟩
    rw [hφ]; simp

end GlobalTheory.ShortBasisAt
