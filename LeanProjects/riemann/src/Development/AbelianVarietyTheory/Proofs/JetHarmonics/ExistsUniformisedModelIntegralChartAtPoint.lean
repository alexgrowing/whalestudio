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
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntChartFrTruncExists
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.VVNonnegIffLeOne
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BaseChangeOfFiniteExtension
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarRingExtOfStar
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaRuleIntegralPointValueBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsExtensionAllModelsUniformizedStatement

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

namespace GlobalTheory.UnifPoint

theorem exists_uniformised_chart : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtA j la), letI := T.Q.H.starRing; ∃ (T' : CDVR) (io : T.Q.c.F →+* T'.Fr) (e : ℕ) (_ : OverLa la T'.V io e) (z : IntFr (T.Q.Xo j) T.Q.c T' io) (_ : z.IsAlg) (_ : T.G.lies j la T' io z (imgV y)) (C : IntegralChartA3 (T.Q.Xo j) T.Q.c T' io z) (P : PELUnif (maximalIdeal T'.V) C.I.G), FrTrunc C.I.G (𝟙 (Sp T'.V)) (chD C.ch) C.xT C.eT ∧ P.TorsionIso ∧ ∀ w : WeightFamilies.Wt D j, ∀ f ∈ T.th j w, vAtV y f = nval T'.V e (evI z f) := by
  intro D T h j hj la y
  letI := T.Q.H.starRing
  obtain ⟨q, S, io, e, ho, z, hz, eta, heta, rfl⟩ := y
  obtain ⟨S', io', z', r, hz', hr, hU, φ, hv, hm⟩ := GlobalTheory.T.exists_extension_all_models_uniformized _ _ _ _ (T.Q.Xo j) T.Q.c S io z hz
  letI := io.toAlgebra
  let ψ : S.Fr →+* S'.Fr := letI := io'.toAlgebra; φ.toRingHom
  have hio : io' = ψ.comp io := by
    letI := io'.toAlgebra
    exact RingHom.ext fun a => (φ.commutes a).symm
  have hv' : ∀ a : S.Fr, vV S'.V (ψ a) = (r : ℤ) * vV S.V a := fun a => by
    by_cases ha : a = 0
    · simp [ha, vV]
    · exact hv a ha
  have hfin : ψ.Finite := IntegralFrameAllCompare.finite_of_scale ψ hr hv' hz'
  have hnab : IsNab (T.Q.Xo j) T.Q.c (T.nab j) := by
    obtain ⟨inst, hn⟩ := h.nabPin j hj
    obtain rfl := GlobalTheory.PowGerm.starSt _ T.Q.H inst hn.1
    exact hn
  have hev : ∀ w : WeightFamilies.Wt D j, ∀ f ∈ T.th j w, ψ (evI z f) = evI z' f := fun w f hf =>
    GlobalTheory.T.thetaRule_integralPoint_value_baseChange _ _ _ _ (T.Q.Xo j) T.Q.c (T.nab j) hnab S S' io io' z z' φ hm _ _ f hf
  have hx : letI := io'.toAlgebra; z'.1.x = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap ψ ≫ z.1.x := hm.1
  have hu : letI := io'.toAlgebra
      ∀ τ i, z'.1.u τ i = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.1.u τ i := hm.2.1
  clear_value ψ
  clear hm hv φ
  subst hio
  obtain ⟨C, hCh⟩ := GlobalTheory.IntChartTrunc.intChart_frTrunc_exists _ T.Q.H _ _ (T.Q.Xo j) T.Q.c (fun _ => rfl) S' _ z'
  obtain ⟨P, hP⟩ := hU C.I
  refine ⟨S', ψ.comp io, r * e, ho.bc ψ hr hv', z', hz', fun hjm => ?_, C, P, hCh, hP, fun w f hf => ?_⟩
  · obtain ⟨u, hu', hl⟩ := heta hjm
    exact ⟨u, hu', GlobalTheory.LiesBaseChange.baseChange_of_finite_extension la _ S S' io ψ z z' hfin hr hv' hx hu u hl⟩
  · rw [← hev w f hf, nval_bc ψ hr hv']
    rfl

end GlobalTheory.UnifPoint
