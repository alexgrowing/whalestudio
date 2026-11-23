import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
import Formalism.LocalToGlobal.ProjectiveLattices.LatPAddRight
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.DepLaws
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelGoodAndHalfEqPrimeProductStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFlagModelBaseChangeIntegralFramedPointStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDegenerationDataAlgebraicPointModelStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PeriodFormAdditiveBalancedPosDefBoundedRankStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLocalDataPrescribedPointsFlagStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTower
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DegenerationDataCoordsNeZeroLatticesIsomorphicStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.MainNotions.DIV.Cons
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocalData

def FactorsFin {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    (Y : Model Xo c β) {p : ℕ} {C : SCF p} (P : PointsOfFlagModel.PtC Y C) : Prop :=
  ∃ (T : CDVR) (g : T.V →+* intO ↥C.S) (ιT : Sp T.V ⟶ Y.X), T.FinRes ∧ Function.Injective g ∧
    (∀ a ∈ maximalIdeal T.V, ‖((g a : intO ↥C.S) : ↥C.S)‖ < 1) ∧ spMap g ≫ ιT = P.yt

theorem half_degree (D : D7) : Module.finrank ℚ D.host.E / 2 = D.R.f := by
  rw [D.host.finrank_cmField]
  unfold Ranks.f Ranks.n
  omega

theorem bar_eq_of_conj (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (x x' : 𝓞 D.host.E)
    (h : (x' : D.host.E) = D.host.conj (x : D.host.E)) : H.bar x = x' := by
  apply IsFractionRing.injective (𝓞 D.host.E) D.host.E
  exact (H.bar_eq x).trans ((barE_eq_conj D x).trans h.symm)

theorem laws_of_factorsFin (D : D7) (Q : Par D) (hQ : Q.Pins) {j : ℕ} (hj : 1 ≤ j) (hm : j < D.R.m) {p : ℕ}
    (hp : p.Prime) {O : Type} [CommRing O] {β : O →+* Q.c.F} {Y : Model (Q.Xo j) Q.c β} {C : SCF p}
    {P : PointsOfFlagModel.PtC Y C} (hf : FactorsFin Y P) (A : DatAt Y P) :
    (∀ a b, A.toLatB.beta a b = A.toLatB.beta b a) ∧
    (∀ a a' b, A.toLatB.beta (a + a') b = A.toLatB.beta a b + A.toLatB.beta a' b) ∧
    (∀ (x x' : 𝓞 D.host.E), (x' : D.host.E) = D.host.conj (x : D.host.E) →
      ∀ a b, A.toLatB.beta (x • a) b = A.toLatB.beta a (x' • b)) ∧
    (∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℤ A.toLatB.Y), ∀ x : ι → ℝ, x ≠ 0 →
      0 < ∑ i, ∑ k, x i * x k * A.toLatB.beta (b i) (b k)) ∧
    ∃ ρ : ℕ, Module.finrank ℤ A.toLatB.Y = 2 * D.R.f * ρ ∧ ρ ≤ (D.R.sigW j).1 ∧ ρ + (D.R.sigW j).1 ≤ D.R.r := by
  obtain ⟨T, g, ιT, h1, h2, h3, h4⟩ := hf
  obtain ⟨ha, hb, hc, ρ, hr1, hr2, hr3⟩ := GlobalTheory.T.periodForm_additive_balanced_posDef_boundedRank D.host.E Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c O β Y p C
    P hp T g ιT h1 h2 h3 h4 A
  obtain ⟨hp1, hq1, -⟩ := hQ.2.2.2 j ⟨hj, hm.le⟩
  rw [hp1] at hr2
  rw [hq1] at hr3
  rw [half_degree D] at hr1
  refine ⟨A.beta_symm, ha, fun x x' hx a b => ?_, hc, ρ, hr1, hr2, ?_⟩
  · rw [← bar_eq_of_conj D Q.H x x' hx]
    exact hb x a b
  · simp only [Ranks.sigW, Ranks.r] at hr3 ⊢
    omega

theorem uniq_of_factorsFin {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    {Y : Model Xo c β} {p : ℕ} (hp : p.Prime) {C : SCF p} {P : PointsOfFlagModel.PtC Y C} (hf : FactorsFin Y P)
    (A A' : DatAt Y P) : ∃ e : A.toLatB.Y ≃ₗ[𝓞 E] A'.Ylat, ∀ a b, A'.beta (e a) (e b) = A.toLatB.beta a b := by
  obtain ⟨T, g, ιT, h1, h2, h3, h4⟩ := hf
  exact (GlobalTheory.T.degenerationData_coords_ne_zero_lattices_isomorphic E H Dw l Xo c O β Y p C P hp T g ιT h1 h2 h3 h4 A A').2

theorem localData_exists :
    ∀ (D : D7) (Q : Par D), Q.Pins → (∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q) → Packet66Rest Q := by
  intro D Q hQ hpq
  have hgood := (GlobalTheory.T.level_good_and_half_eq_prime_product D Q.H Q.l hQ.1.2.1 hQ.2.1.1).1
  choose Tw hTw using fun j p => Towers.exists_tower D.host.E Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c (hpq j) hgood p
  have hdat : ∀ j p (z : PointsOfFlagModel.Pt (Tw j p) .yy), p.Prime → FactorsFin ((Tw j p).Y z.1) z.2.2.1 →
      Nonempty (DatAt ((Tw j p).Y z.1) z.2.2.1) := by
    rintro j p z hp ⟨T, g, ιT, h1, h2, h3, h4⟩
    obtain ⟨A, -⟩ := GlobalTheory.T.exists_degeneration_data_algebraic_point_model D.host.E Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c _ _ _ p _ z.2.2.1 hp T g ιT h1 h2 h3 h4
    exact ⟨A⟩
  let Pt : ℕ → ℕ → Type := fun j p => {z : PointsOfFlagModel.Pt (Tw j p) .yy //
    (1 ≤ j ∧ j < D.R.m) ∧ p.Prime ∧ FactorsFin ((Tw j p).Y z.1) z.2.2.1}
  have A0 : ∀ j p (y : Pt j p), DatAt ((Tw j p).Y y.1.1) y.1.2.2.1 := fun j p y =>
    Classical.choice (hdat j p y.1 y.2.2.1 y.2.2.2)
  obtain ⟨P, dat, hP⟩ := GlobalTheory.T.exists_localData_prescribed_points_flag D Pt (fun j p y => PointsOfFlagModel.fld y.1) (fun j p y => (A0 j p y).toLatB)
    (fun j p y => laws_of_factorsFin D Q hQ y.2.1.1 y.2.1.2 y.2.2.1 y.2.2.2 (A0 j p y))
  let G : In66 Q :=
    { P := P
      dat := dat
      Tw := Tw
      rel := fun j p η z => (P.loc (dat j) p).fld η = PointsOfFlagModel.fld z ∧
        ∀ A : DatAt ((Tw j p).Y z.1) z.2.2.1, ∃ e : (P.loc (dat j) p).Ylat η ≃ₗ[𝓞 D.host.E] A.Ylat,
          ∀ a b, A.beta (e a) (e b) = (P.loc (dat j) p).be η a b }
  have hfac : ∀ j la z, G.IsAlgPt j la z → FactorsFin ((Tw j (WeightAlgebra.resCh la)).Y z.1) z.2.2.1 := by
    rintro j la z ⟨T, io, e, y, ho, hy, hz⟩
    obtain ⟨g, ιT, h2, h3, h4⟩ := (GlobalTheory.T.exists_flag_model_baseChange_integral_framed_point D.host.E Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c la (Tw j _)
      (hTw j _ (resCh_prime la)) T io e ho y hy).2 z hz
    exact ⟨T, g, ιT, hy, h2, h3, h4⟩
  refine ⟨G, fun j hj hm => (hP j hj hm).1, fun j _ _ p hp => hTw j p hp,
    fun j _ _ la z hz => hdat j _ z (resCh_prime la) (hfac j la z hz), fun j hj hm la z hz => ⟨?_, fun η h => h.1⟩,
    fun j _ _ la z _ η h => h.2, fun j _ _ la T io e ho y hy => ?_⟩
  · let y : Pt j (WeightAlgebra.resCh la) := ⟨z, ⟨hj, hm⟩, resCh_prime la, hfac j la z hz⟩
    obtain ⟨η, h1, e, he⟩ := (hP j hj hm).2 _ y
    refine ⟨η, h1, fun A => ?_⟩
    exact (uniq_of_factorsFin (resCh_prime la) y.2.2.2 (A0 j _ y) A).elim fun e' he' =>
      ⟨e.trans e', fun a b => (he' (e a) (e b)).trans (he a b)⟩
  · exact (GlobalTheory.T.exists_flag_model_baseChange_integral_framed_point D.host.E Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c la (Tw j _)
      (hTw j _ (resCh_prime la)) T io e ho y hy).1

end GlobalTheory.LocalData
