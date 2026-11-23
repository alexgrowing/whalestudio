import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import Formalism.LocalToGlobal.ProjectiveLattices.LiesOverBaseChange

noncomputable section

namespace Formalism.L2.Pj

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {D : D7} (Q : Par D)

structure In66 : Type 1 where
  P : ModuliIntegralCharts.Prov D
  dat : ℕ → P.Dat
  Tw : ∀ j p, PointsOfFlagModel.Tower p (Q.Xo j) Q.c
  rel : ∀ j p, (P.loc (dat j) p).Pt (P.loc (dat j) p).YY → PointsOfFlagModel.Pt (Tw j p) .yy → Prop

namespace In66

variable {Q} (G : In66 Q)

abbrev PY (j p : ℕ) : Type := (G.P.loc (G.dat j) p).Pt (G.P.loc (G.dat j) p).YY

def PinDat : Prop := ∀ j, 1 ≤ j → j < D.R.m → G.P.rk (G.dat j) = D.R.r ∧ G.P.jj (G.dat j) = (D.R.sigW j).1

def PinTower : Prop := ∀ j, 1 ≤ j → j < D.R.m → ∀ p, p.Prime → PointsOfFlagModel.TowerAt (G.Tw j p)

def IsAlgPt (j : ℕ) (la : HeightOneSpectrum (𝓞 Q.c.F)) (z : PointsOfFlagModel.Pt (G.Tw j (WeightAlgebra.resCh la)) .yy) : Prop :=
  ∃ (T : CDVR) (io : Q.c.F →+* T.Fr) (e : ℕ) (y : IntFr (Q.Xo j) Q.c T io), OverLa la T.V io e ∧
    algCls (Q.Xo j) Q.c T io y ∧ LiesOverBaseChange la (G.Tw j (WeightAlgebra.resCh la)) T io y z

def HasData : Prop := ∀ j, 1 ≤ j → j < D.R.m → ∀ la z, G.IsAlgPt j la z →
  Nonempty (DatAt ((G.Tw j (WeightAlgebra.resCh la)).Y z.1) z.2.2.1)

def PinPts : Prop := ∀ j, 1 ≤ j → j < D.R.m → ∀ la z, G.IsAlgPt j la z →
  (∃ η, G.rel j _ η z) ∧ ∀ η, G.rel j _ η z → (G.P.loc (G.dat j) _).fld η = PointsOfFlagModel.fld z

def PinLat : Prop := ∀ j, 1 ≤ j → j < D.R.m → ∀ la z, G.IsAlgPt j la z → ∀ η, G.rel j _ η z →
  ∀ A : DatAt ((G.Tw j (WeightAlgebra.resCh la)).Y z.1) z.2.2.1,
    ∃ e : (G.P.loc (G.dat j) _).Ylat η ≃ₗ[𝓞 D.host.E] A.Ylat,
      ∀ a b, A.beta (e a) (e b) = (G.P.loc (G.dat j) _).be η a b

def BaseChange : Prop := ∀ j, 1 ≤ j → j < D.R.m →
  ∀ (la : HeightOneSpectrum (𝓞 Q.c.F)) (T : CDVR) (io : Q.c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e →
    ∀ y : IntFr (Q.Xo j) Q.c T io, algCls (Q.Xo j) Q.c T io y →
      ∃ z, LiesOverBaseChange la (G.Tw j (WeightAlgebra.resCh la)) T io y z

def lies (j : ℕ) (la : HeightOneSpectrum (𝓞 Q.c.F)) (T : CDVR) (io : Q.c.F →+* T.Fr)
    (y : IntFr (Q.Xo j) Q.c T io) (η : G.PY j (WeightAlgebra.resCh la)) : Prop :=
  j < D.R.m → ∃ z, G.rel j (WeightAlgebra.resCh la) η z ∧ LiesOverBaseChange la (G.Tw j (WeightAlgebra.resCh la)) T io y z

end In66

theorem resCh_prime {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) : (WeightAlgebra.resCh la).Prime := by
  unfold WeightAlgebra.resCh
  haveI := la.isPrime
  haveI : Finite (𝓞 K ⧸ la.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot la.asIdeal la.ne_bot
  first
  | exact CharP.char_is_prime (𝓞 K ⧸ la.asIdeal) _
  | exact (CharP.char_is_prime_or_zero (𝓞 K ⧸ la.asIdeal) _).resolve_right
      (ringChar.char_ne_zero_of_finite _)

variable {Q}

theorem In66.liesTotal (G : In66 Q) (h1 : G.PinPts) (h2 : G.BaseChange) {j : ℕ} (hj : InR D j) :
    LiesTotal (Q.Xo j) Q.c (algCls (Q.Xo j) Q.c) (fun la => G.PY j (WeightAlgebra.resCh la)) (G.lies j) := by
  intro la T io e ho y hy
  by_cases hm : j < D.R.m
  · obtain ⟨z, hz⟩ := h2 j hj.1 hm la T io e ho y hy
    obtain ⟨η, hη⟩ := (h1 j hj.1 hm la z ⟨T, io, e, y, ho, hy, hz⟩).1
    exact ⟨η, fun _ => ⟨z, hη, hz⟩⟩
  · exact ⟨(G.P.ex (G.dat j) (WeightAlgebra.resCh la)).yEta
      (Classical.choice ((G.P.ex (G.dat j) (WeightAlgebra.resCh la)).genNe _)), fun h => absurd h hm⟩

end Formalism.L2.Pj
