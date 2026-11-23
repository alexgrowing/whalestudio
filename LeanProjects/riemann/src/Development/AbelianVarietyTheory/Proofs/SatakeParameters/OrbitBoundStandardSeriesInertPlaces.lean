import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BeData
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementB
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WordFreeNumberLeOrbitBound
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardOrbitSeriesValuationBoundZeroStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KvalGeOrbitGainWithoutOperatorStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual addC thetaInZ sumE)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.OrbitBoundStdRec

theorem kvalGe_le {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 l : ℕ) [Fact l.Prime] (nu : Lt → YoungDiagram)
    (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) {B B' : ℝ} (h : B' ≤ B) (H : product_zeroth_first_parts.KvalGe N0 N1 l nu Th B) :
    product_zeroth_first_parts.KvalGe N0 N1 l nu Th B' := fun I m =>
  (H I m).trans (Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (Fact.out : l.Prime).one_lt.le) (neg_le_neg h))

theorem orbit_bound_rec : ∀ (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (Ee : OrbitPlaces.Ent D), OrbitPlaces.Shape D L X Ee →
    (∀ u, ∀ i < D.R.m, ∀ t ∈ D.host.TT, Ee.row u i (false, t) 0 - Ee.row u i (false, t) 1 ≤ 2 * L.sc.a) → 5 ≤ K.dl1 → 4 ≤ K.dl2 →
    BeFam D Ee.ep Ee.be → (Ee.sg = fun _ _ => -1) → OrbitPlaces.OrbitBoundWithoutOperator Ee X K := by
  intro D L X K Ee hS hG hd1 hd2 hBe hsg
  intro w h hC0 hh hX u j hj t0 ht0 Th hB
  have hEv : HEv D (D.what₂.places.resChar w) := by
    have he := h.even
    unfold nP at he
    rw [if_neg (GlobalTheory.KerStd.WordFree.not_signal hC0)] at he
    exact he
  obtain ⟨hep, hbe⟩ := hBe w (Or.inl ⟨hC0, hEv⟩)
  have hs : Ee.sg w (false, t0) = -1 := by rw [hsg]
  rw [hs] at hB
  have z0 := GlobalTheory.T.standardOrbitSeries_valuationBound_zero (OrbitPlaces.orbLoc Ee _ h u j (false, t0) Th) _ _ hep (hbe (false, t0)) hB
  have z1 := GlobalTheory.T.kvalGe_orbitGainWithoutOperator (OrbitPlaces.orbLoc Ee _ h u j (false, t0) Th) _ _ hep (hbe (false, t0)) hB
  have z2 := GlobalTheory.KerStd.WordFree.wordFreeNumber_le_orbitBound D L X K Ee hS hG hd1 hd2 _ h hC0 hh hX u j hj t0 ht0 Th
  rcases le_total (g0 X K (aL L) (bL L) (D.what₂.places.resChar w) (j + 1) t0) 0 with hm | hm
  · rw [max_eq_right hm]
    exact z0
  · rw [max_eq_left hm]
    exact kvalGe_le _ _ _ _ _ z2 z1

end GlobalTheory.OrbitBoundStdRec
