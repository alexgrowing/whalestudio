import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDatumEqOfSameLattice
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianDatum_eq_of_same_lattice : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (d d' : LocNG.Datum P) (τ τ' : Term V M r), LocNG.IsTermOver P d τ → LocNG.IsTermOver P d' τ' → τ.abelian₂ = τ'.abelian₂ → d = d' := by
  first | exact @GlobalTheory.HL.LatUniq.datum_of_lattice | exact GlobalTheory.HL.LatUniq.datum_of_lattice | (intros; apply GlobalTheory.HL.LatUniq.datum_of_lattice <;> assumption)
