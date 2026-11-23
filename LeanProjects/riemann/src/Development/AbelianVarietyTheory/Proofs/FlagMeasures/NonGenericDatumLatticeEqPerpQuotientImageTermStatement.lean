import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonGenericDatumLatticeEqPerpQuotientImageTerm
import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
open Formalism.MainNotions.S

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonGenericDatum_lattice_eq_perpQuotientImage_term : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (r : ℕ) (P : LocNG.FPair H r) (d : LocNG.Datum P) (τ : Loc.Term V M r), LocNG.IsTermOver P d τ → (d.L : Set (H.Wb P.A.f)) = H.Lset τ.abelian₂ P.A.f ∧ (d.L' : Set (H.Wb P.B.f)) = H.Lset τ.abelian₂ P.B.f := by
  first | exact @GlobalTheory.InnerRead.datum_eq_Lset | exact GlobalTheory.InnerRead.datum_eq_Lset | (intros; apply GlobalTheory.InnerRead.datum_eq_Lset <;> assumption)
