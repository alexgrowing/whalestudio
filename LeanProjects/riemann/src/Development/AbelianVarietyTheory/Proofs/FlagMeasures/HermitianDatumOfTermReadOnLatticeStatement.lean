import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDatumOfTermReadOnLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianDatum_of_term_read_on_lattice : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (k : ℕ) (P : FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (theta M) → (∀ (d : Datum P) (t : Term V M r), IsTermOver P d t → H.IsTerm t ∧ (d.L : Set (H.Wb P.A.f)) = H.Lset t.abelian₂ P.A.f ∧ (d.L' : Set (H.Wb P.B.f)) = H.Lset t.abelian₂ P.B.f) ∧ ∀ (d d' : Datum P) (t t' : Term V M r), IsTermOver P d t → IsTermOver P d' t' → H.Lset t.abelian₂ P.A.f = H.Lset t'.abelian₂ P.A.f → H.Lset t.abelian₂ P.B.f = H.Lset t'.abelian₂ P.B.f → (∀ g, M.split = some g → H.iotaGraph g ⟨t.abelian₂, P.A.f, P.B.f, t.T, t.T'⟩ = H.iotaGraph g ⟨t'.abelian₂, P.A.f, P.B.f, t'.T, t'.T'⟩) → d = d' := by
  first | exact @GlobalTheory.LocOver.TermLat.datum_of_lattice | exact GlobalTheory.LocOver.TermLat.datum_of_lattice | (intros; apply GlobalTheory.LocOver.TermLat.datum_of_lattice <;> assumption)
