import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver secOver secMOver)

def OneBlockPrime.Statement : Prop :=
  ∀ (F : Type) [Field F] (κ : Type) [Fintype κ] (Ω : Type) [Field Ω] [Algebra F Ω] (x' : κ → Ω),
    (∃ i, x' i ≠ 0) → NumbersDVR.IsMultiProjPrime (mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x'))

def OneBlockHilbFn.Statement : Prop :=
  ∀ (F : Type) [Field F] (κ : Type) [Fintype κ] (Ω : Type) [Field Ω] [Algebra F Ω] (x' : κ → Ω) (n : ℕ),
    NumbersDVR.hilbFn (mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x')) (fun _ => (n : ℤ)) =
      (Module.finrank F (secMOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') (fun _ => n)) : ℤ)

def ReindexDim.Statement : Prop :=
  ∀ (F : Type) [Field F] (κ : Type) [Fintype κ] (Ω : Type) [Field Ω] [Algebra F Ω] (x' : κ → Ω) (N : ℕ)
    (e : κ ≃ Fin (N + 1)),
    ringKrullDim (NumbersDVR.MRing (fun _ : Unit => κ) F ⧸ mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x')) =
      ringKrullDim (Kleiman.Poly F N ⧸ Kleiman.primeOf (S := F) (x' ∘ e.symm))

def ReindexPiece.Statement : Prop :=
  ∀ (F : Type) [Field F] (κ : Type) [Fintype κ] (Ω : Type) [Field Ω] [Algebra F Ω] (x' : κ → Ω) (N : ℕ)
    (e : κ ≃ Fin (N + 1)) (n : ℕ),
    secMOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') (fun _ => n) = (Kleiman.coordGraded F (x' ∘ e.symm)).piece (n : ℤ)

def ReindexSecs.Statement : Prop :=
  ∀ (F : Type) [Field F] (κ : Type) [Fintype κ] (Ω : Type) [Field Ω] [Algebra F Ω] (x' : κ → Ω) (N : ℕ)
    (e : κ ≃ Fin (N + 1)) (n : ℤ),
    secOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') (fun _ => n) = (Kleiman.twistSys F (x' ∘ e.symm) n).secs

section Inhabitants

open IndefiniteRowSideFullHecke.Kleiman2

variable (F : Type) [Field F]

end Inhabitants

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
