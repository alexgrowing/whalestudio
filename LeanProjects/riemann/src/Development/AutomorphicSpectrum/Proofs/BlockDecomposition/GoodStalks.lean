import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsPresents
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel GlobalTheory.QCoh
open IsLocalRing

namespace GlobalTheory.CompanionTheory.KoszulCount

def germSec {X : Scheme.{0}} {L : LB X} (s : L.Sec) {i : L.ι} {x : X} (hx : x ∈ L.U i) :
    X.presheaf.stalk x :=
  X.presheaf.germ (L.U i) x hx (s.f i)

def CotIndep {X : Scheme.{0}} {L : LB X} {d : ℕ} (t : Fin d → L.Sec) : Prop :=
  ∀ (x : X) (i : L.ι) (hx : x ∈ L.U i),
    LinearIndependent (ResidueField (X.presheaf.stalk x))
      (fun j : {j : Fin d // germSec (t j) hx ∈ maximalIdeal (X.presheaf.stalk x)} =>
        ((maximalIdeal (X.presheaf.stalk x)).toCotangent ⟨_, j.2⟩ :
          CotangentSpace (X.presheaf.stalk x)))

def GoodStalks {X : Scheme.{0}} {L : LB X} (F : X.Modules) {d : ℕ} (t : Fin d → L.Sec) : Prop :=
  ∀ (x : X) (i : L.ι) (hx : x ∈ L.U i),
    RingTheory.Sequence.IsWeaklyRegular (F.presheaf.stalk x :)
        (List.ofFn fun j => germSec (t j) hx) ∧
      Module.length (X.presheaf.stalk x)
        ((F.presheaf.stalk x :) ⧸ (Ideal.span (Set.range fun j => germSec (t j) hx) •
          (⊤ : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x :)))) ≤ 1

end GlobalTheory.CompanionTheory.KoszulCount
