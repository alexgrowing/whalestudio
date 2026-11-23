import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSec

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.VB

namespace GlobalTheory.FlagZ.TautUniq

variable {ι : Type} [Fintype ι] {N : ℕ}

def vecSec {A : Type} [CommRing A] (y : Sp A ⟶ Sp ℤ) (v : Fin N → A) :
    Γ((Scheme.Modules.pullback y).obj (Taut.stdE N), ⊤) :=
  ∑ i, (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (v i) •
    GlobalTheory.QCoh.pullbackSections y (Taut.stdE N) (by simp) (freeFrame (Sp ℤ) (Fin N) i)

theorem vecSec_col {A : Type} [CommRing A] (y : Sp A ⟶ Sp ℤ) (g : Matrix (Fin N) (Fin N) A) (j : Fin N) :
    vecSec y (fun i => g i j) = Taut.colSec y g j := rfl

variable (ι N) in

def stepMap (fl : ∀ _ : ι, Vert.Flag ((Scheme.Modules.pullback (flStr ι N)).obj (Taut.stdE N)) N) {Y : Scheme.{0}}
    (φ : Y ⟶ Fl ι N) (y : Y ⟶ Sp ℤ) (hy : φ ≫ flStr ι N = y) (a : ι) (l : Fin (N + 1)) :
    (Scheme.Modules.pullback φ).obj ((fl a).F l) ⟶ (Scheme.Modules.pullback y).obj (Taut.stdE N) :=
  (Scheme.Modules.pullback φ).map ((fl a).ι l) ≫
    (Scheme.Modules.pullbackComp φ (flStr ι N)).hom.app (Taut.stdE N) ≫
      (Scheme.Modules.pullbackCongr hy).hom.app (Taut.stdE N)

end GlobalTheory.FlagZ.TautUniq
