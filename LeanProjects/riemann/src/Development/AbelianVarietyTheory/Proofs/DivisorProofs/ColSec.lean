import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.VB

namespace GlobalTheory.FlagZ.Taut

variable (ι : Type) [Fintype ι] (N : ℕ)

abbrev stdE : (Sp ℤ).Modules := (HermVB.std (𝟙 (Sp ℤ)) N).E

variable {N} in

def colSec {A : Type} [CommRing A] (x : Sp A ⟶ Sp ℤ) (g : Matrix (Fin N) (Fin N) A) (j : Fin N) :
    Γ((Scheme.Modules.pullback x).obj (stdE N), ⊤) :=
  ∑ i, (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (g i j) •
    GlobalTheory.QCoh.pullbackSections x (stdE N) (by simp) (freeFrame (Sp ℤ) (Fin N) i)

def IsTaut (fl : ∀ _ : ι, Vert.Flag ((Scheme.Modules.pullback (flStr ι N)).obj (stdE N)) N) : Prop :=
  ∀ (A : Type) [CommRing A] (g : ι → GL (Fin N) A) (a : ι) (l : Fin (N + 1)),
    ∃ s : Fin l → Γ((Scheme.Modules.pullback (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g)).obj ((fl a).F l), ⊤),
      IsFrame s ∧ ∀ j, ((Scheme.Modules.pullback (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g)).map ((fl a).ι l) ≫
        (Scheme.Modules.pullbackComp (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g) (flStr ι N)).hom.app
          (stdE N)).app ⊤ (s j) =
        colSec (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g ≫ flStr ι N) (g a).1 (Fin.castLE l.is_le j)

end GlobalTheory.FlagZ.Taut
