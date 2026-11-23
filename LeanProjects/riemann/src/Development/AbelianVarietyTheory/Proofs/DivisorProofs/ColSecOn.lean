import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSec

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.VB

namespace GlobalTheory.FlagZ.Loc

variable {N : ℕ} {T : Scheme.{0}}

def colSecOn (g : T ⟶ Sp ℤ) (V : T.Opens) (G : Matrix (Fin N) (Fin N) Γ(T, V)) (j : Fin N) :
    Γ((Scheme.Modules.pullback g).obj (Taut.stdE N), V) :=
  ∑ i, G i j • GlobalTheory.QCoh.pullbackSections g (Taut.stdE N) (by simp) (freeFrame (Sp ℤ) (Fin N) i)

def Adapted {ι : Type} (g : T ⟶ Sp ℤ)
    (fl' : ∀ _ : ι, Vert.Flag ((Scheme.Modules.pullback g).obj (Taut.stdE N)) N) (V : T.Opens)
    (G : ι → GL (Fin N) Γ(T, V)) : Prop :=
  ∀ (a : ι) (l : Fin (N + 1)), ∃ s : Fin l → Γ((fl' a).F l, V), IsFrame s ∧
    ∀ j, ((fl' a).ι l).app V (s j) = colSecOn g V (G a).1 (Fin.castLE l.is_le j)

end GlobalTheory.FlagZ.Loc
