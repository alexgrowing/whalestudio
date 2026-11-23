import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

def secNz {X : Scheme.{0}} {L : LB X} (s : L.Sec) : X.Opens := ⨆ i, X.basicOpen (s.f i)

def farSet {Z Y : Scheme.{0}} (β : Z ⟶ Y) {L : LB Z} (s : L.Sec) : Set Y := {v | ∀ g, β g = v → g ∈ secNz s}

def cubeTen {S : Scheme.{0}} {G T : Over S} [GrpObj G] (x a b c : T ⟶ G) : List (T ⟶ G) :=
  [x * a, x * a⁻¹, a, a⁻¹, x * b, x * c, x * (b * c)⁻¹, b, c, (b * c)⁻¹]

theorem isOpen_farSet {Z Y : Scheme.{0}} (β : Z ⟶ Y) (hβ : IsClosedMap β) {L : LB Z} (s : L.Sec) :
    IsOpen (farSet β s) := by
  have : farSet β s = (β '' (secNz s : Set Z)ᶜ)ᶜ := by
    ext v
    simp only [farSet, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_image, not_exists, not_and]
    constructor
    · intro h g hg hgv; exact hg (h g hgv)
    · intro h g hgv; by_contra hg; exact h g hg hgv
  rw [this, isOpen_compl_iff]
  exact hβ _ (secNz s).isOpen.isClosed_compl

end GlobalTheory.Mum
