import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkStepMono
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchubertCellOpenImmersion

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

namespace GlobalTheory.FlagZ.Univ

variable (ι : Type) [Fintype ι] (N : ℕ)

instance isOpenImmersion_cellFl (w : ι → Equiv.Perm (Fin N)) :
    IsOpenImmersion (cell (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w) :=
  GlobalTheory.isOpenImmersion_cell ι (ι × Fin (N + 1)) N Prod.fst Prod.snd w

def cellOpen (w : ι → Equiv.Perm (Fin N)) : (Fl ι N).Opens := cell Prod.fst Prod.snd w ''ᵁ ⊤

def cellRing (w : ι → Equiv.Perm (Fin N)) :
    CellRing (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd →+* Γ(Fl ι N, cellOpen ι N w) :=
  ((Scheme.ΓSpecIso (CommRingCat.of _)).inv ≫ ((cell Prod.fst Prod.snd w).appIso ⊤).inv).hom

def cellCol (w : ι → Equiv.Perm (Fin N)) (τ : ι) (j : Fin N) :
    Γ(freeModule (Fl ι N) (Fin N), cellOpen ι N w) :=
  ∑ i, cellRing ι N w ((cellGL Prod.fst Prod.snd w τ).1 i j) •
    resM _ le_top (VB.freeFrame (Fl ι N) (Fin N) i)

theorem mem_cellOpen {w : ι → Equiv.Perm (Fin N)} {y : Fl ι N} :
    y ∈ cellOpen ι N w ↔ y ∈ Set.range (cell Prod.fst Prod.snd w) := by
  simp [cellOpen]

end GlobalTheory.FlagZ.Univ
