import Formalism.LocalToGlobal.Divisibility.JetBounds.PlaceInputAllEntries
import Formalism.LocalToGlobal.ExponentGrids.IntegerShiftClosedExponent

open Module NumberField IsDedekindDomain
open scoped BigOperators

noncomputable section

namespace Formalism.L2.AlgTh

open Formalism.DivisionValues (vw PlOver)
open Formalism.L2.Indef (DefBase DefSide DefCols)
open Formalism.L2.DIV (PathData EmbAt IsExpansion ColsInt RowsInt LastInt UnitsInt StabDvd)
open Formalism.AtG (PerBd colRhs)

def GAt {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs} (Dc : DefCols Df) (u : Dc.Mem)
    (t : Bs.Tup) (Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K)) (w : HeightOneSpectrum (𝓞 K)) (g : ℕ) [Fact g.Prime] (pb : K)
    (Dg : Bs.J → ℕ) (Rg : Bs.J → ℝ) : Prop :=
  ∃ (ι : K →+* ℂ_[g]) (X : PathData K g Bs.J (Fin (Dc.a u) → K) (Fin (Df.nV t) → K)) (D : ℕ) (j1 : Bs.J),
    EmbAt w g ι ∧ IsExpansion X ι (Dc.Pt u t) (Nu : Set (Fin (Dc.a u) → K)) (Df.Mt t : Set (Fin (Df.nV t) → K)) ∧
    ColsInt X w (Nu : Set (Fin (Dc.a u) → K)) ∧ RowsInt X w (Df.Mt t : Set (Fin (Df.nV t) → K)) ∧
    LastInt X ∧ UnitsInt X ∧ StabDvd X D j1 ∧ ¬ g ∣ D ∧
    ∀ π j, ‖X.e π j‖ * ‖ι pb‖ ^ (Dg j) * ‖(g : ℂ_[g])‖ ^ (Rg j) ≤ 1

def ColBoundOfPaths : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Bs : DefBase K) (Df : DefSide Bs) (Dc : DefCols Df) (u : Dc.Mem)
    (t : Bs.Tup) (Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K)) (w : HeightOneSpectrum (𝓞 K)) (g : ℕ) [Fact g.Prime] (pb : K)
    (Dg : Bs.J → ℕ) (Rg : Bs.J → ℝ), PlOver g w → pb ≠ 0 → GAt Dc u t Nu w g pb Dg Rg →
    PerBd Dc u Nu t w (-(∑ j, (Dg j : ℝ) * (vw w pb : ℝ)) - (∑ j, Rg j) * (vw w (g : K) : ℝ)) ∧
    ∀ (Jx : Type) (sx : Finset Jx) (nn : Jx → K) (cg : K) (E0 : ℝ),
      colRhs sx g nn cg E0 w ≤ -(∑ j, (Dg j : ℝ) * (vw w pb : ℝ)) - (∑ j, Rg j) * (vw w (g : K) : ℝ) →
      PerBd Dc u Nu t w (colRhs sx g nn cg E0 w)

def ColRhsLe : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (g : ℕ), PlOver g w →
  ∀ (J : Type) [Fintype J] (pb cg : K) (Dg : J → ℕ) (Rg : J → ℝ) (E0 : ℝ), pb ≠ 0 → (∃ k : ℕ, 0 < k ∧ cg ^ k = 1) →
    ∑ j, Rg j ≤ E0 →
    colRhs Finset.univ g (fun j => pb ^ Dg j) cg E0 w ≤
      -(∑ j, (Dg j : ℝ) * (vw w pb : ℝ)) - (∑ j, Rg j) * (vw w (g : K) : ℝ)

end Formalism.L2.AlgTh
