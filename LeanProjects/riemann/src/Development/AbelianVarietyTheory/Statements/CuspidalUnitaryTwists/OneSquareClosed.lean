import Development.AbelianVarietyTheory.Definitions.Foundations.TupleConstantsNeZero
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.OneSquareLeaf.LeafOneSquareFree

open NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw conjPl)
open Formalism.PairingDivisionLocalBalance (Pl wt)
open Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts

noncomputable section

namespace GlobalTheory.Square

def RatioIn : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ₀ : K →+* ℂ) (S : Sq K) (hd y : ℕ), S.OK hd y →
  ∀ (w : Pl K) (cw : ℂ) (zA zA' : K) (zT zTd : ℤ → K) (gT : ℤ → ℤ) (n0 : ℤ → ℝ) (er dl : ℝ) (T : Type) (S0 : Finset T)
    (cc qq : T → ℕ), (∀ v ∈ S0, 0 < qq v) → S.Twisted σ₀ w cw zA zA' zT zTd gT n0 er dl S0 cc qq →
    ∃ r : K, r ≠ 0 ∧ σ₀ r * S.base.c = cw

def OneSquareClosed : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ₀ : K →+* ℂ) (m : ℕ) (T : Type)
    (r0 : Fin m × Fin m → K) (rw : Pl K → Fin m × Fin m → K) (Se Sd : Finset ℕ) (dd hd yy : Fin m × Fin m → ℕ)
    (N : ℕ) (S0 : Finset T) (cc qq ee : T → ℕ) (zA zA' : Fin m × Fin m → K) (zT : Fin m × Fin m → ℤ → K)
    (zTd : Fin m × Fin m → Bool → ℤ → K) (gT : Fin m × Fin m → ℤ → Pl K → ℤ) (ch : Pl K → Bool)
    (N0 : Fin m × Fin m → ℤ → ℕ → ℝ) (dl : Pl K → ℝ)
    (S : Fin m × Fin m → Sq K) (cw : Pl K → Fin m × Fin m → ℂ),
    (∀ l ∈ Se, l.Prime) → (∀ ij, dd ij = 2 * hd ij) → (∀ ij, dd ij ≤ 2 * N) → (∀ ij, yy ij + 1 ≤ m) →
    (∀ q ∈ S0, cc q ≤ ee q) → (∀ q ∈ S0, 0 < qq q) → (∀ w, 0 ≤ dl w) →
    (∀ ij (s : ℤ), 1 ≤ s → s ≤ hd ij → ∀ l ∈ Sd, 0 ≤ N0 ij s l) →
    (∀ ij, (S ij).OK (hd ij) (yy ij)) →
    (∀ ij, σ₀ (r0 ij) * (S ij).base.c = (S ij).base.c) →
    (∀ w ij, σ₀ (rw w ij) * (S ij).base.c = cw w ij) →
    (∀ w ij, cw w ij = (S ij).base.c ∨
      (S ij).Twisted σ₀ w (cw w ij) (zA ij) (zA' ij) (zT ij) (zTd ij (ch w)) (fun s => gT ij s w)
        (fun s => wt Sd (N0 ij s) w) (wt Se (fun l => 1 / (l : ℝ) ^ 2) w) (dl w) S0 cc qq) →
    SquareCoefficientsCondition r0 rw Se Sd dd hd yy N S0 cc qq ee zA zA' zT zTd gT ch N0 dl

end GlobalTheory.Square
