import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCKer

namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

def Good {f : ℕ} (x : crystallineComparison.V f) : Prop := ∀ v, x v ≠ 0

def blk {α : Type} (a w b : α → α → ℂ) : α ⊕ α → α ⊕ α → ℂ := fun x y =>
  match x, y with
    | .inl p, .inl q => a p q
    | .inl p, .inr q => w p q
    | .inr q, .inl p => conj (w p q)
    | .inr p, .inr q => b p q

theorem blockPSD_iff {α : Type} (Y : Finset α) (a w b : α → α → ℂ) :
    KB.BlockPSD Y Y a w b ↔ TB.PSDOn (Y.disjSum Y) (blk a w b) := by
  unfold KB.BlockPSD
  constructor <;> intro h <;> convert h using 1 <;> funext x y <;>
    rcases x with p | p <;> rcases y with q | q <;> rfl

variable {H : Type} {f : ℕ}

def phi (Y : Finset H) (κ : H → H → ℂ) (K : Fin f → H × ℂ → H × ℂ → ℂ) (x x' : crystallineComparison.V f) : ℂ :=
  ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, K v (h, x v) (h', x' v)

def phiR (Y : Finset H) (κ : H → H → ℂ) (U P Q : Fin f → H × ℂ → H × ℂ → ℂ) (x x' : crystallineComparison.V f) : ℂ :=
  phi Y κ U x x' - phi Y κ P x x' - conj (phi Y κ P x' x) + phi Y κ Q x x'

def locv (v : Fin f) : (H × crystallineComparison.V f) ⊕ (H × crystallineComparison.V f) → (H × ℂ) ⊕ (H × ℂ) :=
  Sum.map (fun p => (p.1, p.2 v)) (fun p => (p.1, p.2 v))

def hd : (H × crystallineComparison.V f) ⊕ (H × crystallineComparison.V f) → H := Sum.elim (fun p => p.1) (fun p => p.1)

def gblk (κ : H → H → ℂ) (U P Q : Fin f → H × ℂ → H × ℂ → ℂ) (x y : (H × crystallineComparison.V f) ⊕ (H × crystallineComparison.V f)) : ℂ :=
  κ (hd x) (hd y) * ∏ v, blk (U v) (P v) (Q v) (locv v x) (locv v y)

end

end Formalism.FourierDecayAlt.P.PBC
