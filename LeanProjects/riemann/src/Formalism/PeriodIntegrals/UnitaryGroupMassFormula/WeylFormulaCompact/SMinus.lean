import Formalism.PeriodIntegrals.WeylForU

noncomputable section

namespace PI.WeylForKWork

open PI PI.UpqRep Matrix

variable {N : ℕ}

def sPlus (ε : Fin N → Bool) : Finset (Fin N) := Finset.univ.filter (fun a => ε a = true)

def sMinus (ε : Fin N → Bool) : Finset (Fin N) := Finset.univ.filter (fun a => ε a = false)

def blk (ε : Fin N → Bool) : Fin (nPl ε) ⊕ Fin (nMi ε) ≃ Fin N :=
  (Equiv.sumCongr
    (((sPlus ε).orderIsoOfFin rfl).toEquiv.trans (Equiv.subtypeEquivRight (fun a => by simp [sPlus])))
    (((sMinus ε).orderIsoOfFin rfl).toEquiv.trans
      (Equiv.subtypeEquivRight (p := fun a => a ∈ sMinus ε) (q := fun a => ¬ (ε a = true))
        (fun a => by simp [sMinus])))).trans
  (Equiv.sumCompl (fun a => ε a = true))

def ePl (ε : Fin N → Bool) (i : Fin (nPl ε)) : Fin N := blk ε (Sum.inl i)

def eMi (ε : Fin N → Bool) (j : Fin (nMi ε)) : Fin N := blk ε (Sum.inr j)

def iPl (ε : Fin N → Bool) (h : Matrix (Fin (nPl ε)) (Fin (nPl ε)) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  (Matrix.fromBlocks h 0 0 1).submatrix (blk ε).symm (blk ε).symm

def iMi (ε : Fin N → Bool) (h : Matrix (Fin (nMi ε)) (Fin (nMi ε)) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  (Matrix.fromBlocks 1 0 0 h).submatrix (blk ε).symm (blk ε).symm

def sPl {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin N → Bool)
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) : Matrix (Fin (nPl ε)) (Fin (nPl ε)) ℂ → (H →L[ℂ] H) :=
  fun h => σ (iPl ε h)

def sMi {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin N → Bool)
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) : Matrix (Fin (nMi ε)) (Fin (nMi ε)) ℂ → (H →L[ℂ] H) :=
  fun h => σ (iMi ε h)

def wu (n : ℕ) (μ : Fin n → ℝ) : ℝ :=
  (∏ a : Fin n, ∏ b ∈ Finset.univ.filter (fun b => a < b), (μ a - μ b + ((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) /
    ∏ i ∈ Finset.range n, (i.factorial : ℝ)

end PI.WeylForKWork
