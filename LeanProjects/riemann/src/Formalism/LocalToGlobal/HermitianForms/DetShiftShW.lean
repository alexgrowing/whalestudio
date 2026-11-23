import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

namespace Formalism.L2.Forms

open Formalism.BasicNotions

variable {N : ℕ}

def shW (l : DomWeight N) (c : ℤ) : DomWeight N where
  w := fun i => l.w i - c
  anti := fun i j h => by
    have := l.anti h
    show l.w j - c ≤ l.w i - c
    omega

theorem shW_zero (l : DomWeight N) : shW l 0 = l := by
  cases l
  simp only [shW, sub_zero]

theorem detShift_shW (l : DomWeight N) (c : ℤ) (hN : 0 < N) : (shW l c).detShift = l.detShift - c := by
  simp [DomWeight.detShift, hN, shW]

theorem natW_shW (l : DomWeight N) (c : ℤ) : (shW l c).natW = l.natW := by
  funext i
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) i.2
  simp only [DomWeight.natW, detShift_shW l c hN]
  congr 1
  simp only [shW]
  ring

theorem delSq_shW (R : Type) [CommRing R] (l : DomWeight N) (c : ℤ) : delSq R N (shW l c) = delSq R N l := by
  unfold delSq
  rw [natW_shW]

theorem extremal_shW (R : Type) [CommRing R] (l : DomWeight N) (c : ℤ) : extremal R N (shW l c) = extremal R N l := by
  unfold extremal
  rw [natW_shW]

theorem CSpan_shW {ι : Type} [Fintype ι] (lam : ι → DomWeight N) (c : ι → ℤ) :
    CSpan (fun τ => shW (lam τ) (c τ)) = CSpan lam := by
  simp only [CSpan, delSq_shW]

theorem nfAll_shW {ι : Type} [Fintype ι] (lam : ι → DomWeight N) (c : ι → ℤ)
    (p q : MvPolynomial (ι × Fin N × Fin N) ℂ) : nfAll (fun τ => shW (lam τ) (c τ)) p q = nfAll lam p q := by
  simp only [nfAll, extremal_shW]

end Formalism.L2.Forms
