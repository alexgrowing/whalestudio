import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.CapOComp

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace CrystallineSemistableComparison.Pb

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]

def cupPowC (A : C ⥤ CommAlgCat.{0} R) (z : CH.Cn (CH.modF A) 2) : ∀ k : ℕ, CH.Cn (CH.modF A) (2 * k)
  | 0 => fun s => (1 : A.obj (s.obj (Fin.last _)))
  | k + 1 => (CH.mulP A).cupC (by omega) (cupPowC A z k) z

def cupListC (A : C ⥤ CommAlgCat.{0} R) : ∀ {k : ℕ}, (Fin k → CH.Cn (CH.modF A) 1) → CH.Cn (CH.modF A) k
  | 0, _ => fun s => (1 : A.obj (s.obj (Fin.last _)))
  | k + 1, ℓ => (CH.mulP A).cupC (by omega) (cupListC A fun i => ℓ (Fin.castSucc i)) (ℓ (Fin.last k))

def resZ (A : C ⥤ CommAlgCat.{0} R) (U : ObjectProperty C) {k : ℕ} (b : CH.Cn (CH.modF A) k) :
    CH.Cn (CH.modF (U.ι ⋙ A)) k :=
  fun σ => b (σ ⋙ U.ι)

def resB (A : C ⥤ CommAlgCat.{0} R) {U V : ObjectProperty C} (h : V ≤ U) {k : ℕ} (b : CH.Cn (CH.modF (U.ι ⋙ A)) k) :
    CH.Cn (CH.modF (V.ι ⋙ A)) k :=
  fun σ => b (σ ⋙ ObjectProperty.ιOfLE h)

theorem capS_le_univ {ι : Type} [Fintype ι] (U : ι → ObjectProperty C) (i : ι) : capS U Finset.univ ≤ U i :=
  fun _ hT => hT i (Finset.mem_univ i)

theorem capS_univ_le {ι : Type} [Fintype ι] [DecidableEq ι] (U : ι → ObjectProperty C) (S : Finset ι) :
    capS U Finset.univ ≤ capS U S :=
  fun _ hT α _ => hT α (Finset.mem_univ α)

end CrystallineSemistableComparison.Pb
