import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.OfSteps

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

theorem BaseChangeColon.intNumL_cons (F : Type) [Field F] (K : Type) [DecidableEq K] (ι : K → Type)
    (V : Ideal (MRing ι F)) (b : K → ℤ) (l : List (K → ℤ)) :
    intNumL F V (b :: l) = intNum F V (Matrix.vecCons b l.get) := by
  unfold intNumL intNum GroundTheory.Heights₂.Heights.NumbersDVR.mixedDiff
  rw [List.ofFn_get, List.ofFn_succ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, List.ofFn_get]

theorem BaseChangeColon.intNumL_add (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (V : Ideal (MRing ι F)) (d : ℕ) (hV : IsMultiProjPrime V)
    (hd : ringKrullDim (MRing ι F ⧸ V) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞))
    (b b' : K → ℤ) (l : List (K → ℤ)) (hl : l.length + 1 = d) :
    intNumL F V ((b + b') :: l) = intNumL F V (b :: l) + intNumL F V (b' :: l) := by
  rw [BaseChangeColon.intNumL_cons, BaseChangeColon.intNumL_cons, BaseChangeColon.intNumL_cons]
  refine IntNumAddFirst.full F K ι l.length V hV.isPrime hV.multiHomog ?_ b b' l.get
  rw [hd]
  exact_mod_cast (show d + Fintype.card K < l.length + 2 + Fintype.card K by omega)
