import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix
open scoped ComplexOrder

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in

theorem LenSq.re_nonneg {P : Matrix ι ι ℂ} (hP : P.PosDef) (y : ι → ℂ) :
    0 ≤ (star y ⬝ᵥ (P *ᵥ y)).re :=
  (Complex.nonneg_iff.mp (hP.posSemidef.dotProduct_mulVec_nonneg y)).1

omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E] in

theorem LenSq.proof (h : HermitianForm F E W) (v : Basis ι E W) : LenSq.Statement h v := by
  intro M y
  have hw : ∀ w, 0 ≤ (star (y w) ⬝ᵥ (M.P w *ᵥ y w)).re := fun w =>
    LenSq.re_nonneg (M.posDef w) (y w)
  refine ⟨hw, ?_⟩
  unfold Majorant.len
  exact Real.sq_sqrt (Finset.sum_nonneg fun w _ => hw w)

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
