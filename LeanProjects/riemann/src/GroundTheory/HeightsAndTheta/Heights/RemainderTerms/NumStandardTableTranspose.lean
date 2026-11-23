import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.FlagIntegralRealEqMulDdConst
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.NumStandardTableEqCardMonotone
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.VandermondeEqVandermondeOf
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset FlagEq

noncomputable section

namespace DegreeValueAlt

variable (f : ℕ)

def toReal {N M : ℕ} (h : N = M) : RootRing f N →+* MvPolynomial (Fin f × Fin M) ℝ :=
  (MvPolynomial.map (algebraMap ℚ ℝ)).comp (rename (Prod.map id (Fin.cast h))).toRingHom

abbrev top (j k : ℕ) (τ : Fin f) (i : Fin j) : IndefiniteRowSideFullHecke.RestTerms.Roots f j k := X (τ, Fin.castAdd k i)

abbrev bot (j k : ℕ) (τ : Fin f) (i : Fin k) : IndefiniteRowSideFullHecke.RestTerms.Roots f j k := X (τ, Fin.natAdd j i)

def fibTB (j k : ℕ) : IndefiniteRowSideFullHecke.RestTerms.Roots f j k :=
  ∏ τ : Fin f, vandermondeOf (top f j k τ) * vandermondeOf (bot f j k τ)

def rectTranspose (a r : ℕ) :
    youngCells (fun _ : Fin a => r) ≃o youngCells (fun _ : Fin r => a) where
  toFun p := ⟨(⟨p.1.2, (YoungDiagramCombinatorics.mem_youngCells _ p.1).1 p.2⟩, (p.1.1 : ℕ)),
    (YoungDiagramCombinatorics.mem_youngCells _ _).2 p.1.1.2⟩
  invFun q := ⟨(⟨q.1.2, (YoungDiagramCombinatorics.mem_youngCells _ q.1).1 q.2⟩, (q.1.1 : ℕ)),
    (YoungDiagramCombinatorics.mem_youngCells _ _).2 q.1.1.2⟩
  left_inv p := rfl
  right_inv q := rfl
  map_rel_iff' := by
    rintro ⟨⟨i, c⟩, hp⟩ ⟨⟨i', c'⟩, hq⟩
    simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk, Prod.mk_le_mk, Fin.le_def]
    exact and_comm

end DegreeValueAlt

end

end GroundTheory.Heights₂.Heights.RestTerms
