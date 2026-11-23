import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TiltSc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EmbeddingColumnLatticeIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSpanSingletonMulIdealCompletionIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowShape.ColsJB

variable {D : D7} {A B : HSp D} {c : ℕ}

theorem coreMat_iB' {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) :
    coreMat d h * (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)).iB = midCol d h := by
  refine (Matrix.submatrix_mul_equiv _ _ _ _ _).trans ?_
  show Matrix.fromCols (frameMat B A d.ι) (midCol d h) *
      Matrix.fromRows (0 : Matrix (Fin A.rank) (Fin 1) D.host.E) (1 : Matrix (Fin 1) (Fin 1) D.host.E) = _
  rw [Matrix.fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, zero_add]

theorem coreMat_vecB {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) (x : D.host.E) :
    coreMat d h *ᵥ vecB (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)) (fun _ => x) =
      fun k => x * d.a k ⟨σ, by omega⟩ := by
  show coreMat d h *ᵥ (_ *ᵥ _) = _
  rw [Matrix.mulVec_mulVec, coreMat_iB']
  funext k
  show ∑ j : Fin 1, midCol d h k j * x = _
  simp [midCol, mul_comm]

end GlobalTheory.RowShape.ColsJB

theorem GlobalTheory.RowShape.cols_jacBes_rowN : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ i σ (hi : i + 2 * (σ + 1) + 1 = D.R.m) v, GlobalTheory.FinPl.ColsAt (rowJac ch.G i (by omega) (σ + 1) (by omega))
    (xLast (besDecAt ch.G (i + 1) σ (by omega)) (vecB (GlobalTheory.OrthSumExists.orthDecHsum D (ch.G.V (.top (i + 1))) (GlobalTheory.SeeSaw.Model.nLine D)) fun _ => D.host.xi0 ^ σ))
    (GlobalTheory.RowShape.rowN ch.G i) (GlobalTheory.RowShape.rowN ch.G (i + 1)) v := by
  refine ⟨0, fun _ _ _ => ⟨0, fun D _ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _ => ?_⟩⟩
  intro i σ hi v a s hs
  have hodd : Odd i := by
    obtain ⟨k, hk⟩ := D.R.m_even
    exact ⟨k - σ - 2, by omega⟩
  unfold GlobalTheory.RowShape.rowN
  rw [dif_pos (by omega), dif_pos (by omega)]
  have hrat : ∀ {m n : ℕ} (N : Matrix (Fin m) (Fin n) D.host.E) (z : Fin n → D.host.E),
      GlobalTheory.MixModel.rat N *ᵥ ratV z = ratV (N *ᵥ z) := by
    intro m n N z
    funext k
    simp [GlobalTheory.MixModel.rat, ratV, Matrix.mulVec, dotProduct, map_sum, map_mul]
  have hL : colMul (rowJac ch.G i (by omega) (σ + 1) (by omega)).jX a s =
      fun k => s * incA D ((ch.G.rowDec i (by omega)).a k ⟨a.1, by omega⟩) := by
    funext k
    rfl
  have hR : colMul (xLast (besDecAt ch.G (i + 1) σ (by omega))
      (vecB (GlobalTheory.OrthSumExists.orthDecHsum D (ch.G.V (.top (i + 1))) (GlobalTheory.SeeSaw.Model.nLine D)) fun _ => D.host.xi0 ^ σ)) a s =
      fun k => (s * incA D (D.host.xi0 ^ a.1)) * incA D ((ch.G.rowDec (i + 1) (by omega)).a k ⟨a.1, by omega⟩) := by
    funext k
    induction a using Fin.lastCases with
    | last =>
      have e1 := GlobalTheory.RowShape.ColsJB.coreMat_vecB (ch.G.rowDec (i + 1) (by omega)) (σ := σ) (by omega) (D.host.xi0 ^ σ)
      simp only [colMul, xLast, Matrix.of_apply, Fin.snoc_last, HypDec.j0, hrat, Fin.val_last]
      show s * ratV ((coreMat (ch.G.rowDec (i + 1) (by omega)) (σ := σ) (by omega)) *ᵥ _) k = _
      rw [e1]
      simp only [ratV, map_mul]
      ring
    | cast b =>
      simp only [colMul, xLast, Matrix.of_apply, Fin.snoc_castSucc, HypDec.jX, GlobalTheory.MixModel.rat, Matrix.map_apply]
      show s * incA D ((Matrix.submatrix (ch.G.rowDec (i + 1) (by omega)).a id (Fin.castLE (by omega)) *
        diagonal (lam (D := D) σ) : Matrix (Fin _) (Fin σ) D.host.E) k b) = _
      rw [Matrix.mul_diagonal, map_mul]
      simp only [lam, Matrix.submatrix_apply, id, Fin.coe_castSucc]
      rw [mul_comm (incA D _) (incA D _), ← mul_assoc]
      rfl
  rw [hL, hR, (GlobalTheory.AscFin.UnitaryEmbeddingLine.embedding_line_mem_lattice_iff _ (neg_ne_zero.2 one_ne_zero) _ _ _ v s).1,
    (GlobalTheory.AscFin.UnitaryEmbeddingLine.embedding_line_mem_lattice_iff _ (neg_ne_zero.2 one_ne_zero) _ _ _ v _).2]
  have hx : D.host.xi0 ^ a.1 ≠ 0 := pow_ne_zero _ (GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D)
  have h1 : GlobalTheory.RowShape.rowId D i ⟨a.1, by omega⟩ = FractionalIdeal.spanSingleton _ ((D.host.xi0 ^ a.1)⁻¹) *
      stairId D.host.AA D.host.AAbar (D.R.m - 1 - i) ⟨a.1, by omega⟩ := by
    unfold GlobalTheory.RowShape.rowId GlobalTheory.RowShape.tiltSc
    rw [if_pos hodd, if_pos (by simp only; omega)]
  have h2 : D.host.AA * GlobalTheory.RowShape.rowId D (i + 1) ⟨a.1, by omega⟩ =
      stairId D.host.AA D.host.AAbar (D.R.m - 1 - i) ⟨a.1, by omega⟩ := by
    unfold GlobalTheory.RowShape.rowId GlobalTheory.RowShape.tiltSc
    rw [if_neg (by rw [Nat.not_odd_iff_even]; exact hodd.add_one), FractionalIdeal.spanSingleton_one, one_mul]
    unfold stairId
    rw [show D.R.m - 1 - i - a.1 = (D.R.m - 1 - (i + 1) - a.1) + 1 by omega, pow_succ]
    ring
  rw [h1, h2, idV_spanSingleton_mul_iff D v _ _ (inv_ne_zero hx) s, inv_inv, mul_comm, and_iff_left hs]
