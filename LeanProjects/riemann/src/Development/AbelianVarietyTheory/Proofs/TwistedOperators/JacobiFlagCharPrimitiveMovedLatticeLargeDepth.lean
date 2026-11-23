import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TiltSc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdVLeOfLoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PsiPrimitiveStandardFramesFourierJacobiLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MulFractionalIdealCompletionSubsetIffMemQuotient
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InverseDifferentCompletionIffCharacterDual
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped nonZeroDivisors

namespace GlobalTheory.RowShape

namespace PrimJac

theorem rowJac_line {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (n : ℕ) (hn : n < D.R.m) (σ : ℕ)
    (h : D.R.m - 1 - n = 2 * σ) (v : Pl D) (p : Fin σ) (a : AE D) :
    colMul (rowJac G n hn σ h).jX p a ∈ latV _ (rowN G n) (· = v) ↔
      a ∈ idV (rowId D n (Fin.castLE (by omega) p)) v := by
  have e1 : colMul (rowJac G n hn σ h).jX p a =
      fun k => a * incA D (1 * (G.rowDec n hn).a k (Fin.castLE (by omega) p)) := by
    funext k
    simp [colMul, HypDec.jX, rat, Matrix.map_apply, rowJac, jacDec, HermitianOrthogonalExtensionData.iso]
  have e2 : rowN G n = (G.rowDec n hn).lat (G.Λ (.top n)) (rowId D n) := by
    unfold rowN; rw [dif_pos hn]
  rw [e1, e2, GlobalTheory.StairLine.line_mem_iff _ _ _ _ (by simp only [Fin.coe_castLE]; omega) one_ne_zero v a, inv_one,
    FractionalIdeal.spanSingleton_one, one_mul]

theorem stairId_ne_zero (D : D7) (c : ℕ) (p : Fin c) : stairId D.host.AA D.host.AAbar c p ≠ 0 := by
  unfold stairId
  exact mul_ne_zero (pow_ne_zero _ (GlobalTheory.CuspCharLattice.host_AA_ne_zero _))
    (inv_ne_zero (pow_ne_zero _ (GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D)))

theorem tiltSc_first {D : D7} {n : ℕ} (hodd : Odd n) (p : Fin (D.R.m - 1 - n)) (hp : 2 * p.1 < D.R.m - 1 - n) :
    tiltSc D n p = (D.host.xi0 ^ p.1)⁻¹ := by
  unfold tiltSc; rw [if_pos hodd, if_pos hp]

theorem rowId_ratio {D : D7} {n : ℕ} (hodd : Odd n) (p q : Fin (D.R.m - 1 - n)) (hpq : q.1 = p.1 + 1)
    (hq : 2 * q.1 < D.R.m - 1 - n) : rowId D n p * (rowId D n q)⁻¹ = dI D := by
  have hx : D.host.xi0 ≠ 0 := cmHost_imaginaryGenerator_ne_zero
  unfold rowId
  rw [tiltSc_first hodd p (by omega), tiltSc_first hodd q hq,
    stairId_succ (GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D) p q hpq]
  have hS := stairId_ne_zero D (D.R.m - 1 - n) q
  revert hS
  generalize stairId D.host.AA D.host.AAbar (D.R.m - 1 - n) q = S
  intro hS
  rw [mul_inv, FractionalIdeal.spanSingleton_inv, inv_inv]
  unfold dI
  calc _ = FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (D.host.xi0 ^ p.1)⁻¹ *
        FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (D.host.xi0 ^ q.1) * D.host.AA * D.host.AAbar * (S * S⁻¹) := by ring
    _ = _ := by
      rw [mul_inv_cancel₀ hS, mul_one, FractionalIdeal.spanSingleton_mul_spanSingleton, hpq, pow_succ,
        ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hx), one_mul]

end PrimJac

open PrimJac

theorem primAt_rowJac {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (ψ : AddChar (AF D.host.F) ℂ)
    (hψ : IsStdChar D ψ (-1)) (n : ℕ) (hn : n < D.R.m) (σ : ℕ) (h : D.R.m - 1 - n = 2 * σ) (v : Pl D) :
    PrimAt ψ (rowJac G n hn σ h) (rowN G n) v := by
  have hodd : Odd n := by
    obtain ⟨k, hk⟩ := D.R.m_even
    exact ⟨k - σ - 1, by omega⟩
  intro i j hij s hs
  have key : (∀ a : AE D, colMul (rowJac G n hn σ h).jX j a ∈ latV _ (rowN G n) (· = v) →
      colMul (rowJac G n hn σ h).jX i (s * a) ∈ latV _ (rowN G n) (· = v)) ↔
      ∀ a ∈ idV (rowId D n (Fin.castLE (by omega) j)) v, s * a ∈ idV (rowId D n (Fin.castLE (by omega) i)) v :=
    ⟨fun H a ha => (rowJac_line G n hn σ h v i _).1 (H a ((rowJac_line G n hn σ h v j a).2 ha)),
      fun H a hc => (rowJac_line G n hn σ h v i _).2 (H a ((rowJac_line G n hn σ h v j a).1 hc))⟩
  have hne : ∀ p : Fin (D.R.m - 1 - n), rowId D n p ≠ 0 := fun p => mul_ne_zero
    (by
      rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
      unfold tiltSc
      split_ifs <;> simp [cmHost_imaginaryGenerator_ne_zero])
    (stairId_ne_zero D _ p)
  rw [key, GlobalTheory.IdealQuot.mul_subset_iff D v _ _ (hne _) (hne _) s hs,
    rowId_ratio hodd _ _ (by simp only [Fin.coe_castLE]; exact hij) (by simp only [Fin.coe_castLE]; have := j.2; omega)]
  exact DiffDual.idV_dI_iff D ψ hψ v s hs

theorem big_primAt_rowJac : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ n (hn : n < D.R.m) σ
    (h : D.R.m - 1 - n = 2 * σ) v, GlobalTheory.FinPl.PrimAt ch.W.ψ (rowJac ch.G n hn σ h) (GlobalTheory.RowShape.rowN ch.G n) v :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ n hn σ h v =>
    primAt_rowJac ch.G ch.W.ψ ch.W.ψ_std n hn σ h v⟩⟩

end GlobalTheory.RowShape
