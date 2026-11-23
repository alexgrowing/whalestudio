import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralOfKeepsSelfDualLatticeLineColon
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsTameFinitePlaceHermitianAll
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvDiagTorusIntegralBesselJacobiUnramified

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.ShiftInt

variable {D : D7}

theorem mul_mem_intAt {v : GlobalTheory.FinPl.Pl D} {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a * b ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_right _ _ ha.1, by rw [map_mul]; exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE ha.2 hb.2⟩

theorem upSum_single {ρ : ℕ} {i j : Fin ρ} (hj : j.1 = i.1 + 1) (c : AE D) :
    upSum (Matrix.single i j c : Mx D ρ ρ) = c := by
  unfold upSum
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · rw [if_pos hj, Matrix.single_apply, if_pos ⟨rfl, rfl⟩]
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (Fin.ext (by omega))
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro b _ hb
    refine Finset.sum_eq_zero fun k _ => ?_
    split_ifs with h
    · rw [Matrix.single_apply, if_neg]
      rintro ⟨rfl, -⟩
      exact hb rfl
    · rfl
  · intro h; exact absurd (Finset.mem_univ _) h

theorem mxAt_single {P : GlobalTheory.FinPl.Pl D → Prop} {ρ : ℕ} (i j : Fin ρ) {c : AE D} (hc : c ∈ idAt D P) :
    MxAt P (Matrix.single i j c : Mx D ρ ρ) := by
  intro a b
  rw [Matrix.single_apply]
  split_ifs
  · exact hc
  · exact zero_mem _

theorem mul_single_mulVec {m ρ : ℕ} (x : Mx D m ρ) (i j : Fin ρ) (c : AE D) (z : Fin ρ → AE D) :
    (x ⬝ (Matrix.single i j c : Mx D ρ ρ)) *ᵥ z = GlobalTheory.FinPl.colMul x i (c * z j) := by
  funext k
  rw [← Matrix.mulVec_mulVec, Matrix.single_mulVec, Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
  · simp [GlobalTheory.FinPl.colMul, mul_comm]
  · intro b _ hb
    simp [Function.update_of_ne hb]
  · intro h; exact absurd (Finset.mem_univ _) h

set_option maxHeartbeats 1000000 in

theorem shift_int : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ) (p : Pieces V₀ W W₀ ρ ρ) (LV : Lat V) (LV₀ : Lat V₀) (LW : Lat W) (LW₀ : Lat W₀) (v : GlobalTheory.FinPl.Pl D), GoodAt dV dW (xZero dW) ψ LV LV₀ LW LW₀ v → StdAt dV dW p LV LW v → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → dW.levi t ∈ grpAt W (· = v) → (∀ N : Mx D ρ ρ, MxAt (· = v) N → (∀ i j, j ≤ i → N i j = 0) → mt W (dW.levi t)⁻¹ ⬝ (xZero dW ⬝ N) ∈ p.A₁ → psiE ψ (upSum N) = 1) → ∀ i j : Fin ρ, j.1 = i.1 + 1 → t.1 i i - 1 ∈ intAt D (· = v) := by
  intro D ψ _ V V₀ W W₀ ρ dV dW p LV LV₀ LW LW₀ v hG hS t htd ht hsh i j hj
  have hlt : i < j := by rw [Fin.lt_def]; omega
  obtain ⟨h1, -, -⟩ := GlobalTheory.FinPl.InvStep.diag_inv t htd
  have hti : t.1 i i - 1 ∈ idAt D (· = v) := by
    have := GlobalTheory.FinPl.InvStep.levi_sub_one_mem dW ht i i
    rwa [one_apply_eq] at this
  refine GlobalTheory.ColonInt.colon_int D V V₀ ρ dV LV LV₀ v (GlobalTheory.FinPl.TamePlaces.tame D v) hG.sdV hG.monoV i j _ hti ?_
  intro r hr hR
  have hP := hG.prim i j hj
  refine (hP (r * t.1 i i) (Ideal.mul_mem_right _ _ hr)).2 ?_
  intro o ho
  have hψr := (hP r hr).1 hR
  have hro : r * o ∈ idAt D (· = v) := Ideal.mul_mem_right _ _ hr
  have hRo : ∀ a : AE D, GlobalTheory.FinPl.colMul dV.jX j a ∈ latV V LV (· = v) →
      GlobalTheory.FinPl.colMul dV.jX i (r * o * a) ∈ latV V LV (· = v) :=
    (hP (r * o) hro).2 fun o' ho' => by rw [mul_assoc]; exact hψr _ (mul_mem_intAt ho ho')
  have hN : (Matrix.single i j (r * t.1 i i * o) : Mx D ρ ρ) = t.1 ⬝ (Matrix.single i j (r * o) : Mx D ρ ρ) := by
    conv_rhs => rw [h1]
    ext a b
    rw [diagonal_mul, Matrix.single_apply, Matrix.single_apply]
    split_ifs with h
    · rw [← h.1]; ring
    · rw [mul_zero]
  have hmove : mt W (dW.levi t)⁻¹ ⬝ (xZero dW ⬝ (Matrix.single i j (r * t.1 i i * o) : Mx D ρ ρ)) =
      xZero dW ⬝ (Matrix.single i j (r * o) : Mx D ρ ρ) := by
    rw [hN, xZero, ← map_inv, ← Matrix.mul_assoc, HypDec.levi_jX, Matrix.mul_assoc, ← Matrix.mul_assoc (t⁻¹).1,
      show (t⁻¹).1 ⬝ t.1 = 1 from t.inv_mul, Matrix.one_mul]
  have hx : MxAt (· = v) (xZero dW ⬝ (Matrix.single i j (r * o) : Mx D ρ ρ)) := by
    intro a b
    have := GlobalTheory.FinPl.InvStep.mat_mem_idAt (xZero dW) _ 1 (mxAt_single i j hro) a b
    rwa [Matrix.mul_one] at this
  have hA : xZero dW ⬝ (Matrix.single i j (r * o) : Mx D ρ ρ) ∈ p.A₁ := by
    refine (hS.a _ hx).2 ((GlobalTheory.FinPl.LatMem.mem_latO_iff D V W LV LW hG.sdV hG.sdW _ _).2 ⟨?_, fun y hy => ?_⟩)
    · rw [HypDec.extX_apply]
      exact fun a b => GlobalTheory.FinPl.InvStep.mat_mem_idAt (xZero dW) _ dV.pX (mxAt_single i j hro) a b
    · have h2 := (hG.cols i _ (Ideal.mul_mem_right _ _ hro)).1 (hRo _ (((hG.monoV y).1 hy).1 j))
      rw [← mul_single_mulVec, Matrix.mulVec_mulVec] at h2
      rw [HypDec.extX_apply]
      exact h2
  have h3 := hsh (Matrix.single i j (r * t.1 i i * o))
    (mxAt_single i j (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hr)))
    (fun a b hab => by
      rw [Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      exact absurd hlt (not_lt.2 hab))
    (by rw [hmove]; exact hA)
  rwa [upSum_single hj] at h3

end GlobalTheory.AscFin.ShiftInt

end
