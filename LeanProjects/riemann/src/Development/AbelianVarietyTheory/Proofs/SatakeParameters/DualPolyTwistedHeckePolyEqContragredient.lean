import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitDetOfSplitDetermines
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Hk3.DualHecke

theorem comp_C_mul_X_dualPoly {K : Type} [Field K] (t u : K) (R : K[X]) :
    (Formalism.L2.DIV.dualPoly t R).comp (C u * X) = Formalism.L2.DIV.dualPoly (t * u) R := by
  unfold Formalism.L2.DIV.dualPoly
  rw [mul_comp, C_comp, comp_assoc, mul_comp, C_comp, X_comp, C_mul]
  congr 2
  ring

theorem dualPoly_heckePolyOf_comp : ∀ (K : Type) [Field K] (n q : ℕ) (a b : ℕ → K) (s s' : K), (q : K) ≠ 0 → s ≠ 0 → 0 < n → a 0 = 1 → (∀ j, j ≤ n → b j * a n = a (n - j)) → dualPoly (s * s' * (q : K) ^ (n - 1)) ((Formalism.L2.Col.heckePolyOf n q b).comp (C s * X)) = (Formalism.L2.Col.heckePolyOf n q a).comp (C s' * X) := by
  intro K _ n q a b s s' hq hs hn h0 h
  have han : a n ≠ 0 := by
    intro h1
    have e := h n le_rfl
    rw [Nat.sub_self, h0, h1, mul_zero] at e
    exact zero_ne_one e
  have hbn : b n * a n = 1 := by
    have e := h n le_rfl
    rwa [Nat.sub_self, h0] at e
  have hb0 : b 0 = 1 := by
    have e := h 0 (Nat.zero_le _)
    rw [Nat.sub_zero] at e
    exact mul_right_cancel₀ han (by rw [e, one_mul])
  have hdual : ∀ k ≤ n, b n * a k = b (n - k) := by
    intro k hk
    have e := h (n - k) (Nat.sub_le _ _)
    rw [Nat.sub_sub_self hk] at e
    rw [← e]
    linear_combination b (n - k) * hbn
  have H := GlobalTheory.PartsCompare.heckePolyOf_dual (n := n) (q := q) hq (a := b) (b := a) hb0 hdual
  have hc := GlobalTheory.PartsCompare.dualPoly_comp (inv_ne_zero hs) (s * s' * (q : K) ^ (n - 1))
    (Formalism.L2.Col.heckePolyOf n q b)
  rw [inv_inv] at hc
  rw [hc, H, comp_C_mul_X_dualPoly]
  congr 1
  field_simp

end GlobalTheory.Hk3.DualHecke
