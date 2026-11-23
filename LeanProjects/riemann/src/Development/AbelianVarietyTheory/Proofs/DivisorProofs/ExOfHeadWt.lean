import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqLastAddGaps
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefStep

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

open Classical in

def stepEx (σ : E →+* ℂ) (j : ℕ) : Ix Dw → ℤ :=
  fun ix => ix.elim 0 fun p => if p.1 = σ ∧ (p.2 : ℕ) < j then 1 else 0

open Classical in

theorem exOf_tailWt (τ : Psi H) (k : ℕ) (hk : Dw.p ≤ k) :
    AllWt.exOf Dw (GlobalTheory.NefWt.tailWt τ k) 0 = stepEx (conjEmb τ.1) (Dw.p + Dw.q - 1 - k) := by
  refine FlagMod.exOf_ext rfl (fun τ' i hi => ?_) (fun τ' i hi => ?_)
  · have h1 : ¬ (τ' = τ ∧ k < (i : ℕ)) := fun h => by
      have := i.2; have := FlagMod.mult_of_mem (Dw := Dw) τ'; omega
    have h2 : ¬ (τ'.1 = conjEmb τ.1 ∧ (i : ℕ) < Dw.p + Dw.q - 1 - k) := fun h =>
      GlobalTheory.AllWt.conj_not_mem τ (h.1 ▸ τ'.2)
    simp only [GlobalTheory.NefWt.tailWt, stepEx, Option.elim, if_neg h1, if_neg h2]
  · have hq := FlagMod.mult_conj (Dw := Dw) τ'
    have hi' := i.2
    by_cases e : τ' = τ
    · subst e
      have : k < Dw.p + (Dw.q - 1 - (i : ℕ)) ↔ (i : ℕ) < Dw.p + Dw.q - 1 - k := by omega
      by_cases h : (i : ℕ) < Dw.p + Dw.q - 1 - k
      · simp [GlobalTheory.NefWt.tailWt, stepEx, h, this.2 h]
      · simp [GlobalTheory.NefWt.tailWt, stepEx, h, mt this.1 h]
    · have hc : conjEmb τ'.1 ≠ conjEmb τ.1 := fun h => e (Subtype.ext (by
        rw [← GlobalTheory.AllWt.conjEmb_conjEmb τ'.1, h, GlobalTheory.AllWt.conjEmb_conjEmb]))
      simp [GlobalTheory.NefWt.tailWt, stepEx, e, hc]

open Classical in

theorem exOf_headWt (τ : Psi H) (k : ℕ) (hk : k < Dw.p) :
    AllWt.exOf Dw (GlobalTheory.NefWt.headWt τ k) 0 = stepEx τ.1 (k + 1) := by
  refine FlagMod.exOf_ext rfl (fun τ' i hi => ?_) (fun τ' i hi => ?_)
  · by_cases e : τ' = τ
    · subst e
      by_cases h : (i : ℕ) ≤ k
      · simp [GlobalTheory.NefWt.headWt, stepEx, h, Nat.lt_succ_of_le h]
      · simp [GlobalTheory.NefWt.headWt, stepEx, h, show ¬ (i : ℕ) < k + 1 by omega]
    · have hc : τ'.1 ≠ τ.1 := fun h => e (Subtype.ext h)
      simp [GlobalTheory.NefWt.headWt, stepEx, e, hc]
  · have hq := FlagMod.mult_conj (Dw := Dw) τ'
    have h1 : ¬ (τ' = τ ∧ Dw.p + (Dw.q - 1 - (i : ℕ)) ≤ k) := fun h => by omega
    have h2 : ¬ (conjEmb τ'.1 = τ.1 ∧ (i : ℕ) < k + 1) := fun h =>
      GlobalTheory.AllWt.conj_not_mem τ' (h.1 ▸ τ.2)
    simp only [GlobalTheory.NefWt.headWt, stepEx, Option.elim, if_neg h1, if_neg h2, neg_zero]

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagMod.FlagCover Y)
  (Z : Comp Xo c)

theorem L₀_tailWt (τ : Psi H) (k : ℕ) (hk : Dw.p ≤ k) :
    L₀ X Z (GlobalTheory.NefWt.tailWt τ k) = LL₀ X Z (stepEx (conjEmb τ.1) (Dw.p + Dw.q - 1 - k)) :=
  congrArg (LL₀ X Z) (exOf_tailWt τ k hk)

theorem L₀_headWt (τ : Psi H) (k : ℕ) (hk : k < Dw.p) :
    L₀ X Z (GlobalTheory.NefWt.headWt τ k) = LL₀ X Z (stepEx τ.1 (k + 1)) :=
  congrArg (LL₀ X Z) (exOf_headWt τ k hk)

end GlobalTheory.NefStep
