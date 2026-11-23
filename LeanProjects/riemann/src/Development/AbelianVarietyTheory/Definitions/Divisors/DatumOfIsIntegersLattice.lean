import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPoints
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CmCurveGoodOutsidePrimePremises

noncomputable section

open WeierstrassCurve
open scoped IntermediateField

namespace GlobalTheory.CMModel

def Stable (L : PeriodPair) (F : IntermediateField ℚ ℂ) {ι : Type} (T : ι → ℂ) : Prop :=
  ∀ σ : ℂ ≃+* ℂ, (∀ x ∈ F, σ x = x) → ∃ e : ι ≃ ι, ∀ i, GlobalTheory.ConjPoint.IsConj L L σ (T i) (T (e i))

def IntV (V : ValuationSubring ℂ) (W : WeierstrassCurve ℂ) : Prop :=
  W.a₁ ∈ V ∧ W.a₂ ∈ V ∧ W.a₃ ∈ V ∧ W.a₄ ∈ V ∧ W.a₆ ∈ V

def ModelAt (V : ValuationSubring ℂ) (F : IntermediateField ℚ ℂ) (W : WeierstrassCurve ℂ) (D : ℂ) : Prop :=
  ∃ C : VariableChange ℂ, (C.u : ℂ) ∈ F ∧ C.r ∈ F ∧ C.s ∈ F ∧ C.t ∈ F ∧ IntV V (C • W) ∧
    V.valuation (C • W).Δ = V.valuation D

abbrev Sq (p : ℕ) : Type := {k : Fin p // ((k : ℕ) : ZMod p) ≠ 0 ∧ IsSquare ((k : ℕ) : ZMod p)}

open Classical in

instance (p : ℕ) : Fintype (Sq p) := Subtype.fintype _

def sqPt (p : ℕ) (t : ℂ) (k : Sq p) : ℂ := ((k.1 : ℕ) : ℂ) * t

def sqProd (p : ℕ) (L : PeriodPair) (t : ℂ) : ℂ := ∏ k : Sq p, L.derivWeierstrassP (sqPt p t k)

def shortTwist {R : Type} [CommRing R] (d a₄ a₆ : R) : WeierstrassCurve R := ⟨0, 0, 0, d ^ 2 * a₄, d ^ 3 * a₆⟩

structure Datum (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ) : Prop where

  mul : Formalism.L2.Th1.F.MulStable L (GlobalTheory.Published.sqrtNegNat p)

  g₂_mem : L.g₂ ∈ F

  g₃_mem : L.g₃ ∈ F

  notMem : t ∉ L.lattice

  ker : GlobalTheory.Published.sqrtNegNat p * t ∈ L.lattice

theorem stable_empty (L : PeriodPair) (F : IntermediateField ℚ ℂ) (T : Empty → ℂ) : Stable L F T :=
  fun _ _ => ⟨Equiv.refl _, fun i => i.elim⟩

theorem stable_of_isRat {L : PeriodPair} {F : IntermediateField ℚ ℂ} {ι : Type} {T : ι → ℂ}
    (h : ∀ i, GlobalTheory.ConjPoint.IsRat L F (T i)) : Stable L F T :=
  fun _ hσ => ⟨Equiv.refl _, fun i => (h i).isConj hσ⟩

theorem stable_single (L : PeriodPair) (t : ℂ) :
    Stable L ℚ⟮L.weierstrassP t, L.derivWeierstrassP t⟯ (fun _ : Unit => t) :=
  stable_of_isRat fun _ =>
    .inr ⟨IntermediateField.subset_adjoin _ _ (by simp), IntermediateField.subset_adjoin _ _ (by simp)⟩

example : Fintype.card (Sq 7) = 3 := by
  have h : ∀ k : Fin 7, (((k : ℕ) : ZMod 7) ≠ 0 ∧ IsSquare ((k : ℕ) : ZMod 7)) ↔ k = 1 ∨ k = 2 ∨ k = 4 := by
    decide
  rw [Fintype.card_congr (Equiv.subtypeEquivRight h)]; decide

example (L : PeriodPair) : shortTwist 1 (-L.g₂ / 4) (-L.g₃ / 4) = GlobalTheory.latticeCurve L := by
  simp [shortTwist, GlobalTheory.latticeCurve]

end GlobalTheory.CMModel
