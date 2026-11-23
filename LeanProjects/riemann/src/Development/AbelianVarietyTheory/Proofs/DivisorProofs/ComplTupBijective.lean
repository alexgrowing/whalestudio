import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotMatch

def complSub {a a' d : ℕ} (h : a + a' = d) (s : {s : Fin a → Fin d // StrictMono s}) : {s : Fin a' → Fin d // StrictMono s} :=
  ⟨Finset.orderEmbOfFin (Finset.univ.image s.1)ᶜ (by
      rw [Finset.card_compl, Finset.card_image_of_injective _ s.2.injective, Finset.card_univ, Fintype.card_fin,
        Fintype.card_fin]; omega), (Finset.orderEmbOfFin _ _).strictMono⟩

theorem range_complSub {a a' d : ℕ} (h : a + a' = d) (s : {s : Fin a → Fin d // StrictMono s}) :
    Set.range (complSub h s).1 = (Set.range s.1)ᶜ := by
  simp only [complSub, Finset.range_orderEmbOfFin, Finset.coe_compl, Finset.coe_image, Finset.coe_univ, Set.image_univ]

theorem complSub_complSub {a a' d : ℕ} (h : a + a' = d) (h' : a' + a = d) (s : {s : Fin a → Fin d // StrictMono s}) :
    complSub h' (complSub h s) = s := by
  apply Subtype.ext
  apply (StrictMono.range_inj (complSub h' (complSub h s)).2 s.2).1
  rw [range_complSub, range_complSub, compl_compl]

def complTup (D : D7) {a a' d : ℕ} {n : D.what₂.Tau → ℕ} (h : a + a' = d) (T : Tup D a d n) : Tup D a' d n :=
  fun τ k => complSub h (T τ k)

theorem complTup_bijective (D : D7) {a a' d : ℕ} {n : D.what₂.Tau → ℕ} (h : a + a' = d) :
    Function.Bijective (complTup D (n := n) h) := by
  refine Function.bijective_iff_has_inverse.2 ⟨complTup D (a := a') (a' := a) (by omega), fun T => ?_, fun T => ?_⟩ <;>
    funext τ k <;> simp only [complTup, complSub_complSub]

theorem exists_signed_perm {α β : Type} [Fintype α] [Fintype β] (c : α → β) (hc : Function.Bijective c) (ε : α → ℤˣ) :
    ∃ (M : α → β → ℤ) (M' : β → α → ℤ), (∀ T₁ T₂, ∑ T, M' T₁ T * M T T₂ = if T₁ = T₂ then 1 else 0) ∧
      ∀ T (f : β → ℂ), ∑ T', (M T T' : ℂ) * f T' = ((ε T : ℤ) : ℂ) * f (c T) := by
  classical
  refine ⟨fun T T' => if T' = c T then (ε T : ℤ) else 0, fun T' T => if T' = c T then (ε T : ℤ) else 0, fun T₁ T₂ => ?_,
    fun T f => ?_⟩
  · obtain ⟨T, rfl⟩ := hc.2 T₁
    rw [Finset.sum_eq_single T]
    · by_cases h : c T = T₂
      · subst h; simp [← Units.val_mul]
      · simp [h, Ne.symm h]
    · intro b _ hb
      have : c T ≠ c b := fun e => hb (hc.1 e).symm
      simp [this]
    · simp
  · rw [Finset.sum_eq_single (c T)]
    · simp
    · intro b _ hb; simp [hb]
    · simp

end GlobalTheory.BotMatch

end
