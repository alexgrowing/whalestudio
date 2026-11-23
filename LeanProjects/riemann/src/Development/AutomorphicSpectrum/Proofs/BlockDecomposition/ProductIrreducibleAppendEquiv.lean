import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PrincipalSeriesSupport.PrinSeriesWord
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionPreservesSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicInductionInStagesProductOfProducts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTwoBlocksEmptyProductLeft

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents

namespace GlobalTheory.CompanionTheory.ProdStage

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open GlobalTheory.ProdFlatten in
unseal GlobalTheory.ProdFlatten.Iso GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.one GlobalTheory.ProdFlatten.two in

theorem equiv_of_iso_two {p q c r t N : ℕ} (x : Fin p → IrrGL k) (y : Fin q → IrrGL k) (w : Fin c → IrrGL k)
    (hx : ∑ a, (x a).1 = r) (hy : ∑ a, (y a).1 = t)
    (hz : ∑ a, (w a).1 = N) (e : r + t = N) (H : Iso (two e (pr x hx) (pr y hy)) (pr w hz)) :
    Nonempty ((ind₂ (stdSum e) (extTensor (prodIrr x hx) (prodIrr y hy))).Equiv (prodIrr w hz)) := H

open GlobalTheory.ProdFlatten in
unseal GlobalTheory.ProdFlatten.Iso GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.one in

theorem equiv_of_iso {q c N : ℕ} (y : Fin q → IrrGL k) (w : Fin c → IrrGL k)
    (hy : ∑ a, (y a).1 = N) (hz : ∑ a, (w a).1 = N) (H : Iso (pr y hy) (pr w hz)) :
    Nonempty ((prodIrr y hy).Equiv (prodIrr w hz)) := H

theorem ind₂_prodIrr_empty {c q N : ℕ} (x : Fin 0 → IrrGL k) (y : Fin q → IrrGL k) (w : Fin c → IrrGL k)
    (hw : List.ofFn w = List.ofFn y) (hx : ∑ a, (x a).1 = 0) (hy : ∑ a, (y a).1 = N)
    (hz : ∑ a, (w a).1 = N) (e : 0 + N = N) :
    Nonempty ((ind₂ (stdSum e) (extTensor (prodIrr x hx) (prodIrr y hy))).Equiv (prodIrr w hz)) := by
  have A : Nonempty ((ind₂ (stdSum e) (extTensor (prodIrr x hx) (prodIrr y hy))).Equiv (prodIrr y hy)) :=
    GlobalTheory.ProdReorder.ind₂_unit_left k N 0 e _ (prodIrr y hy) (isSmooth_prodIrr y hy)
      (fun a => (x a).1) (fun a => (x a).2.rep.V) (fun a => (x a).rep) (stdBlocks (fun a => (x a).1) hx)
  have B : Nonempty ((prodIrr y hy).Equiv (prodIrr w hz)) :=
    equiv_of_iso y w hy hz (GlobalTheory.ProdFlatten.pr_congr hw.symm hy hz)
  exact A.elim fun a => B.elim fun b => ⟨a.trans b⟩

theorem ind₂_prodIrr_equiv_zero {q c r t N : ℕ} (x : Fin 0 → IrrGL k) (y : Fin q → IrrGL k) (w : Fin c → IrrGL k)
    (hw : List.ofFn w = List.ofFn y) (hx : ∑ a, (x a).1 = r) (hy : ∑ a, (y a).1 = t)
    (hz : ∑ a, (w a).1 = N) (e : r + t = N) :
    Nonempty ((ind₂ (stdSum e) (extTensor (prodIrr x hx) (prodIrr y hy))).Equiv (prodIrr w hz)) := by
  have hr : r = 0 := by simpa using hx.symm
  subst hr
  have ht : t = N := by omega
  subst ht
  exact ind₂_prodIrr_empty x y w hw hx hy hz e

theorem ind₂_prodIrr_equiv_pos {p q c r t N : ℕ} (hp : p ≠ 0) (x : Fin p → IrrGL k) (y : Fin q → IrrGL k)
    (w : Fin c → IrrGL k) (hw : List.ofFn w = List.ofFn x ++ List.ofFn y) (hx : ∑ a, (x a).1 = r)
    (hy : ∑ a, (y a).1 = t) (hz : ∑ a, (w a).1 = N) (e : r + t = N) :
    Nonempty ((ind₂ (stdSum e) (extTensor (prodIrr x hx) (prodIrr y hy))).Equiv (prodIrr w hz)) :=
  equiv_of_iso_two x y w hx hy hz e
    (GlobalTheory.ProdFlatten.iso_symm (GlobalTheory.ProdFlatten.pr_append x y w hw (Or.inl hp) hx hy hz e))

theorem ind₂_prodIrr_equiv {p q c r t N : ℕ} (x : Fin p → IrrGL k) (y : Fin q → IrrGL k) (w : Fin c → IrrGL k)
    (hw : List.ofFn w = List.ofFn x ++ List.ofFn y) (hx : ∑ a, (x a).1 = r) (hy : ∑ a, (y a).1 = t)
    (hz : ∑ a, (w a).1 = N) (e : r + t = N) :
    Nonempty ((ind₂ (stdSum e) (extTensor (prodIrr x hx) (prodIrr y hy))).Equiv (prodIrr w hz)) := by
  cases p with
  | zero => exact ind₂_prodIrr_equiv_zero x y w (by simpa using hw) hx hy hz e
  | succ n => exact ind₂_prodIrr_equiv_pos (Nat.succ_ne_zero n) x y w hw hx hy hz e

theorem prod₂_prodIrr_append : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p q r t : ℕ) (x : Fin p → IrrGL k) (y : Fin q → IrrGL k)
    (hx : ∑ a, (x a).1 = r) (hy : ∑ a, (y a).1 = t) (h : ∑ a, (Fin.append x y a).1 = r + t),
    Nonempty ((prod₂ (prodIrr x hx) (prodIrr y hy)).Equiv (prodIrr (Fin.append x y) h)) :=
  fun _ _ _ _ _ _ _ _ _ x y hx hy h =>
    ind₂_prodIrr_equiv x y (Fin.append x y) (List.ofFn_fin_append x y) hx hy h rfl

end GlobalTheory.CompanionTheory.ProdStage
