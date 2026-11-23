import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ShuffleChoices.ShufStd
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ShuffleChoices.UnitPowerEqResiduePower

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
  PositivityTheory.Rg.BcB.F.Choice PositivityTheory.Rg.BcB.F
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.Choice

namespace StandardSymmetricSums

def loF (n : ℕ) (i : Fin (n / 2)) : Fin n := ⟨i.val, by have := i.isLt; omega⟩
def hiF (n : ℕ) (i : Fin (n / 2)) : Fin n := ⟨n - 1 - i.val, by have := i.isLt; omega⟩

theorem lOf_eq {n : ℕ} (x : Fin n → ℤ) (i : Fin (n / 2)) : lOf x i = x (loF n i) - x (hiF n i) := rfl

def gg {n : ℕ} (x : Fin n → ℤ) (k k' : Fin n) : ℤ :=
  x k * (1 - 2 * if k' < k then 1 else 0) + x k' * (1 - 2 * if k < k' then 1 else 0)

theorem gg_lt {n : ℕ} (x : Fin n → ℤ) (p q : Fin n) (h : p < q) : gg x p q = x p - x q := by
  unfold gg; rw [if_neg (not_lt.2 h.le), if_pos h]; ring

theorem gg_gt {n : ℕ} (x : Fin n → ℤ) (p q : Fin n) (h : q < p) : gg x p q = x q - x p := by
  unfold gg; rw [if_pos h, if_neg (not_lt.2 h.le)]; ring

theorem p4 {n : ℕ} (x : Fin n → ℤ) (hx : ∀ p q : Fin n, p < q → x q + 2 ≤ x p) (i j : Fin (n / 2)) (hij : i ≠ j) :
    gg x (loF n i) (loF n j) + gg x (loF n i) (hiF n j) + (gg x (hiF n i) (loF n j) + gg x (hiF n i) (hiF n j)) =
      2 * max (lOf x i) (lOf x j) := by
  have hi' := i.isLt; have hj' := j.isLt
  rw [lOf_eq, lOf_eq]
  rcases lt_or_gt_of_ne (fun h' => hij (Fin.ext h')) with h | h
  · have c1 : loF n i < loF n j := show i.val < j.val from h
    have c2 : loF n i < hiF n j := show i.val < n - 1 - j.val by omega
    have c3 : loF n j < hiF n i := show j.val < n - 1 - i.val by omega
    have c4 : hiF n j < hiF n i := show n - 1 - j.val < n - 1 - i.val by omega
    rw [gg_lt x _ _ c1, gg_lt x _ _ c2, gg_gt x _ _ c3, gg_gt x _ _ c4]
    have := hx _ _ c1; have := hx _ _ c4
    rw [max_eq_left (by linarith)]; ring
  · have c1 : loF n j < loF n i := show j.val < i.val from h
    have c2 : loF n i < hiF n j := show i.val < n - 1 - j.val by omega
    have c3 : loF n j < hiF n i := show j.val < n - 1 - i.val by omega
    have c4 : hiF n i < hiF n j := show n - 1 - i.val < n - 1 - j.val by omega
    rw [gg_gt x _ _ c1, gg_lt x _ _ c2, gg_gt x _ _ c3, gg_lt x _ _ c4]
    have := hx _ _ c1; have := hx _ _ c4
    rw [max_eq_right (by linarith)]; ring

end StandardSymmetricSums

open StandardSymmetricSums

theorem coneTwo : ConeTwo := by
  intro n x _ hx
  have hx' : ∀ p q : Fin n, p < q → x q + 2 ≤ x p := hx
  unfold Cone
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have hi' := i.isLt; have hj' := j.isLt
    rw [lOf_eq, lOf_eq]
    have c1 : loF n i < loF n j := show i.val < j.val by omega
    have c4 : hiF n j < hiF n i := show n - 1 - j.val < n - 1 - i.val by omega
    have := hx' _ _ c1; have := hx' _ _ c4; linarith
  · have hi' := i.isLt
    rw [lOf_eq]
    have c : loF n i < hiF n i := show i.val < n - 1 - i.val by omega
    have := hx' _ _ c; linarith

end PositivityTheory.Rg.BcB.F.Choice

end
