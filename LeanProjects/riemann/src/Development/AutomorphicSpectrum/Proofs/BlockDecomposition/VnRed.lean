import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.FUntwPf

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def vn (E : Spc) (k : ℕ) (a : Ht (l ^ k) E ((2 : ℕ) : ℤ) 1) (b : Ht (l ^ k) E ((0 : ℕ) : ℤ) (-1)) : Ht (l ^ k) E ((2 : ℕ) : ℤ) 0 :=
  (cup (l ^ k) a b).cast rfl rfl

theorem vn_red (h : A11) (E : Spc) (k : ℕ) (a : Ht (l ^ (k + 1)) E ((2 : ℕ) : ℤ) 1) (b : Ht (l ^ (k + 1)) E ((0 : ℕ) : ℤ) (-1)) :
    red (l ^ (k + 1)) (l ^ k) E ((2 : ℕ) : ℤ) 0 (vn E (k + 1) a b) =
      vn E k (red (l ^ (k + 1)) (l ^ k) E _ _ a) (red (l ^ (k + 1)) (l ^ k) E _ _ b) := by
  haveI : NeZero (l ^ (k + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  exact (h (l ^ (k + 1)) (l ^ k) (pow_dvd_pow l k.le_succ) E).1 a b

theorem step (hF : FCup) (hO : CupOne) (E : EtIn) (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (n : ℕ)
    (a : Ht (l ^ n) (sch.obj (gb M)) ((2 : ℕ) : ℤ) 1) (b : Ht (l ^ n) (sch.obj (gb M)) ((0 : ℕ) : ℤ) (-1))
    (hb : eM hN H r M n (-1) 0 b = oneH (AcrEl M.P n)) :
    eM hN H r M n 0 2 (vn (sch.obj (gb M)) n a b) = eM hN H r M n 1 2 a := by
  have h := hF E hN l H r K M n 1 (-1) 0 rfl 2 0 2 rfl a b
  have h2 := congrArg ((mulP (AcrEl M.P n)).cup (add_zero 2) (eM hN H r M n 1 2 a)) hb
  have h' : (mulP (AcrEl M.P n)).cup (add_zero 2) (eM hN H r M n 1 2 a) (oneH (AcrEl M.P n)) = eM hN H r M n 1 2 a :=
    hO _ _ _ _ _
  exact h.trans (h2.trans h')

theorem core (E : EtIn) (hF : FCup) (hO : CupOne) (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K)
    (x : Hl l (sch.obj (gb M)) (2 : ℕ) 1) (w : Hl l (sch.obj (gb M)) (0 : ℕ) (-1))
    (hw : ∀ n, eM hN H r M n (-1) 0 (w.1 n) = oneH (AcrEl M.P n)) :
    ∃ v : Hl l (sch.obj (gb M)) (2 : ℕ) 0, ∀ n, eM hN H r M n 0 2 (v.1 n) = eM hN H r M n 1 2 (x.1 n) := by
  have hv : ∀ k, red (l ^ (k + 1)) (l ^ k) (sch.obj (gb M)) ((2 : ℕ) : ℤ) 0
      (vn (sch.obj (gb M)) (k + 1) (x.1 (k + 1)) (w.1 (k + 1))) = vn (sch.obj (gb M)) k (x.1 k) (w.1 k) := by
    intro k
    have h1 : red (l ^ (k + 1)) (l ^ k) (sch.obj (gb M)) ((2 : ℕ) : ℤ) 1 (x.1 (k + 1)) = x.1 k := x.2 k
    have h2 : red (l ^ (k + 1)) (l ^ k) (sch.obj (gb M)) ((0 : ℕ) : ℤ) (-1) (w.1 (k + 1)) = w.1 k := w.2 k
    exact (vn_red E.a11 _ k _ _).trans (congrArg₂ (vn (sch.obj (gb M)) k) h1 h2)
  exact ⟨⟨fun k => vn (sch.obj (gb M)) k (x.1 k) (w.1 k), hv⟩, fun n => step hF hO E hN H r M n (x.1 n) (w.1 n) (hw n)⟩

theorem main : CrystallineSemistableComparison.E.FCup → CrystallineSemistableComparison.E.FRoot → CrystallineSemistableComparison.E.CupOne → CrystallineSemistableComparison.E.FUntw :=
  fun hF hR hO E hN l _ H r K M x => (hR E hN l H r K M (-1)).elim fun w hw => core E hF hO hN H r M x w hw

end GlobalTheory.CompanionTheory.FUntwPf
