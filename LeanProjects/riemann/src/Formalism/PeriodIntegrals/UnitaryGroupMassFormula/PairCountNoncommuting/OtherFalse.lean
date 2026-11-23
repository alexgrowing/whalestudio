import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.CBCardNC

open Finset

namespace PairCountNCWork

open Formalism.MainNotions.Ext.CutB

variable {N : ℕ} (ε : Fin N → Bool)

def toNC (p : {a // ε a = true} × {b // ε b = false}) : cBNC ε :=
  if h : p.1.1 < p.2.1 then
    ⟨(p.1.1, p.2.1), h, by rw [p.1.2, p.2.2]; decide⟩
  else
    ⟨(p.2.1, p.1.1), lt_of_le_of_ne (not_lt.mp h) (fun e => by
        have e' : p.2.1 = p.1.1 := e
        have h1 := p.1.2; have h2 := p.2.2; rw [e', h1] at h2; exact absurd h2 (by decide)),
      by rw [p.1.2, p.2.2]; decide⟩

theorem other_true {x y : Fin N} (hne : ε x ≠ ε y) (hx : ¬ ε x = true) : ε y = true := by
  cases hy : ε y <;> cases hx' : ε x <;> simp_all

theorem other_false {x y : Fin N} (hne : ε x ≠ ε y) (hx : ε x = true) : ε y = false := by
  cases hy : ε y <;> cases hx' : ε x <;> simp_all

def ofNC (q : cBNC ε) : {a // ε a = true} × {b // ε b = false} :=
  if hx : ε q.1.1 = true then
    (⟨q.1.1, hx⟩, ⟨q.1.2, other_false ε q.2.2 hx⟩)
  else
    (⟨q.1.2, other_true ε q.2.2 hx⟩, ⟨q.1.1, by simpa using hx⟩)

def equivNC : ({a // ε a = true} × {b // ε b = false}) ≃ cBNC ε where
  toFun := toNC ε
  invFun := ofNC ε
  left_inv := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    by_cases h : a < b
    · simp [toNC, ofNC, h, ha]
    · have hb' : ε b ≠ true := by simp [hb]
      simp [toNC, ofNC, h, hb']
  right_inv := by
    rintro ⟨⟨x, y⟩, hlt, hne⟩
    by_cases hx : ε x = true
    · simp [toNC, ofNC, hx, hlt]
    · have hnlt : ¬ y < x := not_lt.mpr hlt.le
      simp [toNC, ofNC, hx, hnlt]

theorem main : cBCardNC := by
  intro N ε
  rw [← Fintype.card_congr (equivNC ε), Fintype.card_prod, Fintype.card_subtype,
    Fintype.card_subtype]
  rfl

end PairCountNCWork
