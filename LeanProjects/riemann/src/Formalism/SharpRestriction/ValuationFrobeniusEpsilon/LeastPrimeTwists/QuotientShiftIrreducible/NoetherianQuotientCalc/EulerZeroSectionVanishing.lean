import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleIso
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleShift

noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]

def GIso.quoBot (F : GMod B R k) (N : Submodule R F.M) (h : N = ⊥) : GIso (F.quo N) F where
  e := Submodule.quotEquivOfEqBot N h
  map_gr m := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact hx
    · intro hy
      exact ⟨N.mkQ y, ⟨y, hy, rfl⟩, rfl⟩

def GIso.subTop (F : GMod B R k) (N : Submodule R F.M) (h : N = ⊤) : GIso (F.sub N) F where
  e := LinearEquiv.ofTop N h
  map_gr m := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨⟨y, h ▸ Submodule.mem_top⟩, hy, rfl⟩

def GIso.quotOfZero (F : GMod B R k) (s : R) (h : ∀ x : F.M, s • x = 0) : GIso (F.quot s) F :=
  GIso.quoBot F _ (by
    rw [eq_bot_iff]
    rintro _ ⟨x, rfl⟩
    exact h x)

def GIso.annOfZero (F : GMod B R k) (s : R) (d : Deg k) (h : ∀ x : F.M, s • x = 0) :
    GIso (F.ann s d) (F.shift d) :=
  (GIso.subTop F _ (by
    rw [eq_top_iff]
    intro x _
    exact h x)).shift d

theorem chi_cons_of_zero (ts : List (Deg k × R)) (F : GMod B R k) (d : Deg k) (s : R)
    (h : ∀ x : F.M, s • x = 0) (m : Deg k) :
    chi ((d, s) :: ts) F m = chi ts F m - chi ts F (m - d) := by
  simp only [chi]
  rw [chi_congr ts _ _ (GIso.quotOfZero F s h) m, chi_congr ts _ _ (GIso.annOfZero F s d h) m,
    chi_shift]

end Formalism.MainNotions.V.Pf.V2.Calc
