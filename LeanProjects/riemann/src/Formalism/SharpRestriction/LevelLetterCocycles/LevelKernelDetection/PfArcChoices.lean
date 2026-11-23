import Formalism.SharpRestriction.LevelLetterCocycles.ExponentWindowSubsetShort

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.MainNotions.WachCoordinates

theorem hn_of {n j : ℕ} {ty : ZMod n → LT} {cuts : Finset (ZMod n)} {arcLen : ZMod n → ℕ}
    (hCu : CutsOK n j ty cuts arcLen) {c : ZMod n} (hc : c ∈ (cutsOf hCu).cuts) :
    (cutsOf hCu).ell c ≤ n :=
  (cutsOf hCu).ell_le c hc

theorem hj_of {n j : ℕ} {ty : ZMod n → LT} {cuts : Finset (ZMod n)} {arcLen : ZMod n → ℕ}
    (hCu : CutsOK n j ty cuts arcLen) {c : ZMod n} (hc : c ∈ (cutsOf hCu).cuts) :
    j ≤ (cutsOf hCu).ell c := by
  simp only [Formalism.MainNotions.WachCoordinates.cutsOf_cuts] at hc
  simp only [Formalism.MainNotions.WachCoordinates.cutsOf_ell]
  exact hCu.2.2.2.1 c hc

theorem three_g_le_parameter_bound {l : ℕ} (hl : 2 ≤ l) {G S η h : ℕ} (hg : gPar G S η ≤ h) :
    3 * gPar G S η ≤ (l - 1) * Formalism.ExponentWindows.E.parM l h (gPar G S η) := by
  unfold Formalism.ExponentWindows.E.parM
  have hd : 0 < l - 1 := by omega
  have h1 := Nat.lt_mul_div_succ (h + 2 * gPar G S η) hd
  exact le_of_lt (lt_of_le_of_lt (by omega) h1)

end Formalism.MainNotions.N.Ln03.Pf
