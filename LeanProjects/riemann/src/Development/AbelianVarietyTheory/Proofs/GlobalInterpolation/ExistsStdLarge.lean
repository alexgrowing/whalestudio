import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

noncomputable section

namespace GlobalTheory.EX

def stdConst (CT2 C8 p m l : ℝ) : FC where
  Ct := 401
  Cc := 2
  CT2 := CT2
  CGam := m
  Csz := m
  Cr := 1
  CTu := 25
  Cdg := 1
  C5 := 1
  full := True
  GK := ⟨m, l, l, l, l, l, l, l, l, l, l, 5, 4, 1, l⟩
  cX := ⟨1, ⟨12, 3, m⟩⟩
  P :=
    { CkLow := l, Ck6 := l, CfL := l, cLL := l⁻¹, CnW := 10, Crho := l, CDelG := l, CLw := 11 * 405, Cj0 := 405,
      Cw := l, cw := 9 / 10, CDel := l, CCount := l, Ch0r := l, Ch0k := l, Ch0N := l, Cgap := l, CetaF := 6,
      CY := l, CYL := 9, Cpde := C8, CccK := 1, CF := m }
  T := { CP := p, eP := 12, Cp := 1, Cb := l, cTO := 377, ChT := l, CbN := l }

theorem stdConst_cPre (CT2 C8 p m l c : ℝ) (h : c ∈ (stdConst CT2 C8 p m l).cPre) : c = p := by
  simpa [FC.cPre, stdConst] using h

theorem stdConst_cMid (CT2 C8 p m l c : ℝ)
    (h : c ∈ (stdConst CT2 C8 p m l).cMid (stdConst CT2 C8 p m l).P.CF) : c = m := by
  simpa [FC.cMid, stdConst] using h

theorem stdConst_cLast (CT2 C8 p m l c : ℝ) (h : c ∈ (stdConst CT2 C8 p m l).cLast) : c = l := by
  simpa [FC.cLast, stdConst] using h

theorem exists_std_large (K K0 : TransportedAlt) (CT2 C8 : ℝ) (h8 : 1 ≤ C8) :
    ∃ C : FC, Std C ∧ C.CT2 = CT2 ∧ C.P.Cpde = C8 ∧ C.Large K C.P.CF ∧ C.Large K0 C.P.CF ∧ C.GK.Nonneg := by
  obtain ⟨p, hp1, hpK, hpK0⟩ : ∃ p : ℝ, 1000 ≤ p ∧ K.pre ≤ p ∧ K0.pre ≤ p :=
    ⟨max 1000 (max K.pre K0.pre), le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
      (le_max_right _ _).trans (le_max_right _ _)⟩
  obtain ⟨m, hm1, hmK, hmK0⟩ : ∃ m : ℝ, 1 ≤ m ∧ K.mid (stdConst CT2 C8 p 0 0).cOut ≤ m ∧
      K0.mid (stdConst CT2 C8 p 0 0).cOut ≤ m :=
    ⟨max 1 (max _ _), le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
      (le_max_right _ _).trans (le_max_right _ _)⟩
  obtain ⟨l, hl1, hlK, hlK0⟩ : ∃ l : ℝ, 1 ≤ l ∧
      K.last ((stdConst CT2 C8 p m 0).cOut ++ (stdConst CT2 C8 p m 0).cMid m) ≤ l ∧
      K0.last ((stdConst CT2 C8 p m 0).cOut ++ (stdConst CT2 C8 p m 0).cMid m) ≤ l :=
    ⟨max 1 (max _ _), le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
      (le_max_right _ _).trans (le_max_right _ _)⟩
  have hm0 : 0 ≤ m := by linarith
  have hl0 : 0 ≤ l := by linarith
  refine ⟨stdConst CT2 C8 p m l, ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, h8, hp1, ?_, ?_⟩,
    rfl, rfl, ⟨?_, trivial, ?_, ?_⟩, ⟨?_, trivial, ?_, ?_⟩, ?_⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, le_rfl, rfl⟩
  · intro c hc; rw [stdConst_cMid _ _ _ _ _ _ hc]; exact hm1
  · intro c hc; rw [stdConst_cLast _ _ _ _ _ _ hc]; exact hl1
  · intro c hc; rw [stdConst_cPre _ _ _ _ _ _ hc]; exact hpK
  · intro c hc; rw [stdConst_cMid _ _ _ _ _ _ hc]; exact hmK
  · intro c hc; rw [stdConst_cLast _ _ _ _ _ _ hc]; exact hlK
  · intro c hc; rw [stdConst_cPre _ _ _ _ _ _ hc]; exact hpK0
  · intro c hc; rw [stdConst_cMid _ _ _ _ _ _ hc]; exact hmK0
  · intro c hc; rw [stdConst_cLast _ _ _ _ _ _ hc]; exact hlK0
  · exact ⟨hm0, hl0, hl0, hl0, hl0, hl0, hl0, hl0, hl0, hl0, hl0, by norm_num [stdConst], by norm_num [stdConst],
      by norm_num [stdConst], hl0⟩

end GlobalTheory.EX

end
