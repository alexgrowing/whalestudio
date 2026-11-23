import Formalism.LocalRingCardinality.DataParams₂

noncomputable section

namespace GlobalTheory.EX

open Formalism.BasicNotions

structure Scales (la : ℝ) where
  J : ℝ
  one_le_J : 1 ≤ J
  Win : Set ℝ
  windows : ∀ y : ℝ, ∃ Y : ℝ, y ≤ Y ∧ ∀ x : ℝ, Y ≤ x → x ≤ Y ^ la → x ∈ Win

namespace Scales

variable {la : ℝ}

def Mem (S : Scales la) (s : Scale) : Prop := s.J = S.J ∧ s.x ∈ S.Win

theorem unb (S : Scales la) (hla : 1 ≤ la) (y : ℝ) : ∃ x ∈ S.Win, y ≤ x := by
  obtain ⟨Y, hY, hW⟩ := S.windows (max y 1)
  have h1 : 1 ≤ Y := le_trans (le_max_right y 1) hY
  refine ⟨Y, hW Y le_rfl ?_, le_trans (le_max_left y 1) hY⟩
  calc Y = Y ^ (1 : ℝ) := (Real.rpow_one Y).symm
    _ ≤ Y ^ la := Real.rpow_le_rpow_of_exponent_le h1 hla

def scale (S : Scales la) (x eps : ℝ) (hx : 1 < x) (h0 : 0 < eps) (h1 : eps < 1 / 52) : Scale :=
  ⟨x, eps, hx, h0, h1, S.J, S.one_le_J⟩

theorem scale_mem (S : Scales la) {x eps : ℝ} (hx : 1 < x) (h0 : 0 < eps) (h1 : eps < 1 / 52) (hw : x ∈ S.Win) :
    S.Mem (S.scale x eps hx h0 h1) := ⟨rfl, hw⟩

theorem exists_mem (S : Scales la) (hla : 1 ≤ la) {eps : ℝ} (h0 : 0 < eps) (h1 : eps < 1 / 52) (y : ℝ) :
    ∃ s : Scale, s.eps = eps ∧ y ≤ s.x ∧ S.Mem s := by
  obtain ⟨x, hw, hx⟩ := S.unb hla (max y 2)
  have h2 : 1 < x := lt_of_lt_of_le (by norm_num) (le_of_max_le_right hx)
  exact ⟨S.scale x eps h2 h0 h1, rfl, le_of_max_le_left hx, S.scale_mem h2 h0 h1 hw⟩

def above (S : Scales la) (x0 : ℝ) : Scales la where
  J := S.J
  one_le_J := S.one_le_J
  Win := {x | x ∈ S.Win ∧ x0 < x}
  windows y := by
    obtain ⟨Y, h1, h2⟩ := S.windows (max y (x0 + 1))
    refine ⟨Y, le_of_max_le_left h1, fun x a b => ⟨h2 x a b, ?_⟩⟩
    have := le_of_max_le_right h1
    linarith

def univ (la J : ℝ) (hJ : 1 ≤ J) : Scales la := ⟨J, hJ, Set.univ, fun y => ⟨y, le_rfl, fun _ _ _ => trivial⟩⟩

theorem mem_univ {J : ℝ} {hJ : 1 ≤ J} {s : Scale} : (univ la J hJ).Mem s ↔ s.J = J :=
  ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

end Scales

end GlobalTheory.EX

end
