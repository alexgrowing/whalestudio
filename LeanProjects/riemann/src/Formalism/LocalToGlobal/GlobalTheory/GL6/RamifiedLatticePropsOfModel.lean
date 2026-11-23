import Formalism.LocalToGlobal.GlobalTheory.GL6.EqOneOfCoprimeTorsionTwoPrimes
import Formalism.LocalToGlobal.GlobalTheory.GL6.RamifiedRankEqFinrank
import Formalism.LocalToGlobal.GlobalTheory.GL6.ExistsIntegerSmulMemOfSpanTop

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Classical NumberField

section Parts

variable (D : D7) (u : D.what₂.Word)

def RamifiedSlopeFormula : Prop :=
  (D.fm u).ramLat.mu = ((D.fm u).lat 0).mu -
    (D.R.f : ℝ) * Real.log (((D.mem u).A.T : ℝ) - 1) / (((D.mem u).A.T : ℝ) - 2)

def LatticeInclusionLength : Prop :=
  (∀ w, OverT D u w → (D.fm u).seenP w = true → ∀ v,
    (0 ≤ ((D.fm u).lam 0 ((D.fm u).tauOf w v)).detShift →
      (D.fm u).S 0 w ≤ (D.fm u).Bw 0 w v ∧
      (∃ n : ℕ, len D u w ((D.fm u).Bw 0 w v) ((D.fm u).S 0 w) = n ∧
        (n : ℚ) = (D.what₂.places.ramIdx w : ℚ) *
          ((D.duS u : ℚ) * (wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v)) : ℚ) / (D.R.k : ℚ))) ∧
      len D u w (Sram D u w) (imgL D u w (Uop D u 0 v) (Sram D u w)) ≤
        len D u w ((D.fm u).Bw 0 w v) ((D.fm u).S 0 w) +
          ((D.what₂.places.ramIdx w * ((D.R.k - 1) * D.duS u) : ℕ) : ℕ∞) +
          len D u w (imgL D u w (Uop D u 0 v) (Sram D u w)) (Sram D u w)) ∧
    (0 ≤ (D.fm u).bTop ((D.fm u).tauOf w v) →
      tL D u w ((D.fm u).bTop ((D.fm u).tauOf w v)) ((D.fm u).S 0 w) ≤ (D.fm u).Bw 0 w v ∧
      (∃ n : ℕ, len D u w ((D.fm u).Bw 0 w v) (tL D u w ((D.fm u).bTop ((D.fm u).tauOf w v)) ((D.fm u).S 0 w)) = n ∧
        (n : ℚ) = (D.what₂.places.ramIdx w : ℚ) * ((D.duS u : ℚ) *
          ((wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v)) : ℚ) + (D.R.k : ℚ) * ((D.fm u).bTop ((D.fm u).tauOf w v) : ℚ)) /
            (D.R.k : ℚ))) ∧
      len D u w (Sram D u w)
          (imgL D u w ((((D.mem u).A.T : ℂ) ^ (D.fm u).bTop ((D.fm u).tauOf w v)) • Uop D u 0 v) (Sram D u w)) ≤
        len D u w ((D.fm u).Bw 0 w v) (tL D u w ((D.fm u).bTop ((D.fm u).tauOf w v)) ((D.fm u).S 0 w)) +
          ((D.what₂.places.ramIdx w * ((D.R.k - 1) * D.duS u) : ℕ) : ℕ∞) +
          len D u w (imgL D u w ((((D.mem u).A.T : ℂ) ^ (D.fm u).bTop ((D.fm u).tauOf w v)) • Uop D u 0 v) (Sram D u w))
            (Sram D u w)))

end Parts

theorem ramified_lattice_props_of_model (D : D7) (u : D.what₂.Word) (M : FreeRankModel (D.mem u).A) (hS : HidaSetting D u) (hd : 0 < D.duS u)
    (hb : RamifiedSlopeFormula D u) (hl : LatticeInclusionLength D u) : Conclusion2 D u :=
  ⟨ramified_rank_formula D u M hS, hb, ramified_max_slope_le_of_model D u M hS hd, hl⟩

theorem ramified_lattice_of_free_model
    (h : ∀ (D : D7) (u : D.what₂.Word), FormsCompatible D u → HidaSetting D u → admS D u →
      Nonempty (FreeRankModel (D.mem u).A) ∧ 0 < D.duS u ∧ RamifiedSlopeFormula D u ∧ LatticeInclusionLength D u) : RamifiedLatticeFamily := by
  intro D u hF hS hA
  obtain ⟨⟨M⟩, hd, hb, hl⟩ := h D u hF hS hA
  exact ramified_lattice_props_of_model D u M hS hd hb hl

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
