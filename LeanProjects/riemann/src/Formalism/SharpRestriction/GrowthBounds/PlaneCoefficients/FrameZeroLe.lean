import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.SymGSupport
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.PosTLSurj
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembDd

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.Proposition5Numerics
open Formalism.MainNotions.G.WittFrameLocaliserOrders

namespace G2

variable {n' r : ℕ} [NeZero n'] {Fr : Frames n' r} {L₁ N₁ : ℕ}

theorem frame_zero_le (hV : Fr.Valid L₁ N₁) (j : ℤ) : Fr.fr j 0 ≤ Fr.fr j (r - 1) := by
  obtain ⟨_, _, hinc, _⟩ := hV
  have key : ∀ i, i ≤ r - 1 → Fr.fr j 0 ≤ Fr.fr j i := by
    intro i
    induction i with
    | zero => intro _; exact le_rfl
    | succ i ih => intro hi; exact (ih (by omega)).trans (hinc j i (by omega)).le
  exact key (r - 1) le_rfl

theorem zstep (hV : Fr.Valid L₁ N₁) (a : ℤ) : Fr.fr a (r - 1) < Fr.fr (a + 1) (r - 1) := (hV.2.2.2.1 a).trans_le (frame_zero_le hV (a + 1))

theorem zmono (hV : Fr.Valid L₁ N₁) (a b : ℤ) (hab : a ≤ b) : Fr.fr a (r - 1) ≤ Fr.fr b (r - 1) := by
  induction b, hab using Int.le_induction with
  | base => exact le_rfl
  | succ b _ ih => exact ih.trans (zstep hV b).le

theorem seg' (hV : Fr.Valid L₁ N₁) {J : ℕ} [NeZero J] {nL : ZMod J → ℕ}
    (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (x : TL J nL r) :
    Fr.fr (segZ x.1 - 1) (r - 1) < posTL Fr x ∧ posTL Fr x ≤ Fr.fr (segZ x.1) (r - 1) := by
  obtain ⟨j, l | m⟩ := x
  · have h := (mem_LLset Fr _ _).1 (llPos_mem Fr (segZ j) l.val (by rw [← hnL]; exact l.isLt))
    exact ⟨h.1.1, le_trans (le_of_lt h.1.2) (frame_zero_le hV (segZ j))⟩
  · have hr : 1 ≤ r := by have := m.isLt; omega
    have h := posTL_seg Fr hV hr hnL (⟨j, Sum.inr m⟩ : TL J nL r)
    exact ⟨h.1, h.2.1⟩

end G2

theorem restGeo : RestGeo := by
  intro n' r _ Fr L₁ N₁ hV p J _ nL hJ hnL j hj y hy x' hpos
  unfold lowP
  apply pow_dvd_pow
  obtain ⟨h1, h2⟩ := G2.seg' hV hnL x'
  have s0 := segZ_nonneg x'.1
  have s1 := segZ_lt x'.1
  simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc] at hy
  obtain ⟨⟨y1, y2⟩, -⟩ := hy
  have hper := hV.2.1
  have hJ' : (J : ℤ) = (Fr.J : ℤ) := by exact_mod_cast hJ
  have hjJ : (j : ℤ) < (Fr.J : ℤ) := by exact_mod_cast hj
  have hj0 : (0 : ℤ) ≤ (j : ℤ) := by positivity
  have hlast : Fr.fr ((Fr.J : ℤ) - 1) (r - 1) = Fr.fr (-1) (r - 1) + n' := by
    have := hper (-1) (r - 1)
    rw [← this]; congr 1
  have w1 := G2.zmono hV (-1) (segZ x'.1 - 1) (by omega)
  have w2 := G2.zmono hV (segZ x'.1) ((Fr.J : ℤ) - 1) (by omega)
  have w3 := G2.zmono hV (j : ℤ) ((Fr.J : ℤ) - 1) (by omega)
  have hwin : Fr.fr (-1) (r - 1) + 1 ≤ posTL Fr x' ∧ posTL Fr x' < Fr.fr (-1) (r - 1) + 1 + n' := by
    constructor <;> omega
  unfold Frames.dist
  apply Int.toNat_le_toNat
  by_cases hc : Fr.fr (-1) (r - 1) + 1 ≤ y
  · have hy' : posTL Fr x' = y := residue_position_injective_window n' _ _ _ hwin ⟨hc, by omega⟩ hpos
    have hs : segZ x'.1 ≤ (j : ℤ) := by
      by_contra hlt
      have := G2.zmono hV (j : ℤ) (segZ x'.1 - 1) (by omega)
      omega
    have := G2.zmono hV (segZ x'.1) (j : ℤ) hs
    omega
  · have a1 : Fr.fr ((j : ℤ) - 1 + Fr.J) 0 = Fr.fr ((j : ℤ) - 1) 0 + n' := hper _ _
    have a2 := hV.2.2.2.1 ((j : ℤ) - 2 + Fr.J)
    have a3 : (j : ℤ) - 2 + Fr.J + 1 = (j : ℤ) - 1 + Fr.J := by ring
    rw [a3] at a2
    have hJ1 : (1 : ℤ) ≤ (Fr.J : ℤ) := by omega
    have a4 := G2.zmono hV (-1) ((j : ℤ) - 2 + Fr.J) (by omega)
    have hy' : posTL Fr x' = y + n' :=
      residue_position_injective_window n' _ _ _ hwin ⟨by omega, by omega⟩ (by rw [DdG.posOf_add_n]; exact hpos)
    have a5 : Fr.fr ((j : ℤ) + Fr.J) (r - 1) = Fr.fr (j : ℤ) (r - 1) + n' := hper _ _
    have a6 := G2.zmono hV (segZ x'.1) ((j : ℤ) + Fr.J) (by omega)
    omega

end Formalism.MainNotions.PairMembershipBlocks
