import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.ManyEdges
import Formalism.SharpRestriction.GrowthBounds.WittFrameLocaliserOrders

noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.G.WittFrameLocaliserOrders

def FramesOK {n' r : ℕ} [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ N₁ G' : ℕ) (F : Frames n' r) : Prop :=
  F.TT = TT ∧ F.Valid L₁ N₁ ∧ (∀ j : ℤ, F.fr j (r - 1) - F.fr (j - 1) 0 < G') ∧
    (∀ j : ℤ, ∀ x ∈ F.LLset j, (((F.LLset j).filter (· ≤ x)).card ≤ r ∨
        (F.LLset j).card < ((F.LLset j).filter (· ≤ x)).card + r) → F.GapGt L₂ j x) ∧
    (∀ j : ℤ, F.GapGt L₂ j (F.fr j 0))

theorem de_pos_of {L₂ : ℕ} {de : ℝ} (h : L₂ < goodU de) : 0 < de := by
  by_contra hde
  have h1 : 1 / de ≤ 0 := by
    apply div_nonpos_of_nonneg_of_nonpos zero_le_one (not_lt.1 hde)
  have : goodU de = 0 := by
    unfold goodU
    exact Nat.ceil_eq_zero.2 h1
  omega

theorem frames_of {n' : ℕ} [NeZero n'] (TT : Finset (Fin n')) (r L₁ L₂ : ℕ) (de h x : ℝ) (hn : Even n')
    (hr : 2 ≤ r) (hL1 : 1 ≤ L₁) (hO : tableLineDegreeFive.OrbitHyp n' TT r L₁ L₂ de h x) :
    ∃ F : Frames n' r, FramesOK TT L₁ L₂ (orbitWindowCount r de h x) (goodG' r de h x) F := by
  obtain ⟨hgood, hL12, hLu, h3G⟩ := hO
  have hde : 0 < de := de_pos_of hLu
  have hg := hgood
  obtain ⟨_, hTiles, _⟩ := hgood
  have hu : 1 ≤ goodU de := bd_goodU_pos hde
  have hell : 0 < (6 * r + 1) * goodU de := Nat.mul_pos (by omega) hu
  have hGdef : goodG' r de h x = (orbitSmallMultiplicity r h x + 5) * ((6 * r + 1) * goodU de) := rfl
  have hMt : orbitSmallMultiplicity r h x + 1 < n' / ((6 * r + 1) * goodU de) := by
    have h1 : (orbitSmallMultiplicity r h x + 2) * ((6 * r + 1) * goodU de) ≤ n' := by
      have h2 : (orbitSmallMultiplicity r h x + 2) * ((6 * r + 1) * goodU de) ≤ (orbitSmallMultiplicity r h x + 5) * ((6 * r + 1) * goodU de) :=
        Nat.mul_le_mul_right _ (by omega)
      rw [hGdef] at h3G
      omega
    exact (Nat.le_div_iff_mul_le hell).2 h1
  obtain ⟨J, B, sidx, hS⟩ := bf_seq TT r (goodU de) (orbitSmallMultiplicity r h x) hn hu hTiles hMt
  obtain ⟨F, hTT, v1, v2, v3, v4, v5, v6, v7, c1, c2, c3, c4, c5⟩ :=
    bf_frames TT r (goodU de) L₂ (goodG' r de h x) (orbitSmallMultiplicity r h x) J B sidx hr hu hLu
      (by rw [hGdef]; exact Nat.mul_le_mul_right _ (by omega)) hS
  subst hTT
  have hL2n : L₂ ≤ n' := by have := bd_U_le_G' r de h x; omega
  have hI := fun y => bd_orbit_interval F.TT L₂ (r - 1) r de h x hL2n hg y
  have hcardL := fun j => bd_letters_card F L₂ (r - 1) r de h x (by omega) hg j (c3 j)
  have hLL : L₁ ≤ L₂ := by omega
  exact ⟨F, rfl, ⟨v1, v2, v3, v4, v5, v6,
      fun j => ⟨(v7 j).1, fun x hx hc => ⟨(v7 j).2 x hx hc, bd_gap_mono F hLL (c4 j x hx hc)⟩,
        bd_gap_mono F hLL (c5 j)⟩,
      hcardL,
      fun j x _ hw => bd_oldest_far F L₁ L₂ (by omega) (by omega) hI j x
        (bd_vectors_before F (by omega) v3 v4 v5 j x hw)⟩, c3, c4, c5⟩

end Formalism.MainNotions.Pf14
