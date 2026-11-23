import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembTop
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.PosTLSurj

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords
open Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

section Geo

variable {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) {L₁ N₁ : ℕ}

theorem lf_fr_per (hV : Fr.Valid L₁ N₁) (j : ℤ) (i : ℕ) (m : ℤ) :
    Fr.fr (j + m * Fr.J) i = Fr.fr j i + m * n' := by
  induction m using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [show j + ((k : ℤ) + 1) * (Fr.J : ℤ) = (j + (k : ℤ) * Fr.J) + Fr.J by ring, hV.2.1, ih]
    ring
  | pred k ih =>
    have h := hV.2.1 (j + (-(k : ℤ) - 1) * Fr.J) i
    rw [show j + (-(k : ℤ) - 1) * (Fr.J : ℤ) + Fr.J = j + -(k : ℤ) * Fr.J by ring, ih] at h
    linarith

private theorem fr_mono_of_valid (hV : Fr.Valid L₁ N₁) (j : ℤ) :
    ∀ i i' : ℕ, i ≤ i' → i' < r → Fr.fr j i ≤ Fr.fr j i' := by
  intro i i' hii' hi'
  induction i' with
  | zero => rw [Nat.le_zero.mp hii']
  | succ k ih =>
    rcases Nat.lt_or_ge i (k + 1) with h | h
    · exact le_trans (ih (by omega) (by omega)) (hV.2.2.1 j k (by omega)).le
    · rw [le_antisymm hii' h]

private theorem fr_last_mono_in_index_of_valid (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (a : ℤ) :
    ∀ b : ℤ, a ≤ b → Fr.fr a (r - 1) ≤ Fr.fr b (r - 1) := by
  intro b hab
  induction b, hab using Int.le_induction with
  | base => exact le_rfl
  | succ k _ ih =>
    exact le_trans ih (le_trans (hV.2.2.2.1 k).le
      (fr_mono_of_valid Fr hV (k + 1) 0 (r - 1) (Nat.zero_le _) (by omega)))

theorem lf_dist_eq (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (j j' x y : ℤ) (hx1 : Fr.fr (j - 1) (r - 1) < x)
    (hx2 : x ≤ Fr.fr j (r - 1)) (hy1 : Fr.fr (j' - 1) (r - 1) < y) (hy2 : y ≤ Fr.fr j' (r - 1))
    (h : posOf n' y = posOf n' x) : Fr.dist j x = Fr.dist j' y := by
  have hn0 : (0 : ℤ) < n' := by exact_mod_cast NeZero.pos n'
  have hv : ((y % (n' : ℤ)).toNat % n') = ((x % (n' : ℤ)).toNat % n') := congrArg Fin.val h
  have ex1 : 0 ≤ x % (n' : ℤ) := Int.emod_nonneg _ hn0.ne'
  have ex2 : x % (n' : ℤ) < n' := Int.emod_lt_of_pos _ hn0
  have ey1 : 0 ≤ y % (n' : ℤ) := Int.emod_nonneg _ hn0.ne'
  have ey2 : y % (n' : ℤ) < n' := Int.emod_lt_of_pos _ hn0
  have hmod : y % (n' : ℤ) = x % (n' : ℤ) := by
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv
    omega
  obtain ⟨k, hk⟩ : (n' : ℤ) ∣ y - x := Int.dvd_of_emod_eq_zero (Int.emod_emod_of_dvd _ (dvd_refl _) ▸ (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hmod))
  have hJ1 := lf_fr_per Fr hV j (r - 1) k
  have hJ2 := lf_fr_per Fr hV (j - 1) (r - 1) k
  have hjj : j' = j + k * Fr.J := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hl | hl
    · have := fr_last_mono_in_index_of_valid Fr hV hr j' (j - 1 + k * Fr.J) (by linarith)
      rw [hJ2] at this
      nlinarith
    · have := fr_last_mono_in_index_of_valid Fr hV hr (j + k * Fr.J) (j' - 1) (by linarith)
      rw [hJ1] at this
      nlinarith
  unfold Frames.dist
  rw [hjj, hJ1]
  congr 1
  linarith

end Geo

section Lab

variable {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) (K : ℕ) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)

theorem labO_apply (hinj : Function.Injective fun x : TL J nL r => posOf n' (posTL Fr x))
    (rho : TL J nL r × Fin (r + K) → ℕ) (y : TL J nL r) (c : Fin (r + K)) :
    labO Fr K nL rho (posOf n' (posTL Fr y), c) = rho (y, c) := by
  classical
  simp only [labO, Finsupp.finset_sum_apply, Finsupp.single_apply]
  rw [Finset.sum_eq_single y]
  · rw [Finset.sum_eq_single c]
    · simp
    · intro c' _ hc'
      rw [if_neg]
      intro h
      exact hc' (Prod.ext_iff.mp h).2
    · intro h; exact absurd (Finset.mem_univ c) h
  · intro x _ hx
    apply Finset.sum_eq_zero
    intro c' _
    rw [if_neg]
    intro h
    exact hx (hinj (Prod.ext_iff.mp h).1)
  · intro h; exact absurd (Finset.mem_univ y) h

theorem labO_support (rho : TL J nL r × Fin (r + K) → ℕ) (v : Fin n' × Fin (r + K))
    (hv : v ∈ (labO Fr K nL rho).support) : ∃ x : TL J nL r, v.1 = posOf n' (posTL Fr x) := by
  classical
  by_contra hne
  push_neg at hne
  apply Finsupp.mem_support_iff.mp hv
  simp only [labO, Finsupp.finset_sum_apply, Finsupp.single_apply]
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro c _
  rw [if_neg]
  intro h
  exact hne x (Prod.ext_iff.mp h).1.symm

end Lab

theorem restLabG : RestLabG := by
  intro p _ n' r K _ _ _ O _ _ _ _S Fr TT L₁ L₂ N₁ G' deg d Y cP hMFH J _ Dt dPl dNo ka rho No Go hMH
  obtain ⟨hJ, hnL, -⟩ := hMH.1.1
  have hV : Fr.Valid L₁ N₁ := hMFH.frames.2.1
  have hr : 1 ≤ r := by have := hMFH.two_le_r; omega
  have hinj := posTL_inj Fr hV hr hJ hnL
  have hB := hMH.2.1
  unfold LabAt
  refine ⟨?_, ?_⟩
  · intro j x hx hW c
    by_cases hy : ∃ y : TL J Dt.nL r, posOf n' (posTL Fr y) = posOf n' x
    · obtain ⟨y, hy⟩ := hy
      rw [← hy, labO_apply Fr K Dt.nL hinj rho y c]
      have hlt := hB.1 y c
      have hseg := posTL_seg Fr hV hr hnL y
      have hxl := (Finset.mem_filter.mp hx).1
      rw [Finset.mem_Icc] at hxl
      have hd := lf_dist_eq Fr hV hr j (segZ y.1) x (posTL Fr y) (not_le.mp hW) hxl.2 hseg.1 hseg.2.1 hy
      rw [hd]
      exact hlt
    · push_neg at hy
      have h0 : labO Fr K Dt.nL rho (posOf n' x, c) = 0 := by
        by_contra hne
        obtain ⟨y, hy'⟩ := labO_support Fr K Dt.nL rho (posOf n' x, c) (Finsupp.mem_support_iff.mpr hne)
        exact hy y hy'.symm
      rw [h0]
      exact pow_pos (Fact.out : p.Prime).pos _
  · intro v hv
    obtain ⟨y, hy⟩ := labO_support Fr K Dt.nL rho v hv
    rw [hy]
    exact (posTL_seg Fr hV hr hnL y).2.2

end Formalism.MainNotions.Proposition5Numerics
