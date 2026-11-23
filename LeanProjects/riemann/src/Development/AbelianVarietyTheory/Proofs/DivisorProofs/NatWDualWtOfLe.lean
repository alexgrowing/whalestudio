import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDlNonneg
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationDenominatorsAndHostFieldSizes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteKernelNodeRankLeTotalRank
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SignedHC

namespace GlobalTheory.GridWtBound

theorem natW_dual_wtOf_le (n : ℕ) (E : Finset ℚ) (M : ℝ) (hM : 0 ≤ M) (hE : ∀ x ∈ E, |(x : ℝ)| ≤ M) (a : Fin n) :
    (((wtOf n E).dual.natW a : ℕ) : ℝ) ≤ 2 * M + 1 := by
  have hn : 0 < n := a.pos
  have hrev : Fin.rev (⟨n - 1, by omega⟩ : Fin n) = ⟨0, hn⟩ := by ext; simp; omega
  have key : (wtOf n E).dual.natW a = ((wtOf n E).w ⟨0, hn⟩ - (wtOf n E).w a.rev).toNat := by
    simp only [DomWeight.natW, DomWeight.detShift, DomWeight.dual, dif_pos hn, hrev]
    congr 1; ring
  have hd : (((wtOf n E).w ⟨0, hn⟩ - (wtOf n E).w a.rev : ℤ) : ℝ) ≤ 2 * M + 1 := by
    unfold wtOf
    split_ifs with h
    · have e0 := hE _ (descEnum_mem E h.1 ⟨0, hn⟩)
      have e1 := hE _ (descEnum_mem E h.1 a.rev)
      have f0 : ((⌊highestWeight E h.1 ⟨0, hn⟩⌋ : ℤ) : ℝ) ≤ ((highestWeight E h.1 ⟨0, hn⟩ : ℚ) : ℝ) := by
        exact_mod_cast Int.floor_le _
      have f1 : ((highestWeight E h.1 a.rev : ℚ) : ℝ) - 1 < ((⌊highestWeight E h.1 a.rev⌋ : ℤ) : ℝ) := by
        exact_mod_cast Int.sub_one_lt_floor _
      have hr : (0 : ℝ) ≤ ((a.rev : ℕ) : ℝ) := Nat.cast_nonneg _
      have g0 : ((highestWeight E h.1 ⟨0, hn⟩ : ℚ) : ℝ) ≤ M - ((n : ℝ) - 1) / 2 := by
        simp only [highestWeight]; push_cast; linarith [(abs_le.1 e0).2]
      have g1 : -M - ((n : ℝ) - 1) / 2 ≤ ((highestWeight E h.1 a.rev : ℚ) : ℝ) := by
        simp only [highestWeight]; push_cast; linarith [(abs_le.1 e1).1]
      push_cast
      linarith
    · simp; linarith
  rw [key]
  have c : (((wtOf n E).w ⟨0, hn⟩ - (wtOf n E).w a.rev).toNat : ℝ) =
      (((((wtOf n E).w ⟨0, hn⟩ - (wtOf n E).w a.rev).toNat : ℤ)) : ℝ) := (Int.cast_natCast _).symm
  rw [c, Int.toNat_eq_max]
  push_cast
  exact max_le (by push_cast at hd; exact hd) (by linarith)

end GlobalTheory.GridWtBound

namespace GlobalTheory.GridWtBound

theorem extend_bounds {n : ℕ} (d : ℕ) (f : Fin n → ℚ) (h : ℝ) (hh : 0 ≤ h)
    (hf : ∀ i, 0 ≤ ((f i : ℚ) : ℝ) ∧ ((f i : ℚ) : ℝ) ≤ h) (j : ℕ) :
    0 ≤ ((GridData.extend d f j : ℤ) : ℝ) ∧ ((GridData.extend d f j : ℤ) : ℝ) ≤ h := by
  unfold GridData.extend
  split_ifs with hj
  · obtain ⟨h1, h2⟩ := hf ⟨j - d, hj⟩
    have a1 : (0 : ℚ) ≤ f ⟨j - d, hj⟩ := by exact_mod_cast h1
    refine ⟨by exact_mod_cast Int.floor_nonneg.2 a1, le_trans ?_ h2⟩
    exact_mod_cast Int.floor_le _
  · simp [hh]

variable {D : D7}

theorem abs_entry_le (large₂ : SizeData₂ D) (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) :
    ∀ x ∈ entries (parV D 1 (i + 1) D.R.m τ), |(x : ℝ)| ≤ 14 * large₂.sc.b := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hgap, hbe, -⟩ := hs
  have hSc := large₂.Sc_pos
  have hsg : sLen D < gap D 1 := sLen_lt_gap D 1
  have hg1 : (1 : ℝ) ≤ (gap D 1 : ℝ) := by exact_mod_cast (by omega : 1 ≤ gap D 1)
  have hsg' : (sLen D : ℝ) + 1 ≤ (gap D 1 : ℝ) := by exact_mod_cast hsg
  have hm0 : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
  have hgb : (gap D 1 : ℝ) ≤ large₂.sc.b := by nlinarith
  have hb1 : (1 : ℝ) ≤ large₂.sc.b := by linarith
  have hScb : large₂.Sc ≤ large₂.sc.b := by nlinarith

  have hv : ∀ j, 0 ≤ ((GridData.extend 2 (D.hc τ).v j : ℤ) : ℝ) ∧ ((GridData.extend 2 (D.hc τ).v j : ℤ) : ℝ) ≤ large₂.Sc :=
    extend_bounds 2 _ _ hSc.le fun l => large₂.cloud_v τ l
  have hbl : ∀ l : Fin D.R.m, 0 ≤ (((D.hc τ).b l : ℚ) : ℝ) ∧ (((D.hc τ).b l : ℚ) : ℝ) ≤ 4 * large₂.sc.b := fun l => by
    obtain ⟨h1, h2⟩ := hbe τ l
    have h3 := (D.hc τ).gap_be l
    have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
    have h4 : (D.hc τ).b l ≤ (D.hc τ).e l := by linarith
    have h5 : (((D.hc τ).b l : ℚ) : ℝ) ≤ (((D.hc τ).e l : ℚ) : ℝ) := by exact_mod_cast h4
    exact ⟨by exact_mod_cast h1.le, h5.trans h2⟩
  have hel : ∀ l : Fin D.R.m, 0 ≤ (((D.hc τ).e l : ℚ) : ℝ) ∧ (((D.hc τ).e l : ℚ) : ℝ) ≤ 4 * large₂.sc.b := fun l => by
    obtain ⟨h1, h2⟩ := hbe τ l
    have h3 := (D.hc τ).gap_be l
    have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
    have h4 : 0 ≤ (D.hc τ).e l := by linarith
    exact ⟨by exact_mod_cast h4, h2⟩
  have hb := extend_bounds 1 _ _ (by linarith) hbl
  have he := extend_bounds 1 _ _ (by linarith) hel
  have htb : (D.R.t : ℝ) ≤ 8 * large₂.sc.b := by
    obtain ⟨h1, h2⟩ := hbe τ ⟨0, by omega⟩
    have h3 := (D.hc τ).gap_be ⟨0, by omega⟩
    have h3' := (Rat.cast_le (K := ℝ)).2 h3
    push_cast at h3'
    have h1' : (0 : ℝ) < (((D.hc τ).b ⟨0, by omega⟩ : ℚ) : ℝ) := by exact_mod_cast h1
    linarith

  have hcen : ∀ j, 1 ≤ j → j ≤ D.R.m → 0 ≤ ((cen D 1 τ j : ℤ) : ℝ) ∧ ((cen D 1 τ j : ℤ) : ℝ) ≤ large₂.sc.b := by
    intro j hj1 hj2
    have e := GridData.mid_eq (GridData.ofHCParam (D.hc τ) (sLen D) (gap D 1) 0) hj1
    have hv2 := hv 2
    have hj1' : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
    have hj2' : (j : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast hj2
    have hmid : 0 ≤ (((GridData.ofHCParam (D.hc τ) (sLen D) (gap D 1) 0).mid j : ℚ) : ℝ) ∧
        (((GridData.ofHCParam (D.hc τ) (sLen D) (gap D 1) 0).mid j : ℚ) : ℝ) ≤ large₂.sc.b := by
      rw [e]
      simp only [GridData.a, GridData.ofHCParam]
      push_cast
      constructor <;> nlinarith
    unfold cen
    refine ⟨by exact_mod_cast Int.floor_nonneg.2 (by exact_mod_cast hmid.1), le_trans ?_ hmid.2⟩
    exact_mod_cast Int.floor_le _
  intro x hx
  obtain ⟨sg, hsg⟩ := mem_entries.1 hx
  simp only [parV, shift, Finset.mem_image] at hsg
  obtain ⟨⟨y, sy⟩, hy, hxy⟩ := hsg
  have hx' := (congrArg Prod.fst hxy).symm
  simp only at hx'
  simp only [GridData.parD, Finset.mem_union, plus, Finset.mem_image, Finset.mem_biUnion, GridData.cloud,
    GridData.blockM, GridData.blockC, mem_block, Finset.mem_Icc, Prod.mk.injEq] at hy
  have hyb : |(y : ℝ)| ≤ 13 * large₂.sc.b := by
    rcases hy with ((⟨a0, ⟨j, -, hj⟩, hay, -⟩ | ⟨j, -, hj, -⟩) | ⟨a0, ⟨j, -, a, ha, hae⟩, hay, -⟩) |
      ⟨a0, ⟨j, ⟨hj1, hj2⟩, a, ha, hae⟩, hay, -⟩
    · have h : 0 ≤ (((num D 1 τ).v j : ℤ) : ℝ) ∧ (((num D 1 τ).v j : ℤ) : ℝ) ≤ large₂.Sc := hv j
      rw [← hay, ← hj]; push_cast
      rw [abs_le]; constructor <;> linarith
    · have h : 0 ≤ (((num D 1 τ).b j : ℤ) : ℝ) ∧ (((num D 1 τ).b j : ℤ) : ℝ) ≤ 4 * large₂.sc.b := hb j
      rw [← hj]; push_cast
      rw [abs_le]; constructor <;> linarith
    · have h : 0 ≤ (((num D 1 τ).e j : ℤ) : ℝ) ∧ (((num D 1 τ).e j : ℤ) : ℝ) ≤ 4 * large₂.sc.b := he j
      have ht : ((num D 1 τ).t : ℝ) ≤ 8 * large₂.sc.b := htb
      have ha' : (a : ℝ) + 1 ≤ ((num D 1 τ).t : ℝ) := by exact_mod_cast ha
      have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg _
      rw [← hay, hae]; push_cast
      rw [abs_le]; constructor <;> linarith
    · have hj1' : 1 ≤ j := by
        have : (num D 1 τ).m = D.R.m := rfl
        omega
      have h : 0 ≤ (((num D 1 τ).cen j : ℤ) : ℝ) ∧ (((num D 1 τ).cen j : ℤ) : ℝ) ≤ large₂.sc.b := hcen j hj1' hj2
      have hs : ((num D 1 τ).s : ℝ) + 1 ≤ (gap D 1 : ℝ) := hsg'
      have ha' : (a : ℝ) + 1 ≤ ((num D 1 τ).s : ℝ) := by exact_mod_cast ha
      have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg _
      rw [← hay, hae]; push_cast
      rw [abs_le]; constructor <;> linarith
  have hsh : |(((if Odd (i + 1 + D.R.m) then -(1 / 2) else 0 : ℚ)) : ℝ)| ≤ 1 / 2 := by
    split_ifs <;> norm_num
  rw [hx']
  push_cast
  calc |(y : ℝ) + (((if Odd (i + 1 + D.R.m) then -(1 / 2) else 0 : ℚ)) : ℝ)|
      ≤ |(y : ℝ)| + |(((if Odd (i + 1 + D.R.m) then -(1 / 2) else 0 : ℚ)) : ℝ)| := abs_add_le _ _
    _ ≤ 14 * large₂.sc.b := by linarith

end GlobalTheory.GridWtBound

namespace GlobalTheory.GridWtBound

theorem one_le_b {D : D7} (large₂ : SizeData₂ D) (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) : (1 : ℝ) ≤ large₂.sc.b := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hgap, -, -⟩ := hs
  have hSc := large₂.Sc_pos
  have hsg : sLen D < gap D 1 := sLen_lt_gap D 1
  have hg1 : (1 : ℝ) ≤ (gap D 1 : ℝ) := by exact_mod_cast (by omega : 1 ≤ gap D 1)
  have hm0 : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
  nlinarith

end GlobalTheory.GridWtBound
