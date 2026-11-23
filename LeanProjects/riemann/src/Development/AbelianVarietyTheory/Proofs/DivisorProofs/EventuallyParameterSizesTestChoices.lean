import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbLLMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairIntAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterSizeConditionsNumericBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteKernelNodeRankLeTotalRank

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean
open GlobalTheory.SignedHC

namespace GlobalTheory.KerConjMean.TopSizes

theorem natW_wtOf_le (n : ℕ) (E : Finset ℚ) (lo hi : ℝ) (hM : lo ≤ hi) (hE : ∀ x ∈ E, lo ≤ (x : ℝ) ∧ (x : ℝ) ≤ hi) (a : Fin n) :
    (((wtOf n E).natW a : ℕ) : ℝ) ≤ hi - lo + 1 := by
  have hn : 0 < n := a.pos
  have key : (wtOf n E).natW a = ((wtOf n E).w a - (wtOf n E).w ⟨n - 1, by omega⟩).toNat := by
    simp only [DomWeight.natW, DomWeight.detShift, dif_pos hn]
  have hd : (((wtOf n E).w a - (wtOf n E).w ⟨n - 1, by omega⟩ : ℤ) : ℝ) ≤ hi - lo + 1 := by
    unfold wtOf
    split_ifs with h
    · have e0 := hE _ (descEnum_mem E h.1 a)
      have e1 := hE _ (descEnum_mem E h.1 ⟨n - 1, by omega⟩)
      have f0 : ((⌊highestWeight E h.1 a⌋ : ℤ) : ℝ) ≤ ((highestWeight E h.1 a : ℚ) : ℝ) := by
        exact_mod_cast Int.floor_le _
      have f1 : ((highestWeight E h.1 ⟨n - 1, by omega⟩ : ℚ) : ℝ) - 1 <
          ((⌊highestWeight E h.1 ⟨n - 1, by omega⟩⌋ : ℤ) : ℝ) := by
        exact_mod_cast Int.sub_one_lt_floor _
      have hr : ((a : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast a.2
      have hc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn]; simp
      have g0 : ((highestWeight E h.1 a : ℚ) : ℝ) ≤ hi + ((n : ℝ) - 1) / 2 := by
        simp only [highestWeight]; push_cast; linarith [e0.2]
      have g1 : lo + ((n : ℝ) - 1) / 2 ≤ ((highestWeight E h.1 ⟨n - 1, by omega⟩ : ℚ) : ℝ) := by
        simp only [highestWeight, Rat.cast_sub, Rat.cast_div, Rat.cast_natCast, Rat.cast_one, Rat.cast_ofNat, hc]
        linarith [e1.1]
      push_cast
      linarith
    · simp; linarith
  rw [key]
  have c : ∀ z : ℤ, (z.toNat : ℝ) = (((z.toNat : ℕ) : ℤ) : ℝ) := fun z => (Int.cast_natCast _).symm
  rw [c, Int.toNat_eq_max]
  push_cast
  exact max_le (by push_cast at hd; exact hd) (by linarith)

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

theorem entry_bounds {D : D7} (large₂ : SizeData₂ D) (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) (j : ℕ) (τ : D.what₂.Tau) :
    ∀ x ∈ (num D 1 τ).weightX j, -(5 * large₂.sc.b) ≤ (x : ℝ) ∧ (x : ℝ) ≤ 2 * large₂.sc.b := by
  obtain ⟨hN, -, -, -, hm2, -, -, hb12⟩ := GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hs
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hgap, hbe, -⟩ := hs
  have hSc := large₂.Sc_pos
  have hg0 : (0 : ℝ) ≤ (gap D 1 : ℝ) := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
  have hScb : large₂.Sc ≤ large₂.sc.b := by nlinarith
  have hts : D.R.t + sLen D + 1 ≤ bigN D := by
    have : D.R.t + sLen D + 1 ≤ D.R.m * (D.R.t + sLen D + 1) := Nat.le_mul_of_pos_left _ (by omega)
    unfold bigN; omega
  have hts' : (D.R.t : ℝ) + (sLen D : ℝ) + 1 ≤ large₂.sc.b := le_trans (by exact_mod_cast hts) hN
  have ht0 : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  have hs0 : (0 : ℝ) ≤ (sLen D : ℝ) := Nat.cast_nonneg _
  have hv : ∀ j, 0 ≤ ((GridData.extend 2 (D.hc τ).v j : ℤ) : ℝ) ∧ ((GridData.extend 2 (D.hc τ).v j : ℤ) : ℝ) ≤ large₂.Sc :=
    extend_bounds 2 _ _ hSc.le fun l => large₂.cloud_v τ l
  have hel : ∀ l : Fin D.R.m, 0 ≤ (((D.hc τ).e l : ℚ) : ℝ) ∧ (((D.hc τ).e l : ℚ) : ℝ) ≤ 4 * large₂.sc.b := fun l => by
    obtain ⟨h1, h2⟩ := hbe τ l
    have h3 := (D.hc τ).gap_be l
    have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
    have h4 : 0 ≤ (D.hc τ).e l := by linarith
    exact ⟨by exact_mod_cast h4, h2⟩
  have he := extend_bounds 1 _ _ (by linarith) hel
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
  rcases GridData.mem_weightX.1 hx with h | h | ⟨i, hi1, hi2, h⟩ | ⟨l, -, -, h⟩
  · obtain ⟨i, hi, rfl⟩ := GridData.mem_tops.1 h
    have hi' : (i : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast (show i ≤ D.R.m from hi)
    have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg _
    have hv2 := hv 2
    simp only [GridData.a, num, GridData.ofHCParam]
    push_cast
    constructor <;> nlinarith
  · obtain ⟨i, -, -, rfl⟩ := GridData.mem_cloudHalf.1 h
    have h : 0 ≤ (((num D 1 τ).v i : ℤ) : ℝ) ∧ (((num D 1 τ).v i : ℤ) : ℝ) ≤ large₂.Sc := hv i
    simp only [GridData.vHalf]
    push_cast
    constructor <;> linarith
  · obtain ⟨a, ha, rfl⟩ := GlobalTheory.SignedHC.mem_block.1 h
    have h : 0 ≤ (((num D 1 τ).cen i : ℤ) : ℝ) ∧ (((num D 1 τ).cen i : ℤ) : ℝ) ≤ large₂.sc.b := hcen i hi1 hi2
    have h1 : (((num D 1 τ).s - 1 : ℕ) : ℝ) ≤ (sLen D : ℝ) := by
      exact_mod_cast (show sLen D - 1 ≤ sLen D from Nat.sub_le _ _)
    have ha' : (a : ℝ) + 1 ≤ (((num D 1 τ).s - 1 : ℕ) : ℝ) := by exact_mod_cast ha
    have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg _
    simp only [Rat.cast_sub, Rat.cast_add, Rat.cast_div, Rat.cast_natCast, Rat.cast_intCast, Rat.cast_one, Rat.cast_ofNat]
    constructor <;> linarith
  · obtain ⟨a, ha, rfl⟩ := GlobalTheory.SignedHC.mem_block.1 h
    have h : 0 ≤ (((num D 1 τ).e l : ℤ) : ℝ) ∧ (((num D 1 τ).e l : ℤ) : ℝ) ≤ 4 * large₂.sc.b := he l
    have h1 : ((num D 1 τ).t : ℝ) = (D.R.t : ℝ) := rfl
    have ha' : (a : ℝ) ≤ ((num D 1 τ).t : ℝ) := by exact_mod_cast Nat.lt_succ_iff.1 ha
    have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg _
    push_cast
    constructor <;> linarith

theorem sizesK : BigC fun {D} _ _ _ _ _ A _ _ _ _ _ _ ch _ b => 3 ≤ b ∧ 1 ≤ bigN D ∧ (bigN D : ℝ) ≤ b ∧ 1 ≤ D.R.f ∧ (D.R.f : ℝ) ≤ b ∧
  Fintype.card D.what₂.Tau ≤ D.R.f ∧ 0 ≤ D.host.rdE ∧ D.host.rdE ≤ b ∧ ∀ j : ℕ, j ≤ D.R.m →
    (ch.G.V (.top j)).rank ≤ bigN D ∧ ∀ τ i, ((wt ch.G (.top j) τ).natW i : ℝ) ≤ 8 * b := by
  refine ⟨0, fun CF _ => ⟨0, fun ε C _ => ⟨0, ?_⟩⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ hch _
  obtain ⟨hN, hf, hN1, hf1, -, hrd1, hrd, hb12⟩ := GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hS.size
  have hlb : 0 ≤ Real.log large₂.sc.b := Real.log_nonneg (by linarith)
  have hc : ch.sc.cGap = 1 := by
    have h : ch.sc = { cGap := 1, cDep := CF, b := large₂.sc.b } := hch
    rw [h]
  refine ⟨by linarith, hN1, hN, hf1, hf, (Lnk.card_Tau D).le, by linarith, ?_, fun j hj => ⟨?_, fun τ i => ?_⟩⟩
  · exact (Real.log_le_log_iff (by linarith) (by linarith)).1 (by linarith)
  · exact GlobalTheory.DefRank.rank_le_bigN ch.G (.top j) hj
  · have key : ∀ x ∈ entries (Node.par D ch.sc.cGap (.top j) τ), -(5 * large₂.sc.b) ≤ (x : ℝ) ∧ (x : ℝ) ≤ 2 * large₂.sc.b := by
      rw [hc]
      intro x hx
      have e : entries (Node.par D 1 (.top j) τ) = (num D 1 τ).weightX j := entries_plus _
      exact entry_bounds large₂ hS.size j τ x (e ▸ hx)
    have hw := natW_wtOf_le _ _ _ _ (by linarith) key i
    calc (((wt ch.G (.top j) τ).natW i : ℕ) : ℝ)
        = (((wtOf _ (entries (Node.par D ch.sc.cGap (.top j) τ))).natW i : ℕ) : ℝ) := rfl
      _ ≤ _ := hw
      _ ≤ 8 * large₂.sc.b := by linarith

end GlobalTheory.KerConjMean.TopSizes
