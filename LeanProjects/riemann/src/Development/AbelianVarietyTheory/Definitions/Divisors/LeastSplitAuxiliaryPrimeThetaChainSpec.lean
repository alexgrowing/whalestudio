import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise

namespace GlobalTheory.ChiGrid

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

open GlobalTheory.SignedHC Finset

section Comb

variable {G : GlobalTheory.SignedHC.GridData}

theorem blockC'_between (hm : G.NearMid) (hs : 1 ≤ G.s) (hg : G.s < G.ga) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ G.m) {x : ℚ}
    (hx : x ∈ G.blockC' i) : G.a i < x ∧ x < G.a i + G.ga := by
  have e1 := abs_le.1 (abs_sub_le_of_mem_block hx)
  have e2 := abs_le.1 (hm i (mem_Icc.2 ⟨h1, h2⟩))
  rw [G.mid_eq h1] at e2
  rw [Nat.cast_sub hs] at e1
  have e3 : (G.s : ℚ) + 1 ≤ G.ga := by exact_mod_cast hg
  push_cast at e1
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]

theorem a_add_le {i j : ℕ} (h : i < j) : G.a j + G.ga ≤ G.a i := by
  have e := G.a_sub_a i j
  have h1 : (i : ℚ) + 1 ≤ j := by exact_mod_cast h
  have h2 : (0 : ℚ) ≤ G.ga := by positivity
  nlinarith

theorem cloudHalf_lt {x : ℚ} (hx : x ∈ G.cloudHalf) : x < G.a G.m := by
  obtain ⟨i, h1, h2, rfl⟩ := GridData.mem_cloudHalf.1 hx
  have h3 : G.v i ≤ G.v 2 := by
    rcases h1.eq_or_lt with rfl | h
    · exact le_rfl
    · exact (G.v_anti 2 i le_rfl h h2).le
  have h4 : (G.v i : ℚ) ≤ G.v 2 := by exact_mod_cast h3
  have h5 : (0 : ℚ) ≤ G.ga := by positivity
  rw [G.a_m, GridData.vHalf]; linarith

theorem card_weightX_zero (hm : G.NearMid) (hs : 1 ≤ G.s) (hg : G.s < G.ga) : (G.weightX 0).card = G.nTop := by
  have hga : (0 : ℚ) < G.ga := by exact_mod_cast (by omega : 0 < G.ga)
  have hle : ∀ {i j : ℕ}, i ≤ j → G.a j ≤ G.a i := fun h => by
    rcases h.eq_or_lt with rfl | h
    · exact le_rfl
    · linarith [a_add_le (G := G) h]
  have c1 : G.tops.card = G.m + 1 := by
    rw [GridData.tops, card_image_of_injective, card_range]
    intro i j h
    rcases lt_trichotomy i j with h' | h' | h'
    · linarith [a_add_le (G := G) h']
    · exact h'
    · linarith [a_add_le (G := G) h']
  have c2 : G.cloudHalf.card = G.k - 1 := by
    rw [GridData.cloudHalf, card_image_of_injOn, Nat.card_Icc]
    · omega
    · intro i hi j hj h
      have hi := mem_Icc.1 (mem_coe.1 hi)
      have hj := mem_Icc.1 (mem_coe.1 hj)
      have e : G.v i = G.v j := by
        have : (G.v i : ℚ) = G.v j := by simp only [GridData.vHalf] at h; linarith
        exact_mod_cast this
      rcases lt_trichotomy i j with h' | h' | h'
      · exact absurd e (G.v_anti i j hi.1 h' hj.2).ne'
      · exact h'
      · exact absurd e (G.v_anti j i hj.1 h' hi.2).ne
  have c3 : ((Icc 1 G.m).biUnion G.blockC').card = G.m * (G.s - 1) := by
    rw [card_biUnion]
    · simp [GridData.blockC']
    · intro i hi j hj hij
      have hi := mem_Icc.1 (mem_coe.1 hi)
      have hj := mem_Icc.1 (mem_coe.1 hj)
      refine disjoint_left.2 fun x h1 h2 => ?_
      have b1 := blockC'_between hm hs hg hi.1 hi.2 h1
      have b2 := blockC'_between hm hs hg hj.1 hj.2 h2
      rcases lt_or_gt_of_ne hij with h | h <;> linarith [a_add_le (G := G) h, b1.1, b1.2, b2.1, b2.2]
  have d1 : Disjoint G.tops G.cloudHalf := disjoint_left.2 fun x h1 h2 => by
    obtain ⟨i, hi, rfl⟩ := GridData.mem_tops.1 h1
    linarith [cloudHalf_lt h2, hle hi]
  have d2 : Disjoint (G.tops ∪ G.cloudHalf) ((Icc 1 G.m).biUnion G.blockC') := disjoint_left.2 fun x h1 h2 => by
    obtain ⟨i, hi, h2⟩ := mem_biUnion.1 h2
    have hi := mem_Icc.1 hi
    have b := blockC'_between hm hs hg hi.1 hi.2 h2
    rcases mem_union.1 h1 with h1 | h1
    · obtain ⟨l, -, rfl⟩ := GridData.mem_tops.1 h1
      rcases lt_or_ge l i with h | h
      · linarith [a_add_le (G := G) h, b.2]
      · linarith [hle h, b.1]
    · linarith [cloudHalf_lt h1, hle hi.2, b.1]
  have := G.two_le_k
  rw [GridData.weightX, GridData.entries_lam, Icc_eq_empty (a := 1) (b := 0) (by omega), biUnion_empty, union_empty,
    card_union_of_disjoint d2, card_union_of_disjoint d1, c1, c2, c3, GridData.nTop, G.n_eq]
  omega

theorem inCoset_weightX_zero (hs : Odd G.s) : InCoset (1 / 2) (G.weightX 0) := by
  intro x hx
  rcases GridData.mem_weightX.1 hx with h | h | ⟨i, -, -, h⟩ | ⟨l, h1, h2, -⟩
  · obtain ⟨i, -, rfl⟩ := GridData.mem_tops.1 h
    exact ⟨G.v 2 + (G.m + 1 - i) * G.ga, by unfold GridData.a; push_cast; ring⟩
  · obtain ⟨i, -, -, rfl⟩ := GridData.mem_cloudHalf.1 h
    exact ⟨G.v i - 1, by unfold GridData.vHalf; push_cast; ring⟩
  · obtain ⟨a, -, rfl⟩ := mem_block.1 h
    obtain ⟨u, hu⟩ := hs
    refine ⟨G.cen i + u - 1 - a, ?_⟩
    rw [hu, Nat.add_sub_cancel]; push_cast; ring
  · omega

end Comb

variable (D)

def sLen : ℕ := D.R.r + 6

def nRk : ℕ := D.R.r + 1

def bigN : ℕ := D.R.k + D.R.m * (D.R.t + sLen D + 1)

def rankV (i j : ℕ) : ℕ := D.R.r + j * D.R.t + i * sLen D

def rankP (i : ℕ) : ℕ := nRk D + i * (sLen D - 1)

def rankX (j : ℕ) : ℕ := rankP D D.R.m + j * (D.R.t + 1)

def cloudLen : ℕ :=
  univ.sup fun τ => ((GridData.ofHCParam (D.hc τ) 0 0 0).v 2 - (GridData.ofHCParam (D.hc τ) 0 0 0).v D.R.k).toNat

def GapBound (C : ℝ) (g : ℕ) : Prop :=
  C * (bigN D : ℝ) ^ 3 + C * (nRk D : ℝ) ^ 7 + C * (nRk D : ℝ) ^ 3 * Real.sqrt (cloudLen D) ≤ g ∧
    2 * bigN D ^ 3 + 2 * sLen D + 2 < g ∧ 48 * (nRk D : ℝ) ^ 2 * Real.sqrt D.R.m ≤ g

def gap (C : ℝ) : ℕ :=
  max (max ⌈C * (bigN D : ℝ) ^ 3 + C * (nRk D : ℝ) ^ 7 + C * (nRk D : ℝ) ^ 3 * Real.sqrt (cloudLen D)⌉₊
    (2 * bigN D ^ 3 + 2 * sLen D + 3)) ⌈48 * (nRk D : ℝ) ^ 2 * Real.sqrt D.R.m⌉₊

theorem gapBound_iff (C : ℝ) (g : ℕ) : GapBound D C g ↔ gap D C ≤ g := by
  simp only [GapBound, gap, max_le_iff, Nat.ceil_le, and_assoc, Nat.lt_iff_add_one_le]

theorem isLeast_gap (C : ℝ) : IsLeast {g | GapBound D C g} (gap D C) :=
  ⟨(gapBound_iff D C _).2 le_rfl, fun g hg => (gapBound_iff D C g).1 hg⟩

def cen (C : ℝ) (τ : D.what₂.Tau) (i : ℕ) : ℤ := ⌊(GridData.ofHCParam (D.hc τ) (sLen D) (gap D C) 0).mid i⌋

def num (C : ℝ) (τ : D.what₂.Tau) : GlobalTheory.SignedHC.GridData := GridData.ofHCParam (D.hc τ) (sLen D) (gap D C) (cen D C τ)

theorem num_nearMid (C : ℝ) (τ : D.what₂.Tau) : (num D C τ).NearMid := GridData.nearMid_of_floor _ fun _ _ => rfl

theorem num_ranks (C : ℝ) (τ : D.what₂.Tau) (i j : ℕ) : (num D C τ).rankD i j = rankV D i j ∧
    (num D C τ).rankP i = rankP D i ∧ (num D C τ).rankX j = rankX D j ∧ (num D C τ).bigN = bigN D :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem odd_r : Odd D.R.r := by
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  have := D.R.two_le_m
  exact ⟨a + b - 1, by unfold Ranks.r; omega⟩

theorem odd_sLen : Odd (sLen D) := (odd_r D).add_even (by decide)

theorem even_rankV (i j : ℕ) : Even (rankV D i j) ↔ Odd (i + j) := by
  have h1 := odd_r D
  have h2 := odd_sLen D
  have h3 := D.R.t_odd
  simp only [rankV, Nat.even_add, Nat.even_mul, ← Nat.not_even_iff_odd] at *
  tauto

theorem even_rankP (i : ℕ) : Even (rankP D i) :=
  (odd_r D).add_one.add (((odd_sLen D).tsub_odd odd_one).mul_left i)

theorem even_rankX (j : ℕ) : Even (rankX D j) := (even_rankP D _).add (D.R.t_odd.add_one.mul_left j)

theorem sLen_lt_gap (C : ℝ) : sLen D < gap D C := by
  have := (isLeast_gap D C).1.2.1
  omega

theorem card_weight (C : ℝ) (τ : D.what₂.Tau) : ((num D C τ).weightX 0).card = rankP D D.R.m :=
  card_weightX_zero (num_nearMid D C τ) (odd_sLen D).pos (sLen_lt_gap D C)

def La (C : ℝ) (τ : D.what₂.Tau) : DomWeight (rankP D D.R.m) where
  w := fun a => ⌊highestWeight _ (card_weight D C τ) a⌋
  anti := fun _ _ h => Int.floor_mono (highestWeight_antitone _ (inCoset_weightX_zero (odd_sLen D)) h)

theorem La_cast (C : ℝ) (τ : D.what₂.Tau) (a : Fin (rankP D D.R.m)) :
    ((La D C τ).w a : ℚ) = highestWeight _ (card_weight D C τ) a := by
  obtain ⟨z, hz⟩ := highestWeight_int (card_weight D C τ) (fun x hx => by
    obtain ⟨y, rfl⟩ := inCoset_weightX_zero (G := num D C τ) (odd_sLen D) x hx
    obtain ⟨u, hu⟩ := even_rankP D D.R.m
    exact ⟨y + 1 - u, by rw [hu]; push_cast; ring⟩) a
  simp [La, hz]

def parV (C : ℝ) (i j : ℕ) (τ : D.what₂.Tau) : SPar :=
  shift (if Odd (i + j) then -(1 / 2) else 0) ((num D C τ).parD i j)

theorem parV_zero (C : ℝ) {j : ℕ} (hj : j ≤ D.R.m) (τ : D.what₂.Tau) : parV D C 0 j τ = (Ptw D).Dpar j τ := by
  have h := GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D C) (cen D C τ)
  rw [GridData.dpar_eq (num D C τ) (Ptw D) τ rfl rfl rfl h.1 h.2.1 h.2.2 hj, parV, zero_add]
  rfl

abbrev q0 : ℕ := Formalism.MainNotions.q0Av D

theorem rPr_spec : (Formalism.MainNotions.rPrAv D).Prime ∧ ¬ Formalism.MainNotions.rPrAv D ∣
    LevelStarExponents.condE D * (D.host.pde - 1) * (D.host.pde' - 1) * Ideal.absNorm D.host.ccK := by
  have h1 : LevelStarExponents.condE D ≠ 0 := by
    have := D.host.qd_big
    unfold LevelStarExponents.condE
    exact mul_ne_zero (mul_ne_zero D.host.QS_pos.ne' (by omega)) (by omega)
  have h2 := D.host.pde_prime.two_le
  have h3 := D.host.pde'_prime.two_le
  have h4 : Ideal.absNorm D.host.ccK ≠ 0 := Ideal.absNorm_eq_zero_iff.not.2 D.host.ccK_ne_bot
  have h5 : LevelStarExponents.condE D * (D.host.pde - 1) * (D.host.pde' - 1) * Ideal.absNorm D.host.ccK ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero h1 (by omega)) (by omega)) h4
  obtain ⟨p, hp, hp'⟩ := Nat.exists_infinite_primes
    (LevelStarExponents.condE D * (D.host.pde - 1) * (D.host.pde' - 1) * Ideal.absNorm D.host.ccK + 1)
  exact Nat.sInf_mem (s := {p : ℕ | p.Prime ∧ ¬ p ∣ _}) ⟨p, hp', fun h => by have := Nat.le_of_dvd (Nat.pos_of_ne_zero h5) h; omega⟩

theorem leastSplitAuxiliaryPrimeThetaChain_spec : (q0 D).Prime ∧ q0 D % (Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D) = 1 ∧ ¬ q0 D ∣ Ideal.absNorm D.host.ccK := by
  have h1 : 0 < LevelStarExponents.condE D := by
    have := D.host.qd_big
    unfold LevelStarExponents.condE
    exact mul_pos (mul_pos D.host.QS_pos (by omega)) (by omega)
  have h2 := (rPr_spec D).1.two_le
  have h3 : 1 < Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D := by nlinarith
  have h4 : Ideal.absNorm D.host.ccK ≠ 0 := Ideal.absNorm_eq_zero_iff.not.2 D.host.ccK_ne_bot
  obtain ⟨p, hp, hlt, hm⟩ := Nat.exists_prime_gt_modEq_one (k := Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D)
    (Ideal.absNorm D.host.ccK) (by omega)
  refine Nat.sInf_mem (s := {p : ℕ | p.Prime ∧ p % _ = 1 ∧ ¬ p ∣ _}) ⟨p, hp, ?_, fun h => ?_⟩
  · rw [hm, Nat.mod_eq_of_lt h3]
  · have := Nat.le_of_dvd (by omega) h; omega

theorem leastSplitAuxiliaryPrime_ne_typePrimes : q0 D ≠ D.host.pde ∧ q0 D ≠ D.host.pde' := by
  have h := (leastSplitAuxiliaryPrimeThetaChain_spec D).2.1
  have h1 : Formalism.MainNotions.rPrAv D ∣ q0 D - 1 := by
    have := Nat.div_add_mod (q0 D) (Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D)
    rw [h] at this
    rw [← this, Nat.add_sub_cancel, mul_assoc]
    exact dvd_mul_right _ _
  have h2 := (rPr_spec D).2
  constructor <;> intro e <;> rw [e] at h1 <;> apply h2
  · exact ((h1.mul_left _).mul_right _).mul_right _
  · exact (h1.mul_left _).mul_right _

def sizeP (C b : ℝ) : ℝ :=
  C * (D.R.f : ℝ) ^ 2 * (nRk D : ℝ) ^ 6 *
    Real.log (b * nRk D * D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde' * |(discr D.host.E : ℝ)|)

def depth0 (C b : ℝ) : ℕ := ⌊sizeP D C b / Real.log (q0 D)⌋₊ + 1

theorem sizeP_lt (C b : ℝ) : sizeP D C b < depth0 D C b * Real.log (q0 D) := by
  have h : 0 < Real.log (q0 D) := Real.log_pos (by exact_mod_cast (leastSplitAuxiliaryPrimeThetaChain_spec D).1.one_lt)
  rw [← div_lt_iff₀ h, depth0]
  push_cast
  exact Nat.lt_floor_add_one _

def S1 : Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
  Formalism.L2.DIV.primesOf ((D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde' : ℕ) : 𝓞 D.host.F)

theorem S1_mem_OmF {v : HeightOneSpectrum (𝓞 D.host.F)} : v ∈ S1 D ↔
    ((D.host.g 0 : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal ∨ ((D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal ∨
      ((D.host.pde : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal ∨ ((D.host.pde' : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
  have h0 : D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde' ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
      D.host.pde_prime.ne_zero) D.host.pde'_prime.ne_zero
  rw [S1, Formalism.L2.DIV.mem_primesOf, and_iff_right (by exact_mod_cast h0)]
  simp only [Nat.cast_mul, v.isPrime.mul_mem_iff_mem_or_mem, or_assoc]

end GlobalTheory.ChiGrid

end
