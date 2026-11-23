import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUniformRealThetaIntertwinerChainStep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsItWOfGlobIt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaIntertwinerAdjointIsRealThetaIntertwine
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfExpIffHasInfQ
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift
noncomputable section

namespace GlobalTheory.NegPair

def desc (T : Finset ℚ) : List ℚ := (T.sort (· ≤ ·)).reverse

theorem mem_desc {T : Finset ℚ} {y : ℚ} : y ∈ desc T ↔ y ∈ T := by simp [desc]

theorem desc_pairwise (T : Finset ℚ) : (desc T).Pairwise (· > ·) := by
  unfold desc
  rw [List.pairwise_reverse]
  exact ((Finset.pairwise_sort T (· ≤ ·)).and (Finset.sort_nodup T (· ≤ ·))).imp fun h => lt_of_le_of_ne h.1 h.2

theorem desc_length (T : Finset ℚ) : (desc T).length = T.card := by simp [desc]

def lowS (S : SPar) (c : ℚ) : Finset ℚ := (S.filter fun p => p.2 = true ∧ p.1 < c).image fun p => c - p.1

def highS (S : SPar) (c : ℚ) : Finset ℚ := (S.filter fun p => p.2 = true ∧ c < p.1).image fun p => c - p.1

def negS (S : SPar) (c : ℚ) : Finset ℚ := (S.filter fun p => p.2 = false).image fun p => c - p.1

theorem mem_lowS {S : SPar} {c y : ℚ} : y ∈ lowS S c ↔ (c - y, true) ∈ S ∧ c - y < c := by
  simp only [lowS, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨x, b⟩, ⟨h, rfl, h2⟩, rfl⟩
    simp only [sub_sub_cancel]; exact ⟨h, h2⟩
  · rintro ⟨h, h2⟩
    exact ⟨(c - y, true), ⟨h, rfl, h2⟩, by ring⟩

theorem mem_highS {S : SPar} {c y : ℚ} : y ∈ highS S c ↔ (c - y, true) ∈ S ∧ c < c - y := by
  simp only [highS, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨x, b⟩, ⟨h, rfl, h2⟩, rfl⟩
    simp only [sub_sub_cancel]; exact ⟨h, h2⟩
  · rintro ⟨h, h2⟩
    exact ⟨(c - y, true), ⟨h, rfl, h2⟩, by ring⟩

theorem mem_negS {S : SPar} {c y : ℚ} : y ∈ negS S c ↔ (c - y, false) ∈ S := by
  simp only [negS, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨x, b⟩, ⟨h, rfl⟩, rfl⟩
    simpa using h
  · intro h
    exact ⟨(c - y, false), ⟨h, rfl⟩, by ring⟩

theorem mem_dualPar_signed {l₁ l₂ : List ℚ} {c x : ℚ} {b : Bool} :
    (x, b) ∈ dualPar (signed l₁ l₂ (-c)) ↔ (b = true ∧ c - x ∈ l₁) ∨ (b = false ∧ c - x ∈ l₂) := by
  simp only [dualPar, GlobalTheory.Chain.signed, Finset.mem_image, Finset.mem_union, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨⟨y, b'⟩, hy, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rcases hy with ⟨z, hz, he⟩ | ⟨z, hz, he⟩ <;> simp only [Prod.mk.injEq] at he <;> obtain ⟨rfl, rfl⟩ := he
    · left; exact ⟨rfl, by simpa using hz⟩
    · right; exact ⟨rfl, by simpa using hz⟩
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
    · exact ⟨(c - x + -c, true), Or.inl ⟨c - x, h, rfl⟩, by simp⟩
    · exact ⟨(c - x + -c, false), Or.inr ⟨c - x, h, rfl⟩, by simp⟩

theorem recon_left (S : SPar) (c : ℚ) (hc : ∀ p ∈ S, p.1 ≠ c) :
    dualPar (signed (desc (lowS S c) ++ desc (highS S c)) ([] ++ desc (negS S c)) (-c)) = S := by
  ext ⟨x, b⟩
  rw [mem_dualPar_signed]
  simp only [List.mem_append, mem_desc, mem_lowS, mem_highS, mem_negS, List.nil_append, List.not_mem_nil,
    false_or, sub_sub_cancel]
  cases b
  · simp
  · have := hc (x, true)
    simp only [true_and, Bool.true_eq_false, false_and, or_false]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      rcases lt_or_gt_of_ne (this h) with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, h'⟩

theorem recon_right (S S' : SPar) (c : ℚ) (B : List ℚ)
    (h : ∀ x b, (x, b) ∈ S' ↔ (b = true ∧ (((x, true) ∈ S ∧ x < c) ∨ c - x ∈ B ∨ (x, false) ∈ S)) ∨
      (b = false ∧ (x, true) ∈ S ∧ c < x)) :
    dualPar (signed (desc (lowS S c) ++ B ++ desc (negS S c)) ([] ++ desc (highS S c)) (-c)) = S' := by
  ext ⟨x, b⟩
  rw [mem_dualPar_signed, h]
  simp only [List.mem_append, mem_desc, mem_lowS, mem_highS, mem_negS, List.nil_append, sub_sub_cancel, or_assoc]

end GlobalTheory.NegPair

namespace GlobalTheory.NegPair
open GlobalTheory.Grid

theorem gap_big (D : D7) : 2 * GlobalTheory.Grid.bigN D ^ 3 + 2 * GlobalTheory.Grid.sLen D + 2 < GlobalTheory.Grid.gap D := (GlobalTheory.Grid.isLeast_gap D).1.2.1

theorem sLen_ge (D : D7) : 6 ≤ GlobalTheory.Grid.sLen D := by unfold GlobalTheory.Grid.sLen; omega

theorem gapQ (D : D7) : 2 * (GlobalTheory.Grid.bigN D : ℚ) ^ 3 + 2 * GlobalTheory.Grid.sLen D + 2 < GlobalTheory.Grid.gap D := by exact_mod_cast gap_big D

theorem sLen_sub_one (D : D7) : ((GlobalTheory.Grid.sLen D - 1 : ℕ) : ℚ) = (GlobalTheory.Grid.sLen D : ℚ) - 1 := by
  rw [Nat.cast_sub (by have := sLen_ge D; omega)]; simp

theorem a_le_a (D : D7) (τ : D.what₂.Tau) {l l' : ℕ} (h : l ≤ l') : (GlobalTheory.Grid.grid D τ).a l' ≤ (GlobalTheory.Grid.grid D τ).a l := by
  have h1 := (GlobalTheory.Grid.grid D τ).a_sub_a l l'
  have h2 : (0 : ℚ) ≤ ((l' : ℚ) - l) * (GlobalTheory.Grid.grid D τ).ga :=
    mul_nonneg (sub_nonneg.2 (by exact_mod_cast h)) (by positivity)
  linarith

theorem a_add_le (D : D7) (τ : D.what₂.Tau) {l l' : ℕ} (h : l < l') :
    (GlobalTheory.Grid.grid D τ).a l' + (GlobalTheory.Grid.gap D : ℚ) ≤ (GlobalTheory.Grid.grid D τ).a l := by
  have h1 := (GlobalTheory.Grid.grid D τ).a_sub_a l l'
  have h3 : (1 : ℚ) ≤ (l' : ℚ) - l := by
    have : ((l + 1 : ℕ) : ℚ) ≤ l' := by exact_mod_cast h
    push_cast at this; linarith
  have h2 : (GlobalTheory.Grid.gap D : ℚ) ≤ ((l' : ℚ) - l) * (GlobalTheory.Grid.grid D τ).ga := by
    change (GlobalTheory.Grid.gap D : ℚ) ≤ ((l' : ℚ) - l) * (GlobalTheory.Grid.gap D : ℚ)
    nlinarith [(Nat.cast_nonneg (GlobalTheory.Grid.gap D) : (0 : ℚ) ≤ GlobalTheory.Grid.gap D)]
  linarith

theorem cen_near (D : D7) (τ : D.what₂.Tau) {l : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ D.R.m) :
    |((GlobalTheory.Grid.cen D τ l : ℤ) : ℚ) - ((GlobalTheory.Grid.grid D τ).a l + (GlobalTheory.Grid.gap D : ℚ) / 2)| ≤ 1 := by
  have := GlobalTheory.Grid.grid_nearMid D τ l (Finset.mem_Icc.2 ⟨h1, h2⟩)
  rw [GlobalTheory.SignedHC.GridData.mid_eq _ h1] at this
  exact this

theorem cloudHalf_lt (D : D7) (τ : D.what₂.Tau) {y : ℚ} (hy : y ∈ (GlobalTheory.Grid.grid D τ).cloudHalf) :
    y + (GlobalTheory.Grid.gap D : ℚ) + 1 ≤ (GlobalTheory.Grid.grid D τ).a D.R.m := by
  obtain ⟨i', h2, hk, rfl⟩ := GlobalTheory.SignedHC.GridData.mem_cloudHalf.1 hy
  have hv : (GlobalTheory.Grid.grid D τ).v i' ≤ (GlobalTheory.Grid.grid D τ).v 2 := by
    rcases eq_or_lt_of_le h2 with h | h
    · subst h; exact le_rfl
    · exact ((GlobalTheory.Grid.grid D τ).v_anti 2 i' le_rfl h hk).le
  have ha := (GlobalTheory.Grid.grid D τ).a_m
  have hv' : ((GlobalTheory.Grid.grid D τ).v i' : ℚ) ≤ (GlobalTheory.Grid.grid D τ).v 2 := by exact_mod_cast hv
  unfold GlobalTheory.SignedHC.GridData.vHalf
  change _ ≤ (GlobalTheory.Grid.grid D τ).a (GlobalTheory.Grid.grid D τ).m
  rw [ha]
  change _ ≤ _ + ((GlobalTheory.Grid.gap D : ℕ) : ℚ) + _
  linarith

theorem mem_blockTP {c y : ℚ} {len : ℕ} (h : y ∈ TPar.block c len) : |y - c| ≤ ((len : ℚ) - 1) / 2 := by
  obtain ⟨a', ha', rfl⟩ := Finset.mem_image.1 h
  have : (a' : ℚ) + 1 ≤ len := by exact_mod_cast (Finset.mem_range.1 ha')
  have h0 : (0 : ℚ) ≤ a' := Nat.cast_nonneg a'
  rw [abs_le]; constructor <;> linarith

theorem block_sym {c x : ℚ} {len : ℕ} : c - x ∈ block len ↔ x ∈ TPar.block c len := by
  unfold block TPar.block
  simp
  constructor
  · rintro ⟨m', hm, he⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hm
    refine ⟨d, by omega, ?_⟩
    push_cast at he ⊢; linarith
  · rintro ⟨a', ha, he⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt ha
    refine ⟨d, by omega, ?_⟩
    push_cast at he ⊢; linarith

theorem loc (D : D7) (τ : D.what₂.Tau) {i : ℕ} (hi : i < D.R.m) {p : ℚ × Bool} (hp : p ∈ (GlobalTheory.Grid.grid D τ).parPi i) :
    (p.1 ≤ (GlobalTheory.Grid.grid D τ).a (D.R.m - i) ∧ p.2 = true) ∨
      ∃ l < D.R.m - i, p.1 = (GlobalTheory.Grid.grid D τ).a l ∧ p.2 = decide (Even (D.R.m - i - l)) := by
  have hg := gapQ D
  have hs : (6 : ℚ) ≤ GlobalTheory.Grid.sLen D := by exact_mod_cast sLen_ge D
  have hN : (0 : ℚ) ≤ (GlobalTheory.Grid.bigN D : ℚ) ^ 3 := by positivity
  have hm : (GlobalTheory.Grid.grid D τ).m = D.R.m := rfl
  rcases GlobalTheory.SignedHC.GridData.mem_parPi.1 hp with ⟨l, hl, rfl⟩ | ⟨hc, h2⟩ | ⟨l, hl1, hl2, hb, h2⟩
  · rw [hm] at hl ⊢
    by_cases hlj : D.R.m - i ≤ l
    · left; exact ⟨a_le_a D τ hlj, by simp [hlj]⟩
    · right; exact ⟨l, by omega, rfl, by simp [hlj]⟩
  · left; refine ⟨?_, h2⟩
    have h1 := cloudHalf_lt D τ hc
    have h3 := a_le_a D τ (show D.R.m - i ≤ D.R.m by omega)
    have : (0 : ℚ) ≤ GlobalTheory.Grid.gap D := Nat.cast_nonneg _
    linarith
  · left; refine ⟨?_, h2⟩
    rw [hm] at hl1 hl2
    have hb' := mem_blockTP hb
    change |p.1 - ((GlobalTheory.Grid.cen D τ l : ℤ) : ℚ)| ≤ (((GlobalTheory.Grid.sLen D - 1 : ℕ) : ℚ) - 1) / 2 at hb'
    rw [sLen_sub_one] at hb'
    have hc := cen_near D τ (by omega : 1 ≤ l) hl2
    have h3 := a_le_a D τ (show D.R.m - i + 1 ≤ l from hl1)
    have h4 := (GlobalTheory.Grid.grid D τ).a_eq_succ_add (D.R.m - i)
    change _ = _ + ((GlobalTheory.Grid.gap D : ℕ) : ℚ) at h4
    rw [abs_le] at hb' hc
    linarith [hb'.2, hc.2]

end GlobalTheory.NegPair

namespace GlobalTheory.NegPair
open GlobalTheory.Grid

theorem blockC'_le (D : D7) (τ : D.what₂.Tau) {j l : ℕ} {x : ℚ} (hl1 : j + 1 ≤ l) (hl2 : l ≤ D.R.m)
    (hb : x ∈ (GlobalTheory.Grid.grid D τ).blockC' l) : x ≤ (GlobalTheory.Grid.grid D τ).a j := by
  have hg := gapQ D
  have hs : (6 : ℚ) ≤ GlobalTheory.Grid.sLen D := by exact_mod_cast sLen_ge D
  have hN : (0 : ℚ) ≤ (GlobalTheory.Grid.bigN D : ℚ) ^ 3 := by positivity
  have hb' := mem_blockTP hb
  change |x - ((GlobalTheory.Grid.cen D τ l : ℤ) : ℚ)| ≤ (((GlobalTheory.Grid.sLen D - 1 : ℕ) : ℚ) - 1) / 2 at hb'
  rw [sLen_sub_one] at hb'
  have hc := cen_near D τ (by omega : 1 ≤ l) hl2
  have h3 := a_le_a D τ hl1
  have h4 := (GlobalTheory.Grid.grid D τ).a_eq_succ_add j
  change _ = _ + ((GlobalTheory.Grid.gap D : ℕ) : ℚ) at h4
  rw [abs_le] at hb' hc
  linarith [hb'.2, hc.2]

theorem cen_bounds (D : D7) (τ : D.what₂.Tau) {i : ℕ} (hi : i < D.R.m) :
    (GlobalTheory.Grid.grid D τ).a (D.R.m - i) + (GlobalTheory.Grid.gap D : ℚ) / 2 - 1 ≤ ((GlobalTheory.Grid.cen D τ (D.R.m - i) : ℤ) : ℚ) ∧
    ((GlobalTheory.Grid.cen D τ (D.R.m - i) : ℤ) : ℚ) ≤ (GlobalTheory.Grid.grid D τ).a (D.R.m - i) + (GlobalTheory.Grid.gap D : ℚ) / 2 + 1 ∧
    (GlobalTheory.Grid.grid D τ).a (D.R.m - i - 1) = (GlobalTheory.Grid.grid D τ).a (D.R.m - i) + (GlobalTheory.Grid.gap D : ℚ) := by
  have hc := cen_near D τ (by omega : 1 ≤ D.R.m - i) (by omega)
  rw [abs_le] at hc
  refine ⟨by linarith [hc.1], by linarith [hc.2], ?_⟩
  exact (GlobalTheory.Grid.grid D τ).a_pred (by omega)

theorem mem_next (D : D7) (τ : D.what₂.Tau) {i : ℕ} (hi : i < D.R.m) (x : ℚ) (b : Bool) :
    (x, b) ∈ (GlobalTheory.Grid.grid D τ).parPi (i + 1) ↔
      (b = true ∧ (((x, true) ∈ (GlobalTheory.Grid.grid D τ).parPi i ∧ x < ((GlobalTheory.Grid.cen D τ (D.R.m - i) : ℤ) : ℚ)) ∨
        ((GlobalTheory.Grid.cen D τ (D.R.m - i) : ℤ) : ℚ) - x ∈ block (GlobalTheory.Grid.sLen D - 1) ∨
        (x, false) ∈ (GlobalTheory.Grid.grid D τ).parPi i)) ∨
      (b = false ∧ (x, true) ∈ (GlobalTheory.Grid.grid D τ).parPi i ∧ ((GlobalTheory.Grid.cen D τ (D.R.m - i) : ℤ) : ℚ) < x) := by
  have hg := gapQ D
  have hs : (6 : ℚ) ≤ GlobalTheory.Grid.sLen D := by exact_mod_cast sLen_ge D
  have hN : (0 : ℚ) ≤ (GlobalTheory.Grid.bigN D : ℚ) ^ 3 := by positivity
  obtain ⟨hcl, hcu, hj1⟩ := cen_bounds D τ hi
  have hm : (GlobalTheory.Grid.grid D τ).m = D.R.m := rfl
  have e1 : D.R.m - (i + 1) = D.R.m - i - 1 := by omega
  have e2 : D.R.m - (i + 1) + 1 = D.R.m - i := by omega

  have below : ∀ l, (GlobalTheory.Grid.grid D τ).a l < ((GlobalTheory.Grid.cen D τ (D.R.m - i) : ℤ) : ℚ) → D.R.m - i ≤ l := by
    intro l hl
    by_contra h
    have := a_le_a D τ (show l ≤ D.R.m - i - 1 by omega)
    linarith
  have above : ∀ l, ((GlobalTheory.Grid.cen D τ (D.R.m - i) : ℤ) : ℚ) < (GlobalTheory.Grid.grid D τ).a l → l < D.R.m - i := by
    intro l hl
    by_contra h
    have := a_le_a D τ (show D.R.m - i ≤ l by omega)
    linarith
  have lowj : ∀ y, y ≤ (GlobalTheory.Grid.grid D τ).a (D.R.m - i) → y < ((GlobalTheory.Grid.cen D τ (D.R.m - i) : ℤ) : ℚ) := by
    intro y hy; linarith
  have cl : ∀ y ∈ (GlobalTheory.Grid.grid D τ).cloudHalf, y ≤ (GlobalTheory.Grid.grid D τ).a (D.R.m - i) := by
    intro y hy
    have h1 := cloudHalf_lt D τ hy
    have h3 := a_le_a D τ (show D.R.m - i ≤ D.R.m by omega)
    have : (0 : ℚ) ≤ GlobalTheory.Grid.gap D := Nat.cast_nonneg _
    linarith
  constructor
  · intro h
    rcases GlobalTheory.SignedHC.GridData.mem_parPi.1 h with ⟨l, hl, he⟩ | ⟨hc, h2⟩ | ⟨l, hl1, hl2, hb, h2⟩
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rw [hm] at hl ⊢
      rw [e1]
      by_cases hlj : D.R.m - i ≤ l
      · left
        refine ⟨by simp; omega, Or.inl ⟨GlobalTheory.SignedHC.GridData.mem_parPi.2 (Or.inl ⟨l, hl, ?_⟩), lowj _ (a_le_a D τ hlj)⟩⟩
        simp [hm, hlj]
      · by_cases hl1 : l = D.R.m - i - 1
        · subst hl1
          left
          refine ⟨by simp, Or.inr (Or.inr (GlobalTheory.SignedHC.GridData.mem_parPi.2 (Or.inl ⟨_, hl, ?_⟩)))⟩
          have : D.R.m - i - (D.R.m - i - 1) = 1 := by omega
          simp [hm, hlj, this]
        · have hpar : D.R.m - i - l = (D.R.m - i - 1 - l) + 1 := by omega
          by_cases hev : Even (D.R.m - i - 1 - l)
          · left
            refine ⟨by simp [hev], Or.inr (Or.inr (GlobalTheory.SignedHC.GridData.mem_parPi.2 (Or.inl ⟨l, hl, ?_⟩)))⟩
            simp [hm, hlj, hpar, Nat.even_add_one, hev]
          · right
            refine ⟨by simp [hev]; omega, GlobalTheory.SignedHC.GridData.mem_parPi.2 (Or.inl ⟨l, hl, ?_⟩), ?_⟩
            · simp [hm, hlj, hpar, Nat.even_add_one, hev]
            · have := a_le_a D τ (show l ≤ D.R.m - i - 1 by omega)
              linarith
    · obtain ⟨x, b⟩ := (⟨x, b⟩ : ℚ × Bool)
      simp only at hc h2
      subst h2
      left
      exact ⟨rfl, Or.inl ⟨GlobalTheory.SignedHC.GridData.mem_parPi.2 (Or.inr (Or.inl ⟨hc, rfl⟩)), lowj _ (cl _ hc)⟩⟩
    · simp only at hb h2
      subst h2
      rw [hm, e2] at hl1
      rw [hm] at hl2
      left
      refine ⟨rfl, ?_⟩
      rcases eq_or_lt_of_le hl1 with h | h
      · subst h
        exact Or.inr (Or.inl (block_sym.2 hb))
      · refine Or.inl ⟨GlobalTheory.SignedHC.GridData.mem_parPi.2 (Or.inr (Or.inr ⟨l, by rw [hm]; omega, by rw [hm]; exact hl2, hb, rfl⟩)), ?_⟩
        exact lowj _ (blockC'_le D τ (by omega) hl2 hb)
  · rintro (⟨rfl, (⟨h, hx⟩ | h | h)⟩ | ⟨rfl, h, hx⟩)
    · rcases GlobalTheory.SignedHC.GridData.mem_parPi.1 h with ⟨l, hl, he⟩ | ⟨hc, _⟩ | ⟨l, hl1, hl2, hb, _⟩
      · simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, -⟩ := he
        have := below l hx
        exact GlobalTheory.SignedHC.GridData.mem_parPi.2 (Or.inl ⟨l, hl, by rw [hm] at hl ⊢; simp; omega⟩)
      · exact GlobalTheory.SignedHC.GridData.mem_parPi.2 (Or.inr (Or.inl ⟨hc, rfl⟩))
      · rw [hm] at hl1 hl2
        exact GlobalTheory.SignedHC.GridData.mem_parPi.2 (Or.inr (Or.inr ⟨l, by rw [hm]; omega, by rw [hm]; exact hl2, hb, rfl⟩))
    · exact GlobalTheory.SignedHC.GridData.mem_parPi.2 (Or.inr (Or.inr ⟨D.R.m - i, by rw [hm]; omega, by rw [hm]; omega,
        block_sym.1 h, rfl⟩))
    · rcases GlobalTheory.SignedHC.GridData.mem_parPi.1 h with ⟨l, hl, he⟩ | ⟨hc, h2⟩ | ⟨l, hl1, hl2, hb, h2⟩
      · simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, he⟩ := he
        rw [hm] at hl he
        have h1 : ¬ (D.R.m - i ≤ l) := by intro h'; simp [h'] at he
        have h2 : ¬ Even (D.R.m - i - l) := by intro h'; simp [h'] at he
        refine GlobalTheory.SignedHC.GridData.mem_parPi.2 (Or.inl ⟨l, hl, ?_⟩)
        rw [hm, e1]
        by_cases hl1 : l = D.R.m - i - 1
        · simp [hl1]
        · have hpar : D.R.m - i - l = (D.R.m - i - 1 - l) + 1 := by omega
          rw [hpar, Nat.even_add_one, not_not] at h2
          simp [h2]
      · simp at h2
      · simp at h2
    · rcases GlobalTheory.SignedHC.GridData.mem_parPi.1 h with ⟨l, hl, he⟩ | ⟨hc, h2⟩ | ⟨l, hl1, hl2, hb, h2⟩
      · simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, he⟩ := he
        rw [hm] at hl he
        have hl' := above l hx
        have h1 : ¬ (D.R.m - i ≤ l) := by omega
        have h2 : Even (D.R.m - i - l) := by
          by_contra h'; simp [h1, h'] at he
        refine GlobalTheory.SignedHC.GridData.mem_parPi.2 (Or.inl ⟨l, hl, ?_⟩)
        rw [hm, e1]
        have hl1 : ¬ (D.R.m - i - 1 ≤ l) := by
          intro h'
          have : D.R.m - i - l = 1 := by omega
          rw [this] at h2; exact absurd h2 (by decide)
        have hpar : D.R.m - i - l = (D.R.m - i - 1 - l) + 1 := by omega
        rw [hpar, Nat.even_add_one] at h2
        simp [hl1, h2]
      · exfalso; have := lowj _ (cl _ hc); linarith
      · rw [hm] at hl1 hl2
        exfalso; have := lowj _ (blockC'_le D τ (by omega) hl2 hb); linarith

end GlobalTheory.NegPair

namespace GlobalTheory.NegPair
open GlobalTheory.Grid

theorem sLen_odd (D : D7) : ∃ q : ℕ, GlobalTheory.Grid.sLen D = 2 * q + 7 := by
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  have := D.R.two_le_m
  refine ⟨a + b - 1, ?_⟩
  unfold GlobalTheory.Grid.sLen Formalism.BasicNotions.Ranks.r
  omega

theorem half_int (D : D7) (τ : D.what₂.Tau) {i : ℕ} {p : ℚ × Bool} (hp : p ∈ (GlobalTheory.Grid.grid D τ).parPi i) :
    ∃ z : ℤ, p.1 = z + 1 / 2 := by
  rcases GlobalTheory.SignedHC.GridData.mem_parPi.1 hp with ⟨l, hl, rfl⟩ | ⟨hc, _⟩ | ⟨l, hl1, hl2, hb, _⟩
  · refine ⟨(GlobalTheory.Grid.grid D τ).v 2 + (((GlobalTheory.Grid.grid D τ).m : ℤ) + 1 - l) * (GlobalTheory.Grid.grid D τ).ga, ?_⟩
    dsimp only
    unfold GlobalTheory.SignedHC.GridData.a
    push_cast; ring
  · obtain ⟨i', -, -, he⟩ := GlobalTheory.SignedHC.GridData.mem_cloudHalf.1 hc
    refine ⟨(GlobalTheory.Grid.grid D τ).v i' - 1, ?_⟩
    rw [he]; unfold GlobalTheory.SignedHC.GridData.vHalf; push_cast; ring
  · obtain ⟨q, hq⟩ := sLen_odd D
    obtain ⟨a', -, he⟩ := Finset.mem_image.1 hb
    refine ⟨GlobalTheory.Grid.cen D τ l + q + 2 - a', ?_⟩
    rw [← he]
    change ((GlobalTheory.Grid.cen D τ l : ℤ) : ℚ) + (((GlobalTheory.Grid.sLen D - 1 : ℕ) : ℚ) - 1) / 2 - a' = _
    rw [sLen_sub_one, hq]; push_cast; ring

theorem high (D : D7) (τ : D.what₂.Tau) {i : ℕ} (hi : i < D.R.m) {p : ℚ × Bool} (hp : p ∈ (GlobalTheory.Grid.grid D τ).parPi i)
    (hc : ((GlobalTheory.Grid.cen D τ (D.R.m - i) : ℤ) : ℚ) < p.1) : ∃ l < D.R.m - i, p.1 = (GlobalTheory.Grid.grid D τ).a l ∧ p.2 = decide (Even (D.R.m - i - l)) ∧
      (GlobalTheory.Grid.grid D τ).a (D.R.m - i) + (GlobalTheory.Grid.gap D : ℚ) ≤ p.1 := by
  have hg := gapQ D
  have hs : (6 : ℚ) ≤ GlobalTheory.Grid.sLen D := by exact_mod_cast sLen_ge D
  have hN : (0 : ℚ) ≤ (GlobalTheory.Grid.bigN D : ℚ) ^ 3 := by positivity
  obtain ⟨hcl, hcu, hj1⟩ := cen_bounds D τ hi
  rcases loc D τ hi hp with ⟨h1, _⟩ | ⟨l, hl, h1, h2⟩
  · exfalso; linarith
  · refine ⟨l, hl, h1, h2, ?_⟩
    rw [h1]; exact (a_add_le D τ hl)

theorem low (D : D7) (τ : D.what₂.Tau) {i : ℕ} (hi : i < D.R.m) {p : ℚ × Bool} (hp : p ∈ (GlobalTheory.Grid.grid D τ).parPi i)
    (hc : p.1 < ((GlobalTheory.Grid.cen D τ (D.R.m - i) : ℤ) : ℚ)) : p.1 ≤ (GlobalTheory.Grid.grid D τ).a (D.R.m - i) ∧ p.2 = true := by
  have hg := gapQ D
  have hs : (6 : ℚ) ≤ GlobalTheory.Grid.sLen D := by exact_mod_cast sLen_ge D
  have hN : (0 : ℚ) ≤ (GlobalTheory.Grid.bigN D : ℚ) ^ 3 := by positivity
  obtain ⟨hcl, hcu, hj1⟩ := cen_bounds D τ hi
  rcases loc D τ hi hp with h | ⟨l, hl, h1, h2⟩
  · exact h
  · exfalso
    have := a_add_le D τ hl
    linarith

theorem far (D : D7) (τ : D.what₂.Tau) {i : ℕ} (hi : i < D.R.m) {p : ℚ × Bool} (hp : p ∈ (GlobalTheory.Grid.grid D τ).parPi i) :
    (GlobalTheory.Grid.gap D : ℚ) / 2 - 1 ≤ |((GlobalTheory.Grid.cen D τ (D.R.m - i) : ℤ) : ℚ) - p.1| := by
  have hg := gapQ D
  have hs : (6 : ℚ) ≤ GlobalTheory.Grid.sLen D := by exact_mod_cast sLen_ge D
  have hN : (0 : ℚ) ≤ (GlobalTheory.Grid.bigN D : ℚ) ^ 3 := by positivity
  obtain ⟨hcl, hcu, hj1⟩ := cen_bounds D τ hi
  rcases loc D τ hi hp with ⟨h1, _⟩ | ⟨l, hl, h1, h2⟩
  · rw [abs_of_nonneg (by linarith)]; linarith
  · have := a_add_le D τ hl
    rw [abs_of_nonpos (by linarith)]; linarith

theorem sep (D : D7) (τ : D.what₂.Tau) {i : ℕ} (hi : i < D.R.m) {x x' : ℚ} (hx : (x, true) ∈ (GlobalTheory.Grid.grid D τ).parPi i)
    (hx' : (x', false) ∈ (GlobalTheory.Grid.grid D τ).parPi i) : (GlobalTheory.Grid.gap D : ℚ) ≤ |x - x'| := by
  rcases loc D τ hi hx' with ⟨-, h⟩ | ⟨l', hl', h1', h2'⟩
  · simp at h
  · simp only at h1' h2'
    rcases loc D τ hi hx with ⟨h1, -⟩ | ⟨l, hl, h1, h2⟩
    · have := a_add_le D τ hl'
      simp only at h1
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
    · simp only at h1 h2
      have hne : l ≠ l' := by
        rintro rfl
        rw [← h2'] at h2
        exact absurd h2 (by decide)
      rcases lt_or_gt_of_ne hne with h | h
      · have := a_add_le D τ h
        rw [abs_of_nonneg (by linarith)]; linarith
      · have := a_add_le D τ h
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith

theorem card_three (S : SPar) (c : ℚ) :
    (lowS S c).card + (highS S c).card + (negS S c).card ≤ S.card := by
  have h1 := Finset.card_image_le (s := S.filter fun p => p.2 = true ∧ p.1 < c) (f := fun p => c - p.1)
  have h2 := Finset.card_image_le (s := S.filter fun p => p.2 = true ∧ c < p.1) (f := fun p => c - p.1)
  have h3 := Finset.card_image_le (s := S.filter fun p => p.2 = false) (f := fun p => c - p.1)
  have h4 : (S.filter fun p => p.2 = true ∧ p.1 < c).card + (S.filter fun p => p.2 = true ∧ c < p.1).card +
      (S.filter fun p => p.2 = false).card ≤ S.card := by
    rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    calc _ ≤ ∑ _p ∈ S, 1 := Finset.sum_le_sum fun p _ => by
            rcases p with ⟨x, b⟩
            cases b
            · simp
            · by_cases h : x < c <;> by_cases h' : c < x <;> simp [h, h'] <;> linarith
      _ = S.card := by simp
  unfold lowS highS negS
  omega

theorem card_parPi (D : D7) (τ : D.what₂.Tau) (i : ℕ) :
    ((GlobalTheory.Grid.grid D τ).parPi i).card ≤ D.R.m + D.R.k + i * (GlobalTheory.Grid.sLen D - 1) := by
  have hm : (GlobalTheory.Grid.grid D τ).m = D.R.m := rfl
  have hk : (GlobalTheory.Grid.grid D τ).k = D.R.k := rfl
  unfold GlobalTheory.SignedHC.GridData.parPi GlobalTheory.SignedHC.plus
  rw [hm]
  refine (Finset.card_union_le _ _).trans ?_
  refine (Nat.add_le_add_right (Finset.card_union_le _ _) _).trans ?_
  have h1 := (Finset.card_image_le (s := Finset.range (D.R.m + 1))
    (f := fun l => ((GlobalTheory.Grid.grid D τ).a l, decide (D.R.m - i ≤ l ∨
      Even (D.R.m - i - l))))).trans (Finset.card_range _).le
  have h2 := (Finset.card_image_le (s := (GlobalTheory.Grid.grid D τ).cloudHalf) (f := fun x => (x, true))).trans
    ((Finset.card_image_le (s := Finset.Icc 2 (GlobalTheory.Grid.grid D τ).k)).trans (Nat.card_Icc 2 _).le)
  have h3 := (Finset.card_image_le
    (s := (Finset.Icc (D.R.m - i + 1) D.R.m).biUnion (GlobalTheory.Grid.grid D τ).blockC')
    (f := fun x => (x, true))).trans ((Finset.card_biUnion_le).trans (Finset.sum_le_sum
      (g := fun _ => GlobalTheory.Grid.sLen D - 1) fun l _ =>
        (Finset.card_image_le).trans (Finset.card_range _).le))
  rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul] at h3
  rw [hk] at h2
  have h4 : (D.R.m + 1 - (D.R.m - i + 1)) * (GlobalTheory.Grid.sLen D - 1) ≤ i * (GlobalTheory.Grid.sLen D - 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have := D.R.m_add_three_le_k
  omega

end GlobalTheory.NegPair

namespace GlobalTheory.NegPair
open GlobalTheory.Grid

theorem gapGt_ofBlocks {p q : ℕ} {l₁ l₂ : List ℚ} {h : ℝ} (hp : p ≤ l₁.length) (hq : q ≤ l₂.length)
    (H : ∀ y ∈ l₁, ∀ y' ∈ l₂, h < |((y - y' : ℚ) : ℝ)|) :
    Formalism.BasicNotions.TH.GapGt (Formalism.BasicNotions.TH.ofBlocks l₁ l₂ : Formalism.BasicNotions.TH.Ix p q → ℚ) h := by
  rintro (a | a) (b | b) hab
  · exact (hab trivial).elim
  · simp only [Formalism.BasicNotions.TH.ofBlocks]
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    exact H _ (List.getElem_mem _) _ (List.getElem_mem _)
  · simp only [Formalism.BasicNotions.TH.ofBlocks]
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    have := H _ (List.getElem_mem (l := l₁) (n := (b : ℕ)) (by omega)) _ (List.getElem_mem (l := l₂) (n := (a : ℕ)) (by omega))
    push_cast at this ⊢
    rwa [abs_sub_comm]
  · exact (hab trivial).elim

theorem gapGe_ofBlocks {p q : ℕ} {l₁ l₂ : List ℚ} {h : ℝ} (hp : p ≤ l₁.length) (hq : q ≤ l₂.length)
    (H : ∀ y ∈ l₁, ∀ y' ∈ l₂, h ≤ |((y - y' : ℚ) : ℝ)|) :
    Formalism.BasicNotions.TH.GapGe (Formalism.BasicNotions.TH.ofBlocks l₁ l₂ : Formalism.BasicNotions.TH.Ix p q → ℚ) h := by
  rintro (a | a) (b | b) hab
  · exact (hab trivial).elim
  · simp only [Formalism.BasicNotions.TH.ofBlocks]
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    exact H _ (List.getElem_mem _) _ (List.getElem_mem _)
  · simp only [Formalism.BasicNotions.TH.ofBlocks]
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    have := H _ (List.getElem_mem (l := l₁) (n := (b : ℕ)) (by omega)) _ (List.getElem_mem (l := l₂) (n := (a : ℕ)) (by omega))
    push_cast at this ⊢
    rwa [abs_sub_comm]
  · exact (hab trivial).elim

theorem abs_le_of_mem_block {y : ℚ} {len : ℕ} (h : y ∈ block len) : |y| ≤ ((len : ℚ) - 1) / 2 := by
  unfold block at h
  simp at h
  obtain ⟨a', ha, rfl⟩ := h
  have : (a' : ℚ) + 1 ≤ len := by exact_mod_cast ha
  have h0 : (0 : ℚ) ≤ a' := Nat.cast_nonneg a'
  rw [abs_le]; constructor <;> linarith

theorem coef_le (D : D7) {n q0 : ℕ} (hn : n ≤ GlobalTheory.Grid.bigN D) (hq : q0 ≤ D.R.m) :
    120 * (n : ℝ) * (q0 : ℝ) ^ ((3 : ℝ) / 2) ≤ 2 * (GlobalTheory.Grid.bigN D : ℝ) ^ 3 := by
  have h12 : 12 * D.R.m ≤ GlobalTheory.Grid.bigN D := by
    have ht := D.R.rank_add_five_le
    have hs := sLen_ge D
    unfold GlobalTheory.Grid.bigN
    have : D.R.m * 12 ≤ D.R.m * (D.R.t + GlobalTheory.Grid.sLen D + 1) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hq2 : (q0 : ℝ) ^ ((3 : ℝ) / 2) ≤ (q0 : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos q0 with h | h
    · subst h; rw [Nat.cast_zero, Real.zero_rpow (by norm_num)]; positivity
    · have : (1 : ℝ) ≤ q0 := by exact_mod_cast h
      calc (q0 : ℝ) ^ ((3 : ℝ) / 2) ≤ (q0 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le this (by norm_num)
        _ = (q0 : ℝ) ^ 2 := Real.rpow_two _
  have hnR : (n : ℝ) ≤ GlobalTheory.Grid.bigN D := by exact_mod_cast hn
  have hqR : (q0 : ℝ) ≤ D.R.m := by exact_mod_cast hq
  have h12R : 12 * (D.R.m : ℝ) ≤ GlobalTheory.Grid.bigN D := by exact_mod_cast h12
  have hq0 : (0 : ℝ) ≤ q0 := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have hqq : (q0 : ℝ) ^ 2 * 144 ≤ (GlobalTheory.Grid.bigN D : ℝ) ^ 2 := by nlinarith
  have hp : (0 : ℝ) ≤ (q0 : ℝ) ^ ((3 : ℝ) / 2) := by positivity
  have hN0 : (0 : ℝ) ≤ GlobalTheory.Grid.bigN D := by positivity
  calc 120 * (n : ℝ) * (q0 : ℝ) ^ ((3 : ℝ) / 2) ≤ 120 * (GlobalTheory.Grid.bigN D : ℝ) * (q0 : ℝ) ^ 2 := by
        gcongr
    _ ≤ 2 * (GlobalTheory.Grid.bigN D : ℝ) ^ 3 := by nlinarith

theorem card_negS (D : D7) (τ : D.what₂.Tau) {i : ℕ} (hi : i < D.R.m) :
    (negS ((GlobalTheory.Grid.grid D τ).parPi i) ((GlobalTheory.Grid.cen D τ (D.R.m - i) : ℤ) : ℚ)).card ≤ D.R.m - i := by
  have hsub : negS ((GlobalTheory.Grid.grid D τ).parPi i) ((GlobalTheory.Grid.cen D τ (D.R.m - i) : ℤ) : ℚ) ⊆
      (Finset.range (D.R.m - i)).image fun l => ((GlobalTheory.Grid.cen D τ (D.R.m - i) : ℤ) : ℚ) - (GlobalTheory.Grid.grid D τ).a l := by
    intro y hy
    rw [mem_negS] at hy
    rcases loc D τ hi hy with ⟨-, h⟩ | ⟨l, hl, h1, -⟩
    · simp at h
    · exact Finset.mem_image.2 ⟨l, Finset.mem_range.2 hl, by simp only at h1; linarith⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (Finset.card_range _).le)

end GlobalTheory.NegPair

namespace GlobalTheory.NegPair
open GlobalTheory.Grid

theorem params : ∀ (D : D7) (i : ℕ), i < D.R.m → ∀ τ : D.what₂.Tau, ∃ al be ga de : List ℚ,
    Formalism.MainNotions.SchurIrreducible.DataAR (GlobalTheory.Grid.sLen D - 1) al be ga de ∧
    GlobalTheory.Grid.parP D i τ = dualPar (signed (al ++ be) (ga ++ de) (-(GlobalTheory.Grid.cen D τ (D.R.m - i) : ℚ))) ∧
    GlobalTheory.Grid.parP D (i + 1) τ =
      dualPar (signed (al ++ block (GlobalTheory.Grid.sLen D - 1) ++ de) (ga ++ be) (-(GlobalTheory.Grid.cen D τ (D.R.m - i) : ℚ))) := by
  intro D i hi τ
  have hg := gapQ D
  have hs : (6 : ℚ) ≤ GlobalTheory.Grid.sLen D := by exact_mod_cast sLen_ge D
  have hN : (0 : ℚ) ≤ (GlobalTheory.Grid.bigN D : ℚ) ^ 3 := by positivity
  obtain ⟨hcl, hcu, hj1⟩ := cen_bounds D τ hi
  obtain ⟨q, hq⟩ := sLen_odd D
  have hne : ∀ p ∈ (GlobalTheory.Grid.grid D τ).parPi i, p.1 ≠ ((GlobalTheory.Grid.cen D τ (D.R.m - i) : ℤ) : ℚ) := fun p hp h => by
    have := far D τ hi hp
    rw [h, sub_self, abs_zero] at this
    linarith
  refine ⟨desc (lowS ((GlobalTheory.Grid.grid D τ).parPi i) ((GlobalTheory.Grid.cen D τ (D.R.m - i) : ℤ) : ℚ)),
    desc (highS ((GlobalTheory.Grid.grid D τ).parPi i) ((GlobalTheory.Grid.cen D τ (D.R.m - i) : ℤ) : ℚ)), [],
    desc (negS ((GlobalTheory.Grid.grid D τ).parPi i) ((GlobalTheory.Grid.cen D τ (D.R.m - i) : ℤ) : ℚ)), ?_,
    (recon_left _ _ hne).symm, (recon_right _ _ _ _ (mem_next D τ hi)).symm⟩
  set S := (GlobalTheory.Grid.grid D τ).parPi i with hS
  set c : ℚ := ((GlobalTheory.Grid.cen D τ (D.R.m - i) : ℤ) : ℚ) with hc

  have hlen : (desc (lowS S c)).length + (desc (highS S c)).length + ([] : List ℚ).length +
      (desc (negS S c)).length + (GlobalTheory.Grid.sLen D - 1) ≤ GlobalTheory.Grid.bigN D := by
    simp only [desc_length, List.length_nil, add_zero]
    have h1 := card_three S c
    have h2 : S.card ≤ D.R.m + D.R.k + i * (GlobalTheory.Grid.sLen D - 1) := card_parPi D τ i
    have h3 : i * (GlobalTheory.Grid.sLen D - 1) + (GlobalTheory.Grid.sLen D - 1) ≤ D.R.m * (GlobalTheory.Grid.sLen D - 1) := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi
    have h4 : D.R.m * (GlobalTheory.Grid.sLen D - 1) + D.R.m ≤ D.R.m * (D.R.t + GlobalTheory.Grid.sLen D + 1) := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
    unfold GlobalTheory.Grid.bigN
    omega
  have hM : ∀ M : ℕ, M ≤ GlobalTheory.Grid.bigN D → (M : ℚ) ^ 3 < (GlobalTheory.Grid.gap D : ℚ) / 2 - (GlobalTheory.Grid.sLen D : ℚ) / 2 := by
    intro M hMN
    have : (M : ℚ) ^ 3 ≤ (GlobalTheory.Grid.bigN D : ℚ) ^ 3 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hMN) 3
    linarith

  have hplus : ∀ y ∈ desc (lowS S c) ++ desc (highS S c), (c - y, true) ∈ S := by
    intro y hy
    simp only [List.mem_append, mem_desc, mem_lowS, mem_highS] at hy
    rcases hy with ⟨h, _⟩ | ⟨h, _⟩ <;> exact h
  have hminus : ∀ y ∈ [] ++ desc (negS S c), (c - y, false) ∈ S := by
    intro y hy
    simp only [List.nil_append, mem_desc, mem_negS] at hy
    exact hy
  have hent : ∀ y ∈ desc (lowS S c) ++ desc (highS S c) ++ [] ++ desc (negS S c), ∃ b, (c - y, b) ∈ S := by
    intro y hy
    rw [List.append_assoc] at hy
    rcases List.mem_append.1 hy with h | h
    · exact ⟨_, hplus y h⟩
    · exact ⟨_, hminus y h⟩
  have hsep : ∀ y ∈ desc (lowS S c) ++ desc (highS S c), ∀ y' ∈ [] ++ desc (negS S c),
      (GlobalTheory.Grid.gap D : ℚ) ≤ |y - y'| := by
    intro y hy y' hy'
    have := sep D τ hi (hplus y hy) (hminus y' hy')
    rwa [show c - y - (c - y') = y' - y by ring, abs_sub_comm] at this
  refine ⟨⟨?_, ?_, desc_pairwise _, desc_pairwise _, List.Pairwise.nil, desc_pairwise _, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · have := sLen_ge D; omega
  · have hv : (GlobalTheory.Grid.grid D τ).vHalf 2 ∈ (GlobalTheory.Grid.grid D τ).cloudHalf :=
      GlobalTheory.SignedHC.GridData.mem_cloudHalf.2 ⟨2, le_rfl, (GlobalTheory.Grid.grid D τ).two_le_k, rfl⟩
    have hvS : ((GlobalTheory.Grid.grid D τ).vHalf 2, true) ∈ S :=
      GlobalTheory.SignedHC.GridData.mem_parPi.2 (Or.inr (Or.inl ⟨hv, rfl⟩))
    have h1 := cloudHalf_lt D τ hv
    have h3 := a_le_a D τ (show D.R.m - i ≤ D.R.m by omega)
    have hmem : c - (GlobalTheory.Grid.grid D τ).vHalf 2 ∈ lowS S c :=
      mem_lowS.2 ⟨by rwa [sub_sub_cancel], by
        have : (0 : ℚ) ≤ GlobalTheory.Grid.gap D := Nat.cast_nonneg _
        linarith⟩
    have := Finset.card_pos.2 ⟨_, hmem⟩
    simp only [desc_length, List.length_nil]
    omega
  ·
    have nd : ∀ T, (desc T).Nodup := fun T => (desc_pairwise T).imp fun h => h.ne'
    rw [List.append_nil]
    refine List.Nodup.append (List.Nodup.append (nd _) (nd _) ?_) (nd _) ?_
    · intro y h1 h2
      rw [mem_desc, mem_lowS] at h1
      rw [mem_desc, mem_highS] at h2
      linarith [h1.2, h2.2]
    · intro y h1 h2
      have := hsep y h1 y (by simpa using h2)
      rw [sub_self, abs_zero] at this
      have : (0 : ℚ) ≤ GlobalTheory.Grid.gap D := Nat.cast_nonneg _
      linarith
  · intro e he
    rw [List.append_nil, mem_desc, mem_lowS] at he
    linarith [he.2]
  · intro e he
    rcases List.mem_append.1 he with h | h
    · rw [mem_desc, mem_highS] at h
      linarith [h.2]
    · rw [mem_desc, mem_negS] at h
      rcases lt_or_gt_of_ne (hne _ h) with h' | h'
      · have := (low D τ hi h h').2
        simp at this
      · simp only at h'
        linarith
  · intro e he
    obtain ⟨b, hb⟩ := hent e he
    obtain ⟨z, hz⟩ := half_int D τ hb
    simp only at hz
    refine ⟨GlobalTheory.Grid.cen D τ (D.R.m - i) - z - q - 4, ?_⟩
    rw [sLen_sub_one, hq]
    push_cast
    rw [hc] at hz
    linarith
  · intro e he
    obtain ⟨b, hb⟩ := hent e he
    have := far D τ hi hb
    rw [← hc, sub_sub_cancel] at this
    rw [sLen_sub_one]
    linarith
  ·
    apply gapGt_ofBlocks (by simp) (by simp)
    intro y hy y' hy'
    have h1 := hsep y hy y' hy'
    have h2 := hM _ hlen
    have h3 : ((((desc (lowS S c)).length + (desc (highS S c)).length + ([] : List ℚ).length +
        (desc (negS S c)).length + (GlobalTheory.Grid.sLen D - 1) : ℕ) : ℚ)) ^ 3 < |y - y'| := by linarith
    exact_mod_cast h3
  ·
    apply gapGt_ofBlocks (by simp [block]; omega) (by simp)
    intro y hy y' hy'
    have h2 := hM _ hlen
    suffices h : (GlobalTheory.Grid.gap D : ℚ) / 2 - (GlobalTheory.Grid.sLen D : ℚ) / 2 ≤ |y - y'| by
      have h3 : ((((desc (lowS S c)).length + (desc (highS S c)).length + ([] : List ℚ).length +
          (desc (negS S c)).length + (GlobalTheory.Grid.sLen D - 1) : ℕ) : ℚ)) ^ 3 < |y - y'| := by linarith
      exact_mod_cast h3
    rw [List.nil_append, mem_desc, mem_highS] at hy'
    obtain ⟨l, hl, -, -, hal⟩ := high D τ hi hy'.1 hy'.2
    simp only at hal
    rcases List.mem_append.1 hy with h | h
    · rcases List.mem_append.1 h with h | h
      · rw [mem_desc, mem_lowS] at h
        have := (low D τ hi h.1 h.2).1
        simp only at this
        rw [abs_of_nonneg (by linarith)]
        linarith
      · have := abs_le_of_mem_block h
        rw [sLen_sub_one] at this
        rw [abs_le] at this
        rw [abs_of_nonneg (by linarith)]
        linarith
    · rw [mem_desc, mem_negS] at h
      have := sep D τ hi hy'.1 h
      rw [show c - y' - (c - y) = y - y' by ring] at this
      linarith
  ·
    apply gapGe_ofBlocks (by simp) (by simp)
    intro y hy y' hy'
    have h1 := hsep y hy y' hy'
    have hc1 := coef_le D (n := (desc (lowS S c)).length + (desc (highS S c)).length + ([] : List ℚ).length +
        (desc (negS S c)).length)
      (q0 := min ((desc (lowS S c)).length + (desc (highS S c)).length) (([] : List ℚ).length + (desc (negS S c)).length))
      (by omega) (by
        have : (negS S c).card ≤ D.R.m - i := card_negS D τ hi
        simp only [desc_length, List.length_nil, zero_add]
        omega)
    have h2 : ((GlobalTheory.Grid.bigN D : ℚ) : ℝ) ^ 3 * 2 < ((GlobalTheory.Grid.gap D : ℚ) : ℝ) := by
      have : (GlobalTheory.Grid.bigN D : ℚ) ^ 3 * 2 < (GlobalTheory.Grid.gap D : ℚ) := by linarith
      exact_mod_cast this
    have h3 : (((GlobalTheory.Grid.gap D : ℚ)) : ℝ) ≤ |((y - y' : ℚ) : ℝ)| := by
      rw [← Rat.cast_abs]; exact_mod_cast h1
    push_cast at h2 h3 hc1 ⊢
    linarith

end GlobalTheory.NegPair
