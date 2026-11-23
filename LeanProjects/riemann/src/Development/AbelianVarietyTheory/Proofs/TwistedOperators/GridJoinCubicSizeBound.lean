import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientThetaParamsRemoveBlockArrow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfExpIffHasInfQ
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridDataAtRealPlaceNegFirstLowEndLtCloud
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin.ArrXPar

open GlobalTheory.SignedHC GlobalTheory.RemoveBlock GlobalTheory.PairLift GlobalTheory.Chain

theorem mem_signed {l₁ l₂ : List ℚ} {c : ℚ} {x : ℚ × Bool} :
    x ∈ signed l₁ l₂ c ↔ (x.2 = true ∧ x.1 - c ∈ l₁) ∨ (x.2 = false ∧ x.1 - c ∈ l₂) := by
  obtain ⟨a, s⟩ := x
  simp only [signed, Finset.mem_union, List.mem_toFinset, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro (⟨y, hy, rfl, rfl⟩ | ⟨y, hy, rfl, rfl⟩)
    · left; simpa using hy
    · right; simpa using hy
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
    · left; exact ⟨_, h, by ring, rfl⟩
    · right; exact ⟨_, h, by ring, rfl⟩

theorem gapGt_ofBlocks {p q : ℕ} {l₁ l₂ : List ℚ} (hp : l₁.length = p) (hq : l₂.length = q) {h : ℝ}
    (H : ∀ x ∈ l₁, ∀ y ∈ l₂, h < |((x - y : ℚ) : ℝ)|) : GapGt (ofBlocks l₁ l₂ : Ix p q → ℚ) h := by
  subst hp hq
  rintro (a | a) (b | b) hab
  · exact (hab trivial).elim
  · simp only [ofBlocks, List.getD_eq_getElem _ _ a.2, List.getD_eq_getElem _ _ b.2]
    exact H _ (List.getElem_mem _) _ (List.getElem_mem _)
  · simp only [ofBlocks, List.getD_eq_getElem _ _ a.2, List.getD_eq_getElem _ _ b.2]
    rw [← neg_sub, Rat.cast_neg, abs_neg]
    exact H _ (List.getElem_mem _) _ (List.getElem_mem _)
  · exact (hab trivial).elim

theorem gapGe_ofBlocks {p q : ℕ} {l₁ l₂ : List ℚ} (hp : l₁.length = p) (hq : l₂.length = q) {h : ℝ}
    (H : ∀ x ∈ l₁, ∀ y ∈ l₂, h ≤ |((x - y : ℚ) : ℝ)|) : GapGe (ofBlocks l₁ l₂ : Ix p q → ℚ) h := by
  subst hp hq
  rintro (a | a) (b | b) hab
  · exact (hab trivial).elim
  · simp only [ofBlocks, List.getD_eq_getElem _ _ a.2, List.getD_eq_getElem _ _ b.2]
    exact H _ (List.getElem_mem _) _ (List.getElem_mem _)
  · simp only [ofBlocks, List.getD_eq_getElem _ _ a.2, List.getD_eq_getElem _ _ b.2]
    rw [← neg_sub, Rat.cast_neg, abs_neg]
    exact H _ (List.getElem_mem _) _ (List.getElem_mem _)
  · exact (hab trivial).elim

end GlobalTheory.GridJoin.ArrXPar

namespace GlobalTheory.GridJoin.ArrXPar

open GlobalTheory.SignedHC GlobalTheory.RemoveBlock GlobalTheory.PairLift GlobalTheory.Chain GlobalTheory.Grid

theorem att_succ (c : ℚ) (D : D7) (i j : ℕ) :
    att c (rkV D (i + 1) j) = c + (if Odd (i + j) then -(1 / 2) else 0) ∧
      att c (rkV D i j) = c + (if Odd (i + 1 + j) then -(1 / 2) else 0) := by
  have e : i + 1 + j = i + j + 1 := by ring
  unfold att
  simp only [odd_rkV, e, Nat.odd_add_one]
  by_cases h : Odd (i + j) <;> simp [h] <;> ring

theorem nat_cube_le {a R : ℕ} (h : a ≤ R) : ((a : ℕ) : ℚ) ^ 3 ≤ (R : ℚ) ^ 3 :=
  pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast h) 3

theorem gridJoin_cubic_size_bound {n mm N : ℕ} (hn : n ≤ N) (hmm : 2 * mm ≤ N) (hN : 1800 ≤ N) :
    120 * (n : ℝ) * (mm : ℝ) ^ ((3 : ℝ) / 2) ≤ 2 * (N : ℝ) ^ 3 := by
  have hn' : (n : ℝ) ≤ N := by exact_mod_cast hn
  have hm' : 2 * (mm : ℝ) ≤ N := by exact_mod_cast hmm
  have hN' : (1800 : ℝ) ≤ N := by exact_mod_cast hN
  have hm0 : (0 : ℝ) ≤ mm := Nat.cast_nonneg _
  have e : (mm : ℝ) ^ ((3 : ℝ) / 2) = mm * √(mm : ℝ) := by
    rw [Real.sqrt_eq_rpow, show ((3 : ℝ) / 2) = 1 + 1 / 2 by norm_num, Real.rpow_add' hm0 (by norm_num), Real.rpow_one]
  have hs : √(mm : ℝ) ≤ N / 30 := Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩
  have hm2 : (mm : ℝ) ≤ N / 2 := by linarith
  rw [e]
  calc 120 * (n : ℝ) * (mm * √(mm : ℝ)) ≤ 120 * (N : ℝ) * ((N / 2) * (N / 30)) := by gcongr
    _ = 2 * (N : ℝ) ^ 3 := by ring

theorem par_pair (D : D7) (hN : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D) (τ : D.what₂.Tau) (i j : ℕ)
    (hi : i < D.R.m) (hj : j ≤ D.R.m) : ∃ be de : List ℚ, Formalism.MainNotions.SchurIrreducible.DataARm (GlobalTheory.Grid.sLen D) [] be [] de ∧
      (parV D (i + 1) j τ).image (fun x => (x.1, !x.2)) =
        dualPar (signed de (Formalism.BasicNotions.TH.block (GlobalTheory.Grid.sLen D) ++ be) (att (cen D τ (D.R.m - i) : ℚ) (rkV D i j))) ∧
      parV D i j τ = dualPar (signed be de (att (cen D τ (D.R.m - i) : ℚ) (rkV D (i + 1) j))) := by
  set c : ℚ := (cen D τ (D.R.m - i) : ℚ) with hc
  set P := (grid D τ).parD i j with hP
  obtain ⟨hS, hT⟩ := att_succ c D i j
  rw [hS, hT]
  set δ : ℚ := if Odd (i + j) then -(1 / 2) else 0 with hδ
  set δ' : ℚ := if Odd (i + 1 + j) then -(1 / 2) else 0 with hδ'
  set Pp : Finset ℚ := (P.filter fun x => x.2 = true).image Prod.fst with hPp
  set Pm : Finset ℚ := (P.filter fun x => x.2 = false).image Prod.fst with hPm
  have mPp : ∀ y, y ∈ Pp ↔ (y, true) ∈ P := by
    intro y; simp only [hPp, Finset.mem_image, Finset.mem_filter]
    exact ⟨fun ⟨x, ⟨h1, h2⟩, h3⟩ => by rw [← h3, ← h2]; exact h1, fun h => ⟨_, ⟨h, rfl⟩, rfl⟩⟩
  have mPm : ∀ y, y ∈ Pm ↔ (y, false) ∈ P := by
    intro y; simp only [hPm, Finset.mem_image, Finset.mem_filter]
    exact ⟨fun ⟨x, ⟨h1, h2⟩, h3⟩ => by rw [← h3, ← h2]; exact h1, fun h => ⟨_, ⟨h, rfl⟩, rfl⟩⟩
  set be := (descList Pp).map (· - c) with hbe
  set de := (descList Pm).map (· - c) with hde
  have mbe : ∀ e, e ∈ be ↔ (e + c, true) ∈ P := by
    intro e; rw [hbe, List.mem_map, ← mPp]
    exact ⟨fun ⟨y, hy, h⟩ => by rw [← h, sub_add_cancel]; exact mem_descList.1 hy,
      fun h => ⟨_, mem_descList.2 h, by ring⟩⟩
  have mde : ∀ e, e ∈ de ↔ (e + c, false) ∈ P := by
    intro e; rw [hde, List.mem_map, ← mPm]
    exact ⟨fun ⟨y, hy, h⟩ => by rw [← h, sub_add_cancel]; exact mem_descList.1 hy,
      fun h => ⟨_, mem_descList.2 h, by ring⟩⟩
  have mP' : ∀ x, x ∈ (grid D τ).parD (i + 1) j ↔ x ∈ P ∨ (x.1 ∈ (grid D τ).blockC (D.R.m - i) ∧ x.2 = true) := by
    intro x
    rw [hP, GridData.mem_parD, GridData.mem_parD]
    have hm : (grid D τ).m = D.R.m := rfl
    rw [hm]
    constructor
    · rintro (h | h | h | ⟨l, hl1, hl2, hx, hs⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr (Or.inl h))
      · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
      · rcases (show l = D.R.m - i ∨ D.R.m - i + 1 ≤ l by omega) with rfl | h
        · exact Or.inr ⟨hx, hs⟩
        · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨l, h, hl2, hx, hs⟩)))
    · rintro ((h | h | h | ⟨l, hl1, hl2, hx, hs⟩) | ⟨hx, hs⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr ⟨l, by omega, hl2, hx, hs⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨D.R.m - i, by omega, by omega, hx, hs⟩))
  have mblk : ∀ y, y ∈ Formalism.BasicNotions.TH.block (GlobalTheory.Grid.sLen D) ↔ y + c ∈ (grid D τ).blockC (D.R.m - i) := by
    intro y
    show _ ↔ y + c ∈ TPar.block c (GlobalTheory.Grid.sLen D)
    have h1 : y ∈ Formalism.BasicNotions.TH.block (GlobalTheory.Grid.sLen D) ↔ y ∈ TPar.block 0 (GlobalTheory.Grid.sLen D) := by
      simp [mem_block, Formalism.BasicNotions.TH.block, eq_comm]
    have h2 := sub_mem_block (c := (0 : ℚ)) (x := y + c) (h := c) (t := GlobalTheory.Grid.sLen D)
    rw [add_sub_cancel_right, zero_add] at h2
    rw [h1, h2]
  refine ⟨be, de, ?_, ?_, ?_⟩
  · have hN0 : (0 : ℚ) ≤ 2 * (GlobalTheory.Grid.bigN D : ℚ) ^ 3 := by positivity
    have hga := GlobalTheory.GridParD.grid_hga D τ
    have hgapA : ∀ i', GapOver ((grid D τ).parD i' j) (2 * (GlobalTheory.Grid.bigN D : ℚ) ^ 3) := fun i' =>
      GlobalTheory.GridParD.gapOver_parD (grid D τ) i' j hN0 (grid_nearMid D τ) (GlobalTheory.GridParD.gridDataAtRealPlace_neg_firstLowEnd_lt_cloud D τ)
        (GlobalTheory.GridParD.grid_heb D τ) (GlobalTheory.GridParD.grid_hbb D τ hN) hga
    have hgap := hgapA i
    have hbel : ∀ x ∈ entries P, x + ((GlobalTheory.Grid.sLen D : ℚ) + 1) / 2 ≤ c :=
      GlobalTheory.GridParD.entries_parD_le (grid D τ) hi hj (grid_nearMid D τ) (GlobalTheory.GridParD.gridDataAtRealPlace_neg_firstLowEnd_lt_cloud D τ)
        (GlobalTheory.GridParD.grid_hbe D τ) (by linarith)
    have hint := int_parD D τ i j
    have hcard0 : P.card ≤ rkV D i j := card_parD_le D τ i j hi.le
    set R : ℕ := rkV D D.R.m D.R.m with hRdef
    set H : ℚ := 2 * (GlobalTheory.Grid.bigN D : ℚ) ^ 3 with hH
    have hR0 : (0 : ℚ) ≤ (R : ℚ) ^ 3 := by positivity
    have hr : Odd D.R.r := by
      obtain ⟨a, ha⟩ := D.R.k_even; obtain ⟨b, hb⟩ := D.R.m_even
      have := D.R.two_le_m
      exact ⟨a + b - 1, by unfold Ranks.r; omega⟩
    have hs : Odd (GlobalTheory.Grid.sLen D) := by unfold GlobalTheory.Grid.sLen; exact hr.add_even (by decide)
    obtain ⟨q, hq⟩ := hs
    have hs1 : (1 : ℚ) ≤ (GlobalTheory.Grid.sLen D : ℚ) := by
      rw [hq]; push_cast; have : (0 : ℚ) ≤ q := by positivity
      linarith
    have hbN : (0 : ℚ) ≤ (GlobalTheory.Grid.bigN D : ℚ) ^ 3 := by positivity
    have ebe : ∀ e ∈ be, e + c ∈ entries P := fun e he => fst_mem_entries ((mbe e).1 he)
    have ede : ∀ e ∈ de, e + c ∈ entries P := fun e he => fst_mem_entries ((mde e).1 he)
    have hneg : ∀ e, e + c ∈ entries P → e + ((GlobalTheory.Grid.sLen D : ℚ) + 1) / 2 ≤ 0 := by
      intro e he; have := hbel _ he; linarith
    have hent : ∀ e ∈ be ++ de, e + c ∈ entries P := by
      intro e he
      rcases List.mem_append.1 he with h | h
      · exact ebe e h
      · exact ede e h
    have pbe : be.Pairwise (· > ·) := (pairwise_descList Pp).map _ fun a b (h : a > b) => show a - c > b - c by linarith
    have pde : de.Pairwise (· > ·) := (pairwise_descList Pm).map _ fun a b (h : a > b) => show a - c > b - c by linarith
    have hlen : be.length + de.length = P.card := by
      have h1 : Pp.card = (P.filter fun x => x.2 = true).card :=
        Finset.card_image_of_injOn fun x hx y hy e => Prod.ext e (by
          rw [(Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2, (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).2])
      have h2 : Pm.card = (P.filter fun x => x.2 = false).card :=
        Finset.card_image_of_injOn fun x hx y hy e => Prod.ext e (by
          rw [(Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2, (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).2])
      simp only [hbe, hde, List.length_map, descList, Finset.length_sort, h1, h2]
      exact nPlus_add_nMinus P
    have hv : (((grid D τ).v 2 : ℚ), true) ∈ P := GridData.mem_parD.2 (Or.inl ⟨GridData.mem_cloud.2
      ⟨2, le_rfl, by have := D.R.m_add_three_le_k; show 2 ≤ D.R.k; omega, rfl⟩, rfl⟩)
    have hvbe : ((grid D τ).v 2 : ℚ) - c ∈ be := (mbe _).2 (by rw [sub_add_cancel]; exact hv)
    have hRi : rkV D (i + 1) j = rkV D i j + GlobalTheory.Grid.sLen D := by unfold rkV; ring
    have hRm : rkV D (i + 1) j ≤ R := by
      have a1 : j * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ hj
      have a2 : (i + 1) * GlobalTheory.Grid.sLen D ≤ D.R.m * GlobalTheory.Grid.sLen D := Nat.mul_le_mul_right _ hi
      simp only [hRdef, rkV]; omega
    have hNR : be.length + de.length + GlobalTheory.Grid.sLen D ≤ R := by omega
    have hRB : R ≤ GlobalTheory.Grid.bigN D := by
      have : D.R.m * (D.R.t + GlobalTheory.Grid.sLen D + 1) = D.R.m * D.R.t + D.R.m * GlobalTheory.Grid.sLen D + D.R.m := by ring
      simp only [hRdef, rkV, GlobalTheory.Grid.bigN]; unfold Ranks.r; omega
    have hRBq : (R : ℚ) ^ 3 ≤ (GlobalTheory.Grid.bigN D : ℚ) ^ 3 := pow_le_pow_left₀ (by positivity) (by exact_mod_cast hRB) 3
    have hpm : ∀ x ∈ be, ∀ y ∈ de, H < |x - y| := by
      intro x hx y hy
      have := hgap _ ((mbe x).1 hx) _ ((mde y).1 hy) (by simp)
      simp only at this
      rwa [show x + c - (y + c) = x - y by ring] at this
    have hblen : (Formalism.BasicNotions.TH.block (GlobalTheory.Grid.sLen D)).length = GlobalTheory.Grid.sLen D := by simp [Formalism.BasicNotions.TH.block]
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine ⟨by unfold GlobalTheory.Grid.sLen; omega, ?_, List.Pairwise.nil, pbe, List.Pairwise.nil, pde, ?_, by simp, ?_, ?_, ?_⟩
      · have := List.length_pos_of_mem hvbe
        simp only [List.length_nil]; omega
      · rw [List.nil_append, List.append_nil, List.Nodup, List.pairwise_append]
        refine ⟨pbe.imp ne_of_gt, pde.imp ne_of_gt, fun a ha b hb hab => ?_⟩
        have := hpm a ha b hb
        rw [hab, sub_self, abs_zero] at this
        linarith
      · intro e he
        have := hneg e (hent e he)
        linarith
      · intro e he
        rw [List.nil_append, List.append_nil] at he
        obtain ⟨z, hz⟩ := hint _ (hent e he)
        refine ⟨z - cen D τ (D.R.m - i) - (q + 1), ?_⟩
        rw [hq, hc] at *
        push_cast
        linarith
      · intro e he
        rw [List.nil_append, List.append_nil] at he
        have := hneg e (hent e he)
        rw [abs_of_neg (by linarith)]
        linarith
    · unfold lamA
      refine gapGt_ofBlocks (by simp) (by simp) fun x hx y hy => ?_
      rw [List.nil_append] at hx hy
      have key : ((([] : List ℚ).length + be.length + ([] : List ℚ).length + de.length + GlobalTheory.Grid.sLen D : ℕ) : ℚ) ^ 3 < |x - y| := by
        have h2 := nat_cube_le (a := ([] : List ℚ).length + be.length + ([] : List ℚ).length + de.length + GlobalTheory.Grid.sLen D)
          (R := R) (by simp only [List.length_nil]; omega)
        have := hpm x hx y hy
        linarith
      exact_mod_cast key
    · unfold lamM'
      refine gapGt_ofBlocks (by simp) (by simp [hblen]; omega) fun x hx y hy => ?_
      rw [List.nil_append] at hx
      rw [List.nil_append] at hy
      have h2 := nat_cube_le (a := ([] : List ℚ).length + be.length + ([] : List ℚ).length + de.length + GlobalTheory.Grid.sLen D)
        (R := R) (by simp only [List.length_nil]; omega)
      have key : ((([] : List ℚ).length + be.length + ([] : List ℚ).length + de.length + GlobalTheory.Grid.sLen D : ℕ) : ℚ) ^ 3 < |x - y| := by
        rcases List.mem_append.1 hy with hy | hy
        · have := hgapA (i + 1) (x + c, false) ((mP' _).2 (Or.inl ((mde x).1 hx))) (y + c, true)
            ((mP' _).2 (Or.inr ⟨(mblk y).1 hy, rfl⟩)) (by simp)
          simp only at this
          rw [show x + c - (y + c) = x - y by ring] at this
          linarith
        · have := hpm y hy x hx
          rw [abs_sub_comm] at this
          linarith
      exact_mod_cast key
    · unfold lamA
      refine gapGe_ofBlocks (by simp) (by simp) fun x hx y hy => ?_
      rw [List.nil_append] at hx hy
      have hb := gridJoin_cubic_size_bound (n := ([] : List ℚ).length + be.length + ([] : List ℚ).length + de.length)
        (mm := min (([] : List ℚ).length + be.length) (([] : List ℚ).length + de.length)) (N := GlobalTheory.Grid.bigN D)
        (by simp only [List.length_nil]; omega) (by simp only [List.length_nil]; omega)
        (by have h1 := hN.1; have h2 : D.R.r ≤ R := by simp only [hRdef, rkV]; omega
            omega)
      have hxy : (H : ℝ) < |((x - y : ℚ) : ℝ)| := by exact_mod_cast hpm x hx y hy
      have hH' : (H : ℝ) = 2 * (GlobalTheory.Grid.bigN D : ℝ) ^ 3 := by rw [hH]; push_cast; ring
      linarith
  · ext ⟨a, s⟩
    show (a, s) ∈ flip (parV D (i + 1) j τ) ↔ (a, s) ∈ negate _
    rw [mem_flip, mem_negate]
    show (a, !s) ∈ negate (shift δ' _) ↔ _
    rw [mem_negate, mem_shift, mem_signed]
    simp only
    rw [mP', mde, List.mem_append, mbe, mblk]
    have e1 : -a - (c + δ') + c = -a - δ' := by ring
    rw [e1]
    cases s <;> simp [or_comm]
  · show dualPar (shift δ P) = _
    congr 1
    ext ⟨a, s⟩
    rw [mem_shift, mem_signed]
    simp only
    rw [mbe, mde]
    have e1 : a - (c + δ) + c = a - δ := by ring
    rw [e1]
    cases s <;> simp

end GlobalTheory.GridJoin.ArrXPar

namespace GlobalTheory.GridJoin.ArrXPar

open GlobalTheory.SignedHC GlobalTheory.RemoveBlock GlobalTheory.PairLift GlobalTheory.Chain GlobalTheory.Grid

theorem arrowX_par : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → GlobalTheory.Hk3.Core R F → ∀ G : GlobalTheory.Grid.GridPre R, G.IsChars → ∀ i j, i < D.R.m → j ≤ D.R.m → ∀ τ : D.what₂.Tau, ∃ aS aT : ℚ, HasInfExp D (G.chiAt (D.R.m - i) (GlobalTheory.Grid.rkV D (i + 1) j)) τ aS ∧ HasInfExp D (G.chiAt (D.R.m - i) (GlobalTheory.Grid.rkV D i j)) τ aT ∧ ∃ be de : List ℚ, Formalism.MainNotions.SchurIrreducible.DataARm (GlobalTheory.Grid.sLen D) [] be [] de ∧ (GlobalTheory.Grid.parV D (i + 1) j τ).image (fun x => (x.1, !x.2)) = dualPar (GlobalTheory.Chain.signed de (Formalism.BasicNotions.TH.block (GlobalTheory.Grid.sLen D) ++ be) aT) ∧ GlobalTheory.Grid.parV D i j τ = dualPar (GlobalTheory.Chain.signed be de aS) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R F hN hC G hch i j hi hj τ
  have hR : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R := ⟨hC.lev, hC.models.inf, hC.models.νY, hC.models.νY', hC.models.νX⟩
  have hm1 : 1 ≤ D.R.m - i := by omega
  have hm2 : D.R.m - i ≤ D.R.m := by omega
  have hexp : HasInfExp D (G.chi (D.R.m - i)) τ (GlobalTheory.Grid.cen D τ (D.R.m - i)) :=
    (GlobalTheory.HeckeInfExp.hasInfExp_iff_hasInfQ D _ _ (fun τ => (GlobalTheory.Grid.cen D τ (D.R.m - i) : ℚ))
      (hch.tie _ hm1 hm2)).2 (hch.aux _ hm1 hm2).inf τ
  obtain ⟨be, de, hd, e1, e2⟩ := par_pair D hN τ i j hi hj
  exact ⟨_, _, hasInfExp_att hexp (exp_eta hR τ) _, hasInfExp_att hexp (exp_eta hR τ) _, be, de, hd, e1, e2⟩

end GlobalTheory.GridJoin.ArrXPar
