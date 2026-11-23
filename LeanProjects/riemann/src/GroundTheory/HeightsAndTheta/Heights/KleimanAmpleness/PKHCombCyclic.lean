import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.KHCombCyclicSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.KHCombContractSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree

noncomputable section

namespace KHCombCyclic

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

abbrev FaceOK (J : ∀ k, Finset (ι k)) (n : ℕ) (G : ∀ k, Finset (ι k)) : Prop :=
  ((∀ l, (G l).Nonempty) ∧ ∑ l, ((G l).card - 1) = n) ∧ ∀ l, J l ⊆ G l

open Classical in

theorem combD_apply (J : ∀ k, Finset (ι k)) (n : ℕ) (f : CombC S J n) (I : CombCell ι J (n + 1)) :
    combD S J n f I = ∑ k, ∑ i ∈ I.1.1 k,
      if h : FaceOK J n (Function.update I.1.1 k ((I.1.1 k).erase i)) then
        (KH.faceSign I.1.1 k i : ℤ) • f ⟨⟨Function.update I.1.1 k ((I.1.1 k).erase i), h.1⟩, h.2⟩
      else 0 := by
  simp only [combD, LinearMap.pi_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  by_cases h : FaceOK J n (Function.update I.1.1 k ((I.1.1 k).erase i))
  · rw [dif_pos h, dif_pos h]; rfl
  · rw [dif_neg h, dif_neg h]; rfl

theorem cell_ext {J : ∀ k, Finset (ι k)} {n : ℕ} {I₁ I₂ : CombCell ι J n} (h : I₁.1.1 = I₂.1.1) : I₁ = I₂ :=
  Subtype.ext (Subtype.ext h)

theorem faceOK_congr {J : ∀ k, Finset (ι k)} {n : ℕ} {k : K} (hJ : J k = ∅) {G G' : ∀ k, Finset (ι k)}
    (hc : (G k).card = (G' k).card) (ho : ∀ m, m ≠ k → G m = G' m) : FaceOK J n G ↔ FaceOK J n G' := by
  have hcard : ∀ m, (G m).card = (G' m).card := fun m => by
    by_cases hm : m = k
    · rw [hm]; exact hc
    · rw [ho m hm]
  have hsub : ∀ m, J m ⊆ G m ↔ J m ⊆ G' m := fun m => by
    by_cases hm : m = k
    · rw [hm, hJ]; simp
    · rw [ho m hm]
  simp only [FaceOK, ← Finset.card_pos, hcard, hsub]

theorem not_faceOK_of_card_one {J : ∀ k, Finset (ι k)} {n : ℕ} (A : ∀ k, Finset (ι k)) (l : K) {i : ι l}
    (hi : i ∈ A l) (h : (A l).card = 1) : ¬ FaceOK J n (Function.update A l ((A l).erase i)) := fun h' => by
  have := h'.1.1 l
  rw [Function.update_self, ← Finset.card_pos, Finset.card_erase_of_mem hi, h] at this
  exact lt_irrefl 0 this

theorem faceSign_pair (A : ∀ k, Finset (ι k)) (k : K) {a b : ι k} (hab : a < b) (he : A k = {a, b}) :
    KH.faceSign A k b = - KH.faceSign A k a := by
  have h1 : ((A k).filter (· < a)).card = 0 := by
    rw [Finset.card_eq_zero, he]
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
    rintro (rfl | rfl)
    · exact lt_irrefl _
    · exact not_lt.mpr hab.le
  have h2 : ((A k).filter (· < b)).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨a, ?_⟩
    rw [he]
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | rfl, h⟩
      · rfl
      · exact absurd h (lt_irrefl _)
    · rintro rfl
      exact ⟨Or.inl rfl, hab⟩
  unfold KH.faceSign
  rw [h1, h2, pow_add, pow_add]
  ring

theorem faceSign_update_one (A : ∀ k, Finset (ι k)) {k l : K} (hl : l ≠ k) (i : ι l) (v : Finset (ι k))
    (hA : (A k).card = 1) (hv : v.card = 1) :
    KH.faceSign (Function.update A k v) l i = KH.faceSign A l i := by
  have hs : ∑ m ∈ Finset.univ.filter (· < l), ((Function.update A k v m).card - 1) =
      ∑ m ∈ Finset.univ.filter (· < l), ((A m).card - 1) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hm : m = k
    · rw [hm, Function.update_self, hv, hA]
    · rw [Function.update_of_ne hm]
  unfold KH.faceSign
  rw [Function.update_of_ne hl, hs]

open Classical in

theorem block_pair (J : ∀ k, Finset (ι k)) (n : ℕ) (f : CombC S J n) (I : CombCell ι J (n + 1)) (k : K)
    (hJ : J k = ∅) (h2 : (I.1.1 k).card = 2)
    (hf : ∀ i ∈ I.1.1 k, ∀ j ∈ I.1.1 k,
      ∀ (hi : FaceOK J n (Function.update I.1.1 k ((I.1.1 k).erase i)))
        (hj : FaceOK J n (Function.update I.1.1 k ((I.1.1 k).erase j))),
      f ⟨⟨_, hi.1⟩, hi.2⟩ = f ⟨⟨_, hj.1⟩, hj.2⟩) :
    ∑ i ∈ I.1.1 k, (if h : FaceOK J n (Function.update I.1.1 k ((I.1.1 k).erase i)) then
        (KH.faceSign I.1.1 k i : ℤ) • f ⟨⟨_, h.1⟩, h.2⟩ else 0) = 0 := by
  obtain ⟨a, b, hab, he⟩ := Finset.card_eq_two.mp h2
  have ha : a ∈ I.1.1 k := by rw [he]; simp
  have hb : b ∈ I.1.1 k := by rw [he]; simp
  have hiff : FaceOK J n (Function.update I.1.1 k ((I.1.1 k).erase a)) ↔
      FaceOK J n (Function.update I.1.1 k ((I.1.1 k).erase b)) :=
    faceOK_congr hJ (by rw [Function.update_self, Function.update_self, Finset.card_erase_of_mem ha,
      Finset.card_erase_of_mem hb]) (fun m hm => by rw [Function.update_of_ne hm, Function.update_of_ne hm])
  let t : ι k → S := fun i => if h : FaceOK J n (Function.update I.1.1 k ((I.1.1 k).erase i)) then
      (KH.faceSign I.1.1 k i : ℤ) • f ⟨⟨_, h.1⟩, h.2⟩ else 0
  show ∑ i ∈ I.1.1 k, t i = 0
  rw [he, Finset.sum_pair hab]
  by_cases hOK : FaceOK J n (Function.update I.1.1 k ((I.1.1 k).erase a))
  · have hOK' := hiff.mp hOK
    simp only [t]
    rw [dif_pos hOK, dif_pos hOK', hf b hb a ha hOK' hOK]
    rcases lt_or_gt_of_ne hab with h | h
    · rw [faceSign_pair I.1.1 k h he, neg_smul, add_neg_cancel]
    · rw [faceSign_pair I.1.1 k h (he.trans (Finset.pair_comm a b)), neg_smul, neg_add_cancel]
  · simp only [t]
    rw [dif_neg hOK, dif_neg (fun h => hOK (hiff.mpr h)), add_zero]

open Classical in

theorem singOne_cocycle (J : ∀ k, Finset (ι k)) (n : ℕ) (hJ : ∀ k, J k = ∅ ∨ J k = Finset.univ) :
    combD S J n (singOne S J n) = 0 := by
  funext I
  rw [combD_apply, Pi.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases hJ k with hk | hk
  · by_cases hc : (I.1.1 k).card = 2 ∧ ∀ m, m ≠ k → J m = ∅ → (I.1.1 m).card = 1
    · have key : ∀ i ∈ I.1.1 k, ∀ hi' : FaceOK J n (Function.update I.1.1 k ((I.1.1 k).erase i)),
          singOne S J n ⟨⟨_, hi'.1⟩, hi'.2⟩ = 1 := by
        intro i hi hi'
        simp only [singOne]
        rw [if_pos]
        intro m hm
        by_cases hmk : m = k
        · rw [hmk, Function.update_self, Finset.card_erase_of_mem hi, hc.1]
        · rw [Function.update_of_ne hmk]
          exact hc.2 m hmk hm
      refine block_pair J n _ I k hk hc.1 fun i hi j hj hi' hj' => ?_
      rw [key i hi hi', key j hj hj']
    · refine Finset.sum_eq_zero fun i hi => ?_
      split_ifs with h
      · have h0 : singOne S J n ⟨⟨_, h.1⟩, h.2⟩ = 0 := by
          simp only [singOne]
          rw [if_neg]
          intro hall
          apply hc
          have hpos : 0 < (I.1.1 k).card := Finset.card_pos.mpr ⟨i, hi⟩
          have hkk := hall k hk
          rw [Function.update_self, Finset.card_erase_of_mem hi] at hkk
          refine ⟨by omega, fun m hm hJm => ?_⟩
          have := hall m hJm
          rwa [Function.update_of_ne hm] at this
        rw [h0, smul_zero]
      · rfl
  · refine Finset.sum_eq_zero fun i hi => dif_neg fun h => ?_
    have hiJ : i ∈ J k := by rw [hk]; exact Finset.mem_univ i
    have := h.2 k hiJ
    rw [Function.update_self] at this
    exact Finset.notMem_erase i _ this

open Classical in

theorem contract_cocycle (J : ∀ k, Finset (ι k)) (n : ℕ) (k : K) (i₀ : ι k) (hJ : J k = ∅)
    (φ g : CombC S J n) (hφ : combD S J n φ = 0)
    (hg1 : ∀ I : CombCell ι J n, (I.1.1 k).card = 1 →
      ∃ I' : CombCell ι J n, I'.1.1 k = {i₀} ∧ (∀ l, l ≠ k → I'.1.1 l = I.1.1 l) ∧ g I = φ I')
    (hg0 : ∀ I : CombCell ι J n, (I.1.1 k).card ≠ 1 → g I = 0) :
    combD S J n g = 0 := by
  funext I
  rw [Pi.zero_apply, combD_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
  have hz : ∀ l, ∀ i ∈ I.1.1 l, ((Function.update I.1.1 l ((I.1.1 l).erase i)) k).card ≠ 1 →
      (if h : FaceOK J n (Function.update I.1.1 l ((I.1.1 l).erase i)) then
        (KH.faceSign I.1.1 l i : ℤ) • g ⟨⟨_, h.1⟩, h.2⟩ else 0) = 0 := by
    intro l i _ hne
    split_ifs with h
    · rw [hg0 ⟨⟨_, h.1⟩, h.2⟩ hne, smul_zero]
    · rfl
  by_cases h1 : (I.1.1 k).card = 1
  · have hOK : FaceOK J (n + 1) (Function.update I.1.1 k {i₀}) :=
      (faceOK_congr hJ (by rw [Function.update_self, Finset.card_singleton, h1])
        (fun m hm => (Function.update_of_ne hm _ _).symm)).mp ⟨I.1.2, I.2⟩
    obtain ⟨I', hI'⟩ : ∃ I' : CombCell ι J (n + 1), I'.1.1 = Function.update I.1.1 k {i₀} :=
      ⟨⟨⟨_, hOK.1⟩, hOK.2⟩, rfl⟩
    have hφI' := congrFun hφ I'
    rw [Pi.zero_apply, combD_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ k)] at hφI'
    refine Eq.trans ?_ hφI'
    have hI'k : (I'.1.1 k).card = 1 := by rw [hI', Function.update_self, Finset.card_singleton]
    congr 1
    · rw [Finset.sum_eq_zero fun i hi => dif_neg (not_faceOK_of_card_one _ k hi h1),
        Finset.sum_eq_zero fun i hi => dif_neg (not_faceOK_of_card_one _ k hi hI'k)]
    refine Finset.sum_congr rfl fun l hlm => ?_
    have hl : l ≠ k := Finset.ne_of_mem_erase hlm
    have hset : I.1.1 l = I'.1.1 l := by rw [hI', Function.update_of_ne hl]
    refine Finset.sum_congr hset fun i hi => ?_
    have hF' : Function.update I'.1.1 l ((I'.1.1 l).erase i) =
        Function.update (Function.update I.1.1 l ((I.1.1 l).erase i)) k {i₀} := by
      rw [← hset, hI', Function.update_comm (Ne.symm hl)]
    have hFk : ((Function.update I.1.1 l ((I.1.1 l).erase i)) k).card = 1 := by
      rw [Function.update_of_ne (Ne.symm hl), h1]
    have hiff : FaceOK J n (Function.update I.1.1 l ((I.1.1 l).erase i)) ↔
        FaceOK J n (Function.update I'.1.1 l ((I'.1.1 l).erase i)) := by
      rw [hF']
      exact faceOK_congr hJ (by rw [Function.update_self, Finset.card_singleton, hFk])
        (fun m hm => (Function.update_of_ne hm _ _).symm)
    have hsign : KH.faceSign I'.1.1 l i = KH.faceSign I.1.1 l i := by
      rw [hI']
      exact faceSign_update_one I.1.1 hl i {i₀} h1 (Finset.card_singleton i₀)
    by_cases hc : FaceOK J n (Function.update I.1.1 l ((I.1.1 l).erase i))
    · rw [dif_pos hc, dif_pos (hiff.mp hc), hsign]
      obtain ⟨I'', hk'', ho'', hgI⟩ := hg1 ⟨⟨_, hc.1⟩, hc.2⟩ hFk
      rw [hgI]
      congr 1
      refine congrArg φ (cell_ext ?_)
      show I''.1.1 = Function.update I'.1.1 l ((I'.1.1 l).erase i)
      rw [hF', Function.eq_update_iff]
      exact ⟨hk'', fun m hm => ho'' m hm⟩
    · rw [dif_neg hc, dif_neg (fun h => hc (hiff.mpr h))]
  · by_cases h2 : (I.1.1 k).card = 2
    · rw [Finset.sum_eq_zero fun l hlm => Finset.sum_eq_zero fun i hi => hz l i hi (by
        rw [Function.update_of_ne (Ne.symm (Finset.ne_of_mem_erase hlm)), h2]; omega), add_zero]
      have hrep : ∀ i ∈ I.1.1 k, ∀ Ii : CombCell ι J n, Ii.1.1 k = {i₀} →
          (∀ m, m ≠ k → Ii.1.1 m = Function.update I.1.1 k ((I.1.1 k).erase i) m) →
          Ii.1.1 = Function.update I.1.1 k {i₀} := fun i _ Ii hk ho => by
        rw [Function.eq_update_iff]
        exact ⟨hk, fun m hm => (ho m hm).trans (Function.update_of_ne hm _ _)⟩
      have hcard : ∀ i ∈ I.1.1 k, ((Function.update I.1.1 k ((I.1.1 k).erase i)) k).card = 1 := fun i hi => by
        rw [Function.update_self, Finset.card_erase_of_mem hi, h2]
      refine block_pair J n g I k hJ h2 fun i hi j hj hi' hj' => ?_
      obtain ⟨Ii, hki, hoi, hgi⟩ := hg1 ⟨⟨_, hi'.1⟩, hi'.2⟩ (hcard i hi)
      obtain ⟨Ij, hkj, hoj, hgj⟩ := hg1 ⟨⟨_, hj'.1⟩, hj'.2⟩ (hcard j hj)
      rw [hgi, hgj]
      exact congrArg φ (cell_ext ((hrep i hi Ii hki hoi).trans (hrep j hj Ij hkj hoj).symm))
    · rw [Finset.sum_eq_zero fun i hi => hz k i hi (by
          rw [Function.update_self, Finset.card_erase_of_mem hi]
          have := Finset.card_pos.mpr ⟨i, hi⟩
          omega),
        Finset.sum_eq_zero fun l hlm => Finset.sum_eq_zero fun i hi => hz l i hi (by
          rw [Function.update_of_ne (Ne.symm (Finset.ne_of_mem_erase hlm))]; exact h1), add_zero]

theorem cyclic_cohom (hC : KHCombContract.Statement) (J : ∀ k, Finset (ι k)) (n : ℕ)
    (hJ : ∀ k, J k = ∅ ∨ J k = Finset.univ) (f : CombC S J n) (hf : combD S J n f = 0) :
    ∃ s : S, f - s • singOne S J n ∈ combB S J n := by
  classical
  by_cases hcell : Nonempty (CombCell ι J n)
  swap
  · refine ⟨0, ?_⟩
    have : f - (0 : S) • singOne S J n = 0 := funext fun I => (hcell ⟨I⟩).elim
    rw [this]
    exact Submodule.zero_mem _
  obtain ⟨I₀⟩ := hcell
  let i₀ : ∀ k, ι k := fun k => (I₀.1.2.1 k).choose
  have key : ∀ T : Finset K, (∀ k ∈ T, J k = ∅) → ∃ φ : CombC S J n, combD S J n φ = 0 ∧
      f - φ ∈ combB S J n ∧ ∀ I : CombCell ι J n,
        ((∀ k ∈ T, (I.1.1 k).card = 1) → ∃ I' : CombCell ι J n, (∀ k ∈ T, I'.1.1 k = {i₀ k}) ∧
          (∀ l, l ∉ T → I'.1.1 l = I.1.1 l) ∧ φ I = f I') ∧
        (¬ (∀ k ∈ T, (I.1.1 k).card = 1) → φ I = 0) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨f, hf, by rw [sub_self]; exact Submodule.zero_mem _, fun I => ⟨fun _ => ⟨I, fun k hk =>
        absurd hk (Finset.notMem_empty k), fun _ _ => rfl, rfl⟩, fun h => absurd (fun k hk =>
        absurd hk (Finset.notMem_empty k)) h⟩⟩
    | insert k T hk ih =>
      intro hT
      obtain ⟨φ, hφ, hfφ, hφI⟩ := ih fun m hm => hT m (Finset.mem_insert_of_mem hm)
      have hJk : J k = ∅ := hT k (Finset.mem_insert_self k T)
      obtain ⟨g, hφg, hg⟩ := hC S K ι J n k (i₀ k) (by rw [hJk]; exact Finset.notMem_empty _) φ hφ
      refine ⟨g, contract_cocycle J n k (i₀ k) hJk φ g hφ (fun I h1 => (hg I).1 ⟨hJk, h1⟩)
        (fun I h1 => (hg I).2 fun h => h1 h.2), ?_, fun I => ⟨?_, ?_⟩⟩
      · have := Submodule.add_mem _ hfφ hφg
        rwa [sub_add_sub_cancel] at this
      · intro hI
        obtain ⟨I₁, hI₁k, hI₁o, hgI⟩ := (hg I).1 ⟨hJk, hI k (Finset.mem_insert_self k T)⟩
        have hne : ∀ m ∈ T, m ≠ k := fun m hm h => hk (h ▸ hm)
        have hI₁T : ∀ m ∈ T, (I₁.1.1 m).card = 1 := fun m hm => by
          rw [hI₁o m (hne m hm)]
          exact hI m (Finset.mem_insert_of_mem hm)
        obtain ⟨I', hI'T, hI'o, hφI₁⟩ := (hφI I₁).1 hI₁T
        refine ⟨I', fun m hm => ?_, fun l hl => ?_, hgI.trans hφI₁⟩
        · rcases Finset.mem_insert.mp hm with h | hm
          · rw [h, hI'o k hk, hI₁k]
          · exact hI'T m hm
        · have hlk : l ≠ k := fun h => hl (by rw [h]; exact Finset.mem_insert_self k T)
          rw [hI'o l (fun h => hl (Finset.mem_insert_of_mem h)), hI₁o l hlk]
      · intro hI
        by_cases h1 : (I.1.1 k).card = 1
        · obtain ⟨I₁, hI₁k, hI₁o, hgI⟩ := (hg I).1 ⟨hJk, h1⟩
          rw [hgI]
          refine (hφI I₁).2 fun hall => hI fun m hm => ?_
          rcases Finset.mem_insert.mp hm with h | hm
          · rw [h]; exact h1
          · rw [← hI₁o m (fun h => hk (h ▸ hm))]
            exact hall m hm
        · exact (hg I).2 fun h => h1 h.2
  obtain ⟨E, hE⟩ : ∃ E : Finset K, ∀ k, k ∈ E ↔ J k = ∅ :=
    ⟨Finset.univ.filter fun k => J k = ∅, fun k => by simp⟩
  obtain ⟨φ, -, hfφ, hφI⟩ := key E fun k hk => (hE k).mp hk
  have hval : ∀ I₁ I₂ : CombCell ι J n, (∀ k ∈ E, (I₁.1.1 k).card = 1) → (∀ k ∈ E, (I₂.1.1 k).card = 1) →
      φ I₁ = φ I₂ := by
    intro I₁ I₂ h₁ h₂
    obtain ⟨I₁', hk₁, ho₁, hφ₁⟩ := (hφI I₁).1 h₁
    obtain ⟨I₂', hk₂, ho₂, hφ₂⟩ := (hφI I₂).1 h₂
    have huniv : ∀ I : CombCell ι J n, ∀ l, l ∉ E → I.1.1 l = Finset.univ := fun I l hl => by
      have hJl : J l = Finset.univ := (hJ l).resolve_left fun h => hl ((hE l).mpr h)
      have := I.2 l
      rw [hJl] at this
      exact Finset.univ_subset_iff.mp this
    rw [hφ₁, hφ₂]
    refine congrArg f (cell_ext (funext fun l => ?_))
    by_cases hl : l ∈ E
    · rw [hk₁ l hl, hk₂ l hl]
    · rw [ho₁ l hl, ho₂ l hl, huniv I₁ l hl, huniv I₂ l hl]
  refine ⟨if h : ∃ I : CombCell ι J n, ∀ k ∈ E, (I.1.1 k).card = 1 then φ h.choose else 0, ?_⟩
  have hφs : φ = (if h : ∃ I : CombCell ι J n, ∀ k ∈ E, (I.1.1 k).card = 1 then φ h.choose else 0) •
      singOne S J n := by
    funext I
    simp only [Pi.smul_apply, singOne, smul_eq_mul]
    by_cases hI : ∀ k ∈ E, (I.1.1 k).card = 1
    · have h : ∃ I : CombCell ι J n, ∀ k ∈ E, (I.1.1 k).card = 1 := ⟨I, hI⟩
      rw [dif_pos h, if_pos (fun k hk => hI k ((hE k).mpr hk)), mul_one]
      exact hval I h.choose hI h.choose_spec
    · rw [if_neg (fun h => hI fun k hk => h k ((hE k).mp hk)), mul_zero]
      exact (hφI I).2 hI
  rw [← hφs]
  exact hfφ

end KHCombCyclic

theorem KHCombCyclic.proof (hC : KHCombContract.Statement) : KHCombCyclic.Statement := by
  intro S _ K _ _ ι _ _ J n hJ
  exact ⟨KHCombCyclic.singOne_cocycle J n hJ, fun f hf => KHCombCyclic.cyclic_cohom hC J n hJ f hf⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
