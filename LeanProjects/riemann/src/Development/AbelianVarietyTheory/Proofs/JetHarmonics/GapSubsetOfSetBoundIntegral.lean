import Mathlib
import Formalism.FlagUnipotentLattices.UnipotentStabiliserCharacterisation
import Formalism.FormalDegreeBessel.FormalDegreeRatio.DSFdeg
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.DegreeProportionalWords

open Finset
open scoped ENNReal

noncomputable section

namespace GlobalTheory.CompareIterDegree

open Formalism.QuantumDeterminants Formalism.HermitianLatticeCounting.ExpansionTerms GlobalTheory.IndefiniteRowSideFullHecke.DegreeProportionalWords

theorem norm_mul_sqrt (z : ℂ) (r : ℝ) : ‖z * ((Real.sqrt r : ℝ) : ℂ)‖ = |‖z‖| * √r := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg r), abs_norm]

theorem termCount_iff : FormalDegreeSubsetSum ↔ TermCount := by
  constructor
  · intro h n l H H' τ ρ hH hH' hτ hρ
    have := h n l (fun I => ‖τ I‖) ρ (H * H') (mul_nonneg hH hH')
      (fun I hI => ⟨by simpa using hτ I hI, (hρ I hI).1.le, (hρ I hI).2⟩)
    simp only [norm_mul_sqrt, gam]
    simpa only [mul_assoc] using this
  · intro h n l tau ratio H hH hI
    classical
    have key := h n l H 1 (fun I => if ratio I = 0 then 0 else (tau I : ℂ))
      (fun I => if ratio I = 0 then (Real.exp 1 * n) ^ l else ratio I) hH zero_le_one ?_ ?_
    · simp only [norm_mul_sqrt, gam, mul_one] at key
      refine le_trans (le_of_eq (sum_congr rfl fun I _ => ?_)) key
      by_cases h0 : ratio I = 0 <;> simp [h0]
    · intro I hc
      by_cases h0 : ratio I = 0
      · simp [h0, pow_nonneg hH]
      · simpa [h0] using (hI I hc).1
    · intro I hc
      by_cases h0 : ratio I = 0
      · simp only [h0, if_true, le_refl, and_true]
        rcases I.eq_empty_or_nonempty with rfl | ⟨s, _⟩
        · simp [← hc]
        · have : (0 : ℝ) < n := by exact_mod_cast s.pos
          positivity
      · simp only [h0, if_false]
        exact ⟨lt_of_le_of_ne (hI I hc).2.1 (Ne.symm h0), (hI I hc).2.2⟩

theorem termCountNorm_of (h : TermCount) : TermCountNorm := by
  intro V _ _ n l H H' τ ρ v w hH hH' hτ hρ hw
  refine (norm_sum_le _ _).trans (le_trans ?_ (mul_le_mul_of_nonneg_right
    (h n l H H' τ ρ hH hH' hτ hρ) (norm_nonneg v)))
  rw [sum_mul]
  refine sum_le_sum fun I hI => ?_
  rw [norm_smul, norm_mul_sqrt, abs_norm, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hw I (mem_powersetCard.1 hI).2) (norm_nonneg _)

theorem iteration_iff : IteratedHighestWeightBound ↔ Iteration := by
  constructor
  · intro h A V ι _ _ _ N M j D w lam R Γ hN hM hΓ hone L μ hμ
    have hsub : ∀ (P : A → ℝ), IsGauge P → ∀ x y, ⌈P (x + y)⌉₊ ≤ ⌈P x⌉₊ + ⌈P y⌉₊ := fun P hP x y =>
      (Nat.ceil_mono (hP.2 x y)).trans (Nat.ceil_add_le _ _)
    obtain ⟨a, ha, hb, hc⟩ := h V A ι j D w (fun x => ⌈N x⌉₊) (fun x => ⌈M x⌉₊) μ Γ 0 (wordWt w L) hΓ
      (hsub N hN) (hsub M hM) (by simp [hN.1]) (by simp [hM.1]) (by
        intro κ i hκ
        have h1 : N (κ - μ) ≤ (wordWt w L : ℝ) := Nat.ceil_le.1 (by simpa using hκ)
        have h2 := hN.2 (κ - μ) (μ - lam)
        rw [sub_add_sub_cancel] at h2
        obtain ⟨a, ha, hs, hl⟩ := hone i κ (by linarith)
        exact ⟨a, ha, hl, fun ν hν => ⟨Nat.ceil_le.2 (hs ν hν).1,
          Nat.ceil_le.2 (by simpa using (hs ν hν).2)⟩⟩) μ L (by simp [hN.1, wordWt])
    exact ⟨a, ha, fun ν hν => ⟨Nat.ceil_le.1 (hc ν hν).1, Nat.ceil_le.1 (hc ν hν).2⟩, hb⟩
  · intro h V P Λ _ _ _ jh Dop wt N1 Ninf lam Gam c0 q0 hG h1 h2 h3 h4 hone μ al hμ
    obtain ⟨a, ha, hs, hl⟩ := h P V Λ (fun x => (N1 x : ℝ)) (fun x => (Ninf x : ℝ)) jh Dop wt lam
      ((q0 : ℝ) - c0) Gam ⟨by simp [h3], fun x y => by beta_reduce; exact_mod_cast h1 x y⟩
      ⟨by simp [h4], fun x y => by beta_reduce; exact_mod_cast h2 x y⟩ hG (by
        intro i κ hκ
        have hκ' : N1 (κ - lam) + c0 ≤ q0 := by
          have : ((N1 (κ - lam) + c0 : ℕ) : ℝ) ≤ q0 := by push_cast; linarith
          exact_mod_cast this
        obtain ⟨a, ha, hl, hs⟩ := hone κ i hκ'
        exact ⟨a, ha, fun ν hν => ⟨by beta_reduce; exact_mod_cast (hs ν hν).1,
          by beta_reduce; exact_mod_cast (hs ν hν).2⟩, hl⟩)
      al μ (by
        have : ((N1 (μ - lam) + (al.map wt).sum + c0 : ℕ) : ℝ) ≤ q0 := by exact_mod_cast hμ
        rw [Nat.cast_add, Nat.cast_add] at this
        simp only [wordWt]
        linarith)
    exact ⟨a, ha, hl, fun ν hν => ⟨by have := (hs ν hν).1; simp only [wordWt] at this; exact_mod_cast this,
      Nat.cast_le.1 (hs ν hν).2⟩⟩

theorem l1_add_le {A : Type} (a b : A →₀ ℂ) : l1 (a + b) ≤ l1 a + l1 b := by
  classical
  have e : ∀ c : A →₀ ℂ, c.support ⊆ a.support ∪ b.support →
      l1 c = ∑ ν ∈ a.support ∪ b.support, ‖c ν‖ := fun c hc =>
    sum_subset hc fun ν _ hν => by simp [Finsupp.notMem_support_iff.1 hν]
  rw [e _ Finsupp.support_add, e a subset_union_left, e b subset_union_right, ← sum_add_distrib]
  exact sum_le_sum fun ν _ => norm_add_le _ _

theorem comb_eq {A V : Type} [AddCommGroup A] [AddCommGroup V] [Module ℂ V] (j : A → V) (μ : A) (a : A →₀ ℂ) :
    comb j μ a = Finsupp.linearCombination ℂ (fun ν => j (μ + ν)) a := rfl

theorem iterationSum_of (h : Iteration) : IterationSum := by
  intro A V ι _ _ _ N M j D w lam R Γ hN hM hΓ hone L μ c hc
  classical
  have key : ∀ S : Finset A, S ⊆ c.support → ∃ c' : A →₀ ℂ,
      wordOp D L (∑ ν ∈ S, c ν • j (μ + ν)) = comb j μ c' ∧
      (∀ ν' ∈ c'.support, ∃ ν ∈ c.support, N (ν' - ν) ≤ (wordWt w L : ℝ) ∧ M (ν' - ν) ≤ (L.length : ℝ)) ∧
      l1 c' ≤ Γ ^ wordWt w L * ∑ ν ∈ S, ‖c ν‖ := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro _; exact ⟨0, by simp [comb], by simp, by simp [l1]⟩
    | insert ν S hν ih =>
      intro hS
      obtain ⟨c', h1, h2, h3⟩ := ih ((subset_insert _ _).trans hS)
      have hνc : ν ∈ c.support := hS (mem_insert_self _ _)
      obtain ⟨a, ha, hs, hl⟩ := h A V ι N M j D w lam R Γ hN hM hΓ hone L (μ + ν) (hc ν hνc)
      set b : A →₀ ℂ := c ν • Finsupp.equivMapDomain (Equiv.addLeft ν) a with hb
      have hbs : ∀ x, b x = c ν * a (x - ν) := by
        intro x; simp [hb, Finsupp.equivMapDomain_apply, neg_add_eq_sub]
      refine ⟨b + c', ?_, ?_, ?_⟩
      · rw [sum_insert hν, map_add, map_smul, h1, ha, comb_eq j μ (b + c'), map_add, hb, map_smul,
          Finsupp.equivMapDomain_eq_mapDomain, Finsupp.linearCombination_mapDomain, comb_eq, comb_eq]
        simp [Function.comp_def, add_assoc]
      · intro x hx
        rcases mem_union.1 (Finsupp.support_add hx) with hx | hx
        · refine ⟨ν, hνc, hs _ ?_⟩
          rw [Finsupp.mem_support_iff] at hx ⊢
          rw [hbs] at hx
          exact right_ne_zero_of_mul hx
        · exact h2 x hx
      · have hb1 : l1 b = ‖c ν‖ * l1 a := by
          have e1 : l1 b = (Finsupp.equivMapDomain (Equiv.addLeft ν) a).sum fun _ z => ‖c ν • z‖ :=
            Finsupp.sum_smul_index' (h := fun _ z => ‖z‖) (by simp)
          rw [e1, Finsupp.sum_equivMapDomain]
          simp [Finsupp.sum, l1, mul_sum]
        rw [sum_insert hν, mul_add]
        refine (l1_add_le _ _).trans (add_le_add ?_ h3)
        rw [hb1, mul_comm]
        exact mul_le_mul_of_nonneg_right hl (norm_nonneg _)
  exact key c.support subset_rfl

theorem iterationGauge_of (h : Iteration) : IterationGauge := by
  intro A V ι _ _ _ N M j D w lam R Γ p K hN hM hΓ hone hadd hsm hK L μ hμ
  obtain ⟨a, ha, hs, hl⟩ := h A V ι N M j D w lam R Γ hN hM hΓ hone L μ hμ
  have hp0 : p 0 = 0 := by simpa using hsm 0 0
  have h1 : p (comb j μ a) ≤ ∑ ν ∈ a.support, p (a ν • j (μ + ν)) :=
    Finset.le_sum_of_subadditive p hp0.le hadd _ _
  rw [ha]
  refine h1.trans (le_trans (sum_le_sum (g := fun ν => ‖a ν‖ₑ * K) fun ν hν => ?_) ?_)
  · rw [hsm]
    refine mul_le_mul' le_rfl (hK _ ?_)
    have h2 := hN.2 (μ - lam) ν
    rw [show μ - lam + ν = μ + ν - lam by abel] at h2
    linarith [(hs ν hν).1]
  · rw [← sum_mul]
    refine mul_le_mul' (le_trans (le_of_eq ?_) (ENNReal.ofReal_le_ofReal hl)) le_rfl
    rw [l1, ENNReal.ofReal_sum_of_nonneg fun _ _ => norm_nonneg _]
    simp

theorem fdeg_ratio_abs {n : ℕ} (μ : Fin n → ℝ) (s : Fin n) (t : ℝ) (hinj : Function.Injective μ) :
    fdegHC (μ + Pi.single s t) / fdegHC μ = ∏ c ∈ univ.erase s, |(μ s + t - μ c) / (μ s - μ c)| := by
  set μ' : Fin n → ℝ := μ + Pi.single s t with hμ'
  have hμ'a : ∀ a, μ' a = μ a + if a = s then t else 0 := by
    intro a; simp [hμ', Pi.single_apply]
  set r : Fin n → ℝ := fun c => |(μ s + t - μ c) / (μ s - μ c)| with hr
  have hfac : ∀ a b : Fin n, a < b →
      |μ' a - μ' b| / |μ a - μ b| = (if a = s then r b else 1) * (if b = s then r a else 1) := by
    intro a b hab
    have hne : a ≠ b := ne_of_lt hab
    by_cases has : a = s
    · subst has
      have hbs : b ≠ a := fun h => hne h.symm
      rw [hμ'a, hμ'a, if_pos rfl, if_neg hbs, if_pos rfl, if_neg hbs]
      simp [hr, abs_div]
    · by_cases hbs : b = s
      · subst hbs
        rw [hμ'a, hμ'a, if_neg has, if_pos rfl, if_neg has, if_pos rfl]
        simp only [hr, one_mul, add_zero, abs_div]
        rw [abs_sub_comm (μ a) (μ b + t), abs_sub_comm (μ a) (μ b)]
      · rw [hμ'a, hμ'a, if_neg has, if_neg hbs, if_neg has, if_neg hbs]
        have h0 : μ a - μ b ≠ 0 := sub_ne_zero.2 (fun h => hne (hinj h))
        simp only [add_zero, mul_one]
        exact div_self (abs_ne_zero.2 h0)
  have hden : (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b),
      (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) ≠ 0 := by
    refine prod_ne_zero_iff.2 fun a _ => prod_ne_zero_iff.2 fun b hb => ?_
    have hab : a < b := (mem_filter.1 hb).2
    have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
    linarith
  unfold fdegHC
  rw [div_div_div_cancel_right₀ hden, ← prod_div_distrib]
  simp_rw [← prod_div_distrib]
  rw [prod_congr rfl (fun a _ => prod_congr rfl (fun b hb => hfac a b (mem_filter.1 hb).2))]
  simp_rw [prod_mul_distrib]
  have h1 : (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b),
      (if a = s then r b else 1)) = ∏ b ∈ univ.filter (fun b : Fin n => s < b), r b := by
    rw [prod_eq_single s]
    · simp
    · intro a _ has; simp [has]
    · intro h; exact absurd (mem_univ s) h
  have h2 : (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b),
      (if b = s then r a else 1)) = ∏ a ∈ univ.filter (fun a : Fin n => a < s), r a := by
    rw [prod_filter]
    refine prod_congr rfl fun a _ => ?_
    rw [prod_ite_eq']
    simp
  rw [h1, h2, ← prod_filter_mul_prod_filter_not (univ.erase s) (fun c => s < c)]
  congr 1
  · congr 1; ext c
    simp only [mem_filter, mem_erase, mem_univ, and_true, true_and, ne_eq, Fin.lt_def, Fin.ext_iff]
    constructor <;> intro h <;> omega
  · congr 1; ext c
    simp only [mem_filter, mem_erase, mem_univ, and_true, true_and, ne_eq, Fin.lt_def, Fin.ext_iff]
    constructor <;> intro h <;> omega

theorem fac_nonneg {d t : ℝ} (hd : 1 ≤ |d|) (ht : |t| ≤ 1) : 0 ≤ (d + t) / d := by
  rw [abs_le] at ht
  rcases le_abs.1 hd with h | h
  · exact div_nonneg (by linarith) (by linarith)
  · exact div_nonneg_of_nonpos (by linarith) (by linarith)

theorem fdeg_ratio {n : ℕ} (μ : Fin n → ℝ) (s : Fin n) (t : ℝ) (ht : |t| ≤ 1)
    (hgap : ∀ a b, a ≠ b → 1 ≤ |μ a - μ b|) :
    fdegHC (μ + Pi.single s t) / fdegHC μ = ∏ c ∈ univ.erase s, (μ s + t - μ c) / (μ s - μ c) := by
  have hinj : Function.Injective μ := fun a b hab => by
    by_contra hne
    have := hgap a b hne
    rw [hab, sub_self, abs_zero] at this
    linarith
  rw [fdeg_ratio_abs μ s t hinj]
  refine prod_congr rfl fun c hc => abs_of_nonneg ?_
  rw [add_sub_right_comm]
  exact fac_nonneg (hgap s c (ne_of_mem_erase hc).symm) ht

theorem gapOne_of_regInt {n : ℕ} {μ : Fin n → ℝ} (h : RegInt μ) : ∀ a b, a ≠ b → 1 ≤ |μ a - μ b| := by
  intro a b hab
  obtain ⟨m, hm⟩ := h.2 a b
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hab (h.1 (by simpa [sub_eq_zero] using hm))
  rw [hm]
  exact_mod_cast Int.one_le_abs hm0

theorem sub_single {n : ℕ} (μ : Fin n → ℝ) (s : Fin n) :
    μ - Pi.single s 1 = μ + Pi.single s (-1) := by
  rw [Pi.single_neg, sub_eq_add_neg]

theorem step_ratio_eq {n : ℕ} {μ : Fin n → ℝ} (h : RegInt μ) (s : Fin n) :
    fdegHC (μ + Pi.single s 1) / fdegHC μ = ∏ c ∈ univ.erase s, (μ s + 1 - μ c) / (μ s - μ c) ∧
    fdegHC (μ - Pi.single s 1) / fdegHC μ = ∏ c ∈ univ.erase s, (μ s - 1 - μ c) / (μ s - μ c) := by
  refine ⟨fdeg_ratio μ s 1 (by simp) (gapOne_of_regInt h), ?_⟩
  rw [sub_single, fdeg_ratio μ s (-1) (by simp) (gapOne_of_regInt h)]
  simp only [← sub_eq_add_neg]

theorem stepSize_iff : DegStepBound ↔ StepSize := by
  refine forall_congr' fun n => forall_congr' fun μ => forall_congr' fun s => ?_
  rw [RegInt, and_imp]
  refine forall_congr' fun h1 => forall_congr' fun h2 => ?_
  rw [(step_ratio_eq ⟨h1, h2⟩ s).1, (step_ratio_eq ⟨h1, h2⟩ s).2]

theorem chain_bound {α : Type} [DecidableEq α] (F : Finset α → ℝ) (lo hi : ℝ) (hlo : 0 ≤ lo) (I : Finset α)
    (hpos : ∀ J ⊆ I, 0 < F J)
    (hstep : ∀ J s, s ∉ J → insert s J ⊆ I → lo ≤ F (insert s J) / F J ∧ F (insert s J) / F J ≤ hi) :
    lo ^ I.card ≤ F I / F ∅ ∧ F I / F ∅ ≤ hi ^ I.card := by
  have h0 := hpos ∅ (empty_subset _)
  induction I using Finset.induction_on with
  | empty => simp [h0.ne']
  | insert s J hs ih =>
    have hJ := hpos J (subset_insert _ _)
    obtain ⟨i1, i2⟩ := ih (fun K hK => hpos K (hK.trans (subset_insert _ _)))
      (fun K u hu hK => hstep K u hu (hK.trans (subset_insert _ _)))
    obtain ⟨j1, j2⟩ := hstep J s hs subset_rfl
    have e : F (insert s J) / F ∅ = F J / F ∅ * (F (insert s J) / F J) := by field_simp
    rw [card_insert_of_notMem hs, pow_succ, pow_succ, e]
    exact ⟨mul_le_mul i1 j1 hlo (div_pos hJ h0).le,
      mul_le_mul i2 j2 (hlo.trans j1) ((div_pos hJ h0).le.trans i2)⟩

theorem eSet_insert {n : ℕ} {J : Finset (Fin n)} {s : Fin n} (hs : s ∉ J) :
    eSet (insert s J) = eSet J + Pi.single s 1 := by
  funext a
  by_cases h : a = s
  · subst h; simp [eSet, hs]
  · simp [eSet, h]

theorem eSet_empty {n : ℕ} : eSet (∅ : Finset (Fin n)) = 0 := by
  funext a; simp [eSet]

theorem inj_of_gapTwo {n : ℕ} {μ : Fin n → ℝ} (h : GapTwo μ) : Function.Injective μ := fun a b hab => by
  by_contra hne
  have := h a b hne
  rw [hab, sub_self, abs_zero] at this
  linarith

theorem inj_add_of_gapTwo {n : ℕ} {μ e : Fin n → ℝ} (h : GapTwo μ) (he : ∀ a b, |e a - e b| ≤ 1) :
    Function.Injective (μ + e) := fun a b hab => by
  by_contra hne
  have h1 := h a b hne
  have h2 := he b a
  rw [show μ a - μ b = e b - e a by simp only [Pi.add_apply] at hab; linarith] at h1
  linarith

theorem gapTwo_iff {n : ℕ} {μ : Fin n → ℝ} (h : StrictAnti μ) :
    (∀ a b, a < b → 2 ≤ μ a - μ b) ↔ GapTwo μ := by
  constructor
  · intro hg a b hab
    rcases lt_or_gt_of_ne hab with h1 | h1
    · exact (hg a b h1).trans (le_abs_self _)
    · rw [abs_sub_comm]; exact (hg b a h1).trans (le_abs_self _)
  · intro hg a b hab
    have := hg a b hab.ne
    rwa [abs_of_pos (sub_pos.2 (h hab))] at this

theorem setBound_of_stepSize (h : StepSize) : DegSetBound := by
  intro n μ I hanti hint hgap
  have hg := (gapTwo_iff hanti).1 hgap
  have hreg : ∀ J : Finset (Fin n), RegInt (μ + eSet J) := fun J =>
    ⟨inj_add_of_gapTwo hg fun a b => by unfold eSet; split_ifs <;> simp, fun a b => by
      obtain ⟨m, hm⟩ := hint a b
      refine ⟨m + (if a ∈ J then 1 else 0) - (if b ∈ J then 1 else 0), ?_⟩
      simp only [Pi.add_apply, eSet]
      push_cast
      linarith⟩
  have := chain_bound (fun J => fdegHC (μ + eSet J)) (1 / n) n (by positivity) I
    (fun J _ => formal_degree_pos_holds n _ (hreg J).1) (fun J s hs _ => by
      have h1 := (hreg (insert s J)).1
      rw [eSet_insert hs, ← add_assoc] at h1 ⊢
      exact (h n _ s (hreg J)).1 h1)
  simp only [eSet_empty, add_zero, one_div, inv_pow] at this
  exact this

theorem gapSubset_of_gapStep (h : GapStepSize) : GapSubsetSize := by
  intro n μ I
  constructor
  · intro hg
    have := chain_bound (fun J => fdegHC (μ + eSet J)) (1 / (4 * (n : ℝ) ^ 2)) (Real.exp 1 * n) (by positivity) I
      (fun J hJ => formal_degree_pos_holds n _ (inj_of_gapTwo (hg J hJ))) (fun J s hs hJ => by
        have h1 := hg _ hJ
        rw [eSet_insert hs, ← add_assoc] at h1 ⊢
        exact (h n _ s (hg J ((subset_insert _ _).trans hJ))).1 h1)
    simpa only [eSet_empty, add_zero] using this
  · intro hg
    have := chain_bound (fun J => fdegHC (μ - eSet J)) (1 / (4 * (n : ℝ) ^ 2)) (Real.exp 1 * n) (by positivity) I
      (fun J hJ => formal_degree_pos_holds n _ (inj_of_gapTwo (hg J hJ))) (fun J s hs hJ => by
        have h1 := hg _ hJ
        rw [eSet_insert hs, ← sub_sub] at h1 ⊢
        exact (h n _ s (hg J ((subset_insert _ _).trans hJ))).2 h1)
    simpa only [eSet_empty, sub_zero] using this

theorem round_gap {n : ℕ} {μ : Fin n → ℝ} (hg : GapTwo μ) (s : Fin n) (g : ℝ → ℤ) (hm : Monotone g)
    (h2 : ∀ x, g (x + 2) = g x + 2) (h0 : g 0 = 0) :
    GapTwo (fun c => -(g (μ s - μ c) : ℝ)) ∧ ∀ c, c ≠ s → 0 < (μ s - μ c) * g (μ s - μ c) := by
  have key : ∀ x y : ℝ, x + 2 ≤ y → (g x : ℝ) + 2 ≤ g y := fun x y hxy => by
    have := hm hxy
    rw [h2] at this
    exact_mod_cast this
  refine ⟨fun a b hab => ?_, fun c hc => ?_⟩
  · rcases le_abs.1 (hg a b hab) with h | h
    · have := key (μ s - μ a) (μ s - μ b) (by linarith)
      exact le_abs.2 (Or.inl (by linarith))
    · have := key (μ s - μ b) (μ s - μ a) (by linarith)
      exact le_abs.2 (Or.inr (by linarith))
  · rcases le_abs.1 (hg s c hc.symm) with h | h
    · have := key 0 (μ s - μ c) (by linarith)
      rw [h0] at this
      exact mul_pos (by linarith) (by push_cast at this; linarith)
    · have := key (μ s - μ c) 0 (by linarith)
      rw [h0] at this
      exact mul_pos_of_neg_of_neg (by linarith) (by push_cast at this; linarith)

theorem fac_le {x y t : ℝ} (hxy : 0 < x * y) (h : t * y ≤ t * x) : (x + t) / x ≤ (y + t) / y := by
  have hx : x ≠ 0 := left_ne_zero_of_mul hxy.ne'
  have hy : y ≠ 0 := right_ne_zero_of_mul hxy.ne'
  have : (y + t) / y - (x + t) / x = (t * x - t * y) / (x * y) := by field_simp; ring
  have h2 := div_nonneg (sub_nonneg.2 h) hxy.le
  linarith

theorem real_step (h : DegStepBound) {n : ℕ} {μ : Fin n → ℝ} (hg : GapTwo μ) (s : Fin n) (t : ℝ)
    (ht : t = 1 ∨ t = -1) :
    1 / (n : ℝ) ≤ fdegHC (μ + Pi.single s t) / fdegHC μ ∧ fdegHC (μ + Pi.single s t) / fdegHC μ ≤ n := by
  have ht1 : |t| ≤ 1 := by rcases ht with rfl | rfl <;> simp
  rw [fdeg_ratio μ s t ht1 fun a b hab => le_trans one_le_two (hg a b hab)]
  have main : ∀ g : ℝ → ℤ, Monotone g → (∀ x, g (x + 2) = g x + 2) → g 0 = 0 →
      ((∀ x, t * g x ≤ t * x) → ∏ c ∈ univ.erase s, (μ s + t - μ c) / (μ s - μ c) ≤ n) ∧
      ((∀ x, t * x ≤ t * g x) → 1 / (n : ℝ) ≤ ∏ c ∈ univ.erase s, (μ s + t - μ c) / (μ s - μ c)) := by
    intro g hm h2 h0
    obtain ⟨hg', hsg⟩ := round_gap hg s g hm h2 h0
    have hb : 1 / (n : ℝ) ≤ ∏ c ∈ univ.erase s, ((g (μ s - μ c) : ℝ) + t) / g (μ s - μ c) ∧
        ∏ c ∈ univ.erase s, ((g (μ s - μ c) : ℝ) + t) / g (μ s - μ c) ≤ n := by
      have hinj : Function.Injective ((fun c => -(g (μ s - μ c) : ℝ)) + Pi.single s t) :=
        inj_add_of_gapTwo hg' fun a b => by
          simp only [Pi.single_apply]; split_ifs <;> simp [ht1]
      have := h n _ s (inj_of_gapTwo hg') fun a b =>
        ⟨-g (μ s - μ a) - -g (μ s - μ b), by push_cast; rfl⟩
      rcases ht with rfl | rfl
      · simpa [h0, add_comm] using this.1 hinj
      · rw [sub_single] at this
        simpa [h0, add_comm, sub_eq_add_neg] using this.2 hinj
    have hn1 : ∀ c ∈ univ.erase s, 0 ≤ (μ s + t - μ c) / (μ s - μ c) := fun c hc => by
      rw [add_sub_right_comm]
      exact fac_nonneg (le_trans one_le_two (hg s c (ne_of_mem_erase hc).symm)) ht1
    have hn2 : ∀ c ∈ univ.erase s, 0 ≤ ((g (μ s - μ c) : ℝ) + t) / g (μ s - μ c) := fun c hc => by
      have := hg' s c (ne_of_mem_erase hc).symm
      simp only [sub_self, h0, Int.cast_zero, neg_zero, zero_sub, neg_neg] at this
      exact fac_nonneg (le_trans one_le_two this) ht1
    refine ⟨fun hx => le_trans (prod_le_prod hn1 fun c hc => ?_) hb.2,
      fun hx => le_trans hb.1 (prod_le_prod hn2 fun c hc => ?_)⟩
    · rw [add_sub_right_comm]
      exact fac_le (hsg c (ne_of_mem_erase hc)) (hx _)
    · rw [add_sub_right_comm]
      exact fac_le (by rw [mul_comm]; exact hsg c (ne_of_mem_erase hc)) (hx _)
  have hf := main (fun x => ⌊x⌋) Int.floor_mono (fun x => Int.floor_add_ofNat x 2) Int.floor_zero
  have hc := main (fun x => ⌈x⌉) Int.ceil_mono (fun x => Int.ceil_add_ofNat x 2) Int.ceil_zero
  rcases ht with rfl | rfl
  · exact ⟨hc.2 fun x => by simpa using Int.le_ceil x, hf.1 fun x => by simpa using Int.floor_le x⟩
  · exact ⟨hf.2 fun x => by simpa using Int.floor_le x, hc.1 fun x => by simpa using Int.le_ceil x⟩

theorem weaken_consts {n : ℕ} (hn : 0 < n) :
    1 / (4 * (n : ℝ) ^ 2) ≤ 1 / (n : ℝ) ∧ (n : ℝ) ≤ Real.exp 1 * n := by
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨one_div_le_one_div_of_le (by linarith) (by nlinarith), ?_⟩
  have := Real.add_one_le_exp (1 : ℝ)
  nlinarith

theorem gapStep_of_stepBound (h : DegStepBound) : GapStepSize := by
  intro n μ s hg
  obtain ⟨w1, w2⟩ := weaken_consts s.pos
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · obtain ⟨a, b⟩ := real_step h hg s 1 (Or.inl rfl)
    exact ⟨w1.trans a, b.trans w2⟩
  · obtain ⟨a, b⟩ := real_step h hg s (-1) (Or.inr rfl)
    rw [sub_single]
    exact ⟨w1.trans a, b.trans w2⟩

theorem gapSubset_of_setBound_integral (h : DegSetBound) (n : ℕ) (μ : Fin n → ℝ) (I : Finset (Fin n))
    (hanti : StrictAnti μ) (hint : ∀ a b, ∃ m : ℤ, μ a - μ b = (m : ℝ)) :
    ((∀ J ⊆ I, GapTwo (μ + eSet J)) →
      (1 / (4 * (n : ℝ) ^ 2)) ^ I.card ≤ fdegHC (μ + eSet I) / fdegHC μ ∧
        fdegHC (μ + eSet I) / fdegHC μ ≤ (Real.exp 1 * n) ^ I.card) ∧
    ((∀ J ⊆ I, GapTwo (μ - eSet J)) →
      (1 / (4 * (n : ℝ) ^ 2)) ^ I.card ≤ fdegHC (μ - eSet I) / fdegHC μ ∧
        fdegHC (μ - eSet I) / fdegHC μ ≤ (Real.exp 1 * n) ^ I.card) := by
  have w : (1 / (4 * (n : ℝ) ^ 2)) ^ I.card ≤ ((n : ℝ) ^ I.card)⁻¹ ∧
      (n : ℝ) ^ I.card ≤ (Real.exp 1 * n) ^ I.card ∧ 0 < (n : ℝ) ^ I.card := by
    rcases I.eq_empty_or_nonempty with rfl | ⟨s, _⟩
    · simp
    · obtain ⟨w1, w2⟩ := weaken_consts s.pos
      have : (0 : ℝ) < n := by exact_mod_cast s.pos
      rw [← inv_pow, ← one_div (n : ℝ)]
      exact ⟨pow_le_pow_left₀ (by positivity) w1 _, pow_le_pow_left₀ (by positivity) w2 _, by positivity⟩
  refine ⟨fun hg => ?_, fun hg => ?_⟩
  · have h0 := hg ∅ (empty_subset _)
    rw [eSet_empty, add_zero] at h0
    obtain ⟨a, b⟩ := h n μ I hanti hint ((gapTwo_iff hanti).2 h0)
    exact ⟨w.1.trans a, b.trans w.2.1⟩
  · have h0 := hg ∅ (empty_subset _)
    rw [eSet_empty, sub_zero] at h0
    have hI := hg I subset_rfl
    have hanti' : StrictAnti (μ - eSet I) := fun a b hab => by
      have := (gapTwo_iff hanti).2 h0 a b hab
      simp only [Pi.sub_apply, eSet]
      split_ifs <;> linarith
    obtain ⟨a, b⟩ := h n (μ - eSet I) I hanti' (fun a b => by
      obtain ⟨m, hm⟩ := hint a b
      refine ⟨m - (if a ∈ I then 1 else 0) + (if b ∈ I then 1 else 0), ?_⟩
      simp only [Pi.sub_apply, eSet]
      push_cast
      linarith) ((gapTwo_iff hanti').2 hI)
    have e : (fun a => (μ - eSet I) a + if a ∈ I then 1 else 0) = μ := by
      funext a; simp [eSet]
    rw [e] at a b
    have p : 0 < fdegHC μ / fdegHC (μ - eSet I) :=
      div_pos (formal_degree_pos_holds n _ hanti.injective) (formal_degree_pos_holds n _ hanti'.injective)
    rw [← inv_div (fdegHC μ)]
    exact ⟨w.1.trans (inv_anti₀ p b), le_trans (inv_le_of_inv_le₀ w.2.2 a) w.2.1⟩

theorem joined_iff {n : ℕ} (Q : Set (Fin n → ℝ)) (μ ν : Fin n → ℝ) :
    Relation.EqvGen (fun x y => x ∈ Q ∧ y ∈ Q ∧ ∃ s, y = x + Pi.single s 1) μ ν ↔
      Relation.ReflTransGen (StepIn Q) μ ν := by
  have hsymm : ∀ {x y}, StepIn Q x y → StepIn Q y x := by
    rintro x y ⟨hx, hy, s, rfl | rfl⟩
    · exact ⟨hy, hx, s, Or.inr (by simp)⟩
    · exact ⟨hy, hx, s, Or.inl (by simp)⟩
  have hrev : ∀ {x y}, Relation.ReflTransGen (StepIn Q) x y → Relation.ReflTransGen (StepIn Q) y x := by
    intro x y h
    induction h with
    | refl => exact .refl
    | tail _ hs ih => exact .head (hsymm hs) ih
  constructor
  · intro h
    induction h with
    | rel x y h => obtain ⟨hx, hy, s, hs⟩ := h; exact .single ⟨hx, hy, s, Or.inl hs⟩
    | refl x => exact .refl
    | symm x y _ ih => exact hrev ih
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
  · intro h
    induction h with
    | refl => exact .refl _
    | tail _ hs ih =>
      refine .trans _ _ _ ih ?_
      obtain ⟨hx, hy, s, rfl | rfl⟩ := hs
      · exact .rel _ _ ⟨hx, hy, s, rfl⟩
      · exact .symm _ _ (.rel _ _ ⟨hy, hx, s, by simp⟩)

theorem degreeProportional_iff : DegVand ↔ DegreeProportional := by
  constructor
  · intro h n P Q d hreg hpos hstep hPQ hjoin
    rcases P.eq_empty_or_nonempty with rfl | ⟨μ₀, h0⟩
    · exact ⟨1, one_pos, by simp⟩
    refine ⟨d μ₀ / fdegHC μ₀, div_pos (hpos _ (hPQ h0)) (formal_degree_pos_holds n _ (hreg _ (hPQ h0)).1),
      fun μ hμ => ?_⟩
    rw [h n Q d hreg hpos hstep μ₀ μ ((joined_iff Q _ _).2 (hjoin _ h0 _ hμ)) (hPQ h0),
      div_mul_cancel₀ _ (formal_degree_pos_holds n _ (hreg _ (hPQ hμ)).1).ne']
  · intro h n Q d hreg hpos hstep μ ν hj hμ
    have hν : ν ∈ Q := by
      have := (joined_iff Q _ _).1 hj
      induction this with
      | refl => exact hμ
      | tail _ hs _ => exact hs.2.1
    obtain ⟨c, -, hc⟩ := h n {μ, ν} Q d hreg hpos hstep (Set.pair_subset hμ hν) (by
      rintro x (rfl | rfl) y (rfl | rfl)
      · exact .refl
      · exact (joined_iff Q _ _).1 hj
      · exact (joined_iff Q _ _).1 (.symm _ _ hj)
      · exact .refl)
    rw [hc μ (by simp), hc ν (by simp), mul_div_cancel_right₀ _ (formal_degree_pos_holds n _ (hreg _ hμ).1).ne',
      mul_div_cancel_right₀ _ (formal_degree_pos_holds n _ (hreg _ hν).1).ne']

theorem typings_iff :
    (FormalDegreeSubsetSum ∧ IteratedHighestWeightBound ∧ DegSetBound ∧ DegStepBound ∧ DegVand) ↔ Statement := by
  constructor
  · rintro ⟨h1, h2, -, h4, h5⟩
    have t := termCount_iff.1 h1
    have i := iteration_iff.1 h2
    have g := gapStep_of_stepBound h4
    exact ⟨t, termCountNorm_of t, i, iterationSum_of i, iterationGauge_of i, stepSize_iff.1 h4, g,
      gapSubset_of_gapStep g, degreeProportional_iff.1 h5⟩
  · rintro ⟨t, -, i, -, -, s, -, -, d⟩
    exact ⟨termCount_iff.2 t, iteration_iff.2 i, setBound_of_stepSize s, stepSize_iff.2 s,
      degreeProportional_iff.2 d⟩

end GlobalTheory.CompareIterDegree
