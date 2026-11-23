import Development.WeilBound.CoreStatements.LocalThetaKernels.EvlLoc
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell

set_option linter.unusedSectionVars false

noncomputable section

open Matrix MeasureTheory ValuativeRel Topology GlobalTheory.SplitFlip GlobalTheory.SplitWeil
open scoped Pointwise

namespace PositivityTheory.ThKG.Std

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {κ : Type} [Fintype κ] [DecidableEq κ]

def ind (c : k) (x : k) : ℂ := if valuation k x ≤ valuation k c then 1 else 0

def wt (P : Finset κ) (Z : κ → k) : ℂ := ∏ p, if p ∈ P then 1 else ind 1 (Z p)

def cut (P : Finset κ) (Z : κ → k) : κ → k := fun p => if p ∈ P then Z p else 0

def one (κ : Type) [Fintype κ] (Z : κ → k) : ℂ := ∏ p, ind 1 (Z p)

theorem ind_add {c x y : k} (hy : valuation k y ≤ valuation k c) : ind c (x + y) = ind c x := by
  unfold ind
  refine if_congr ⟨fun h => ?_, fun h => Valuation.map_add_le _ h hy⟩ rfl rfl
  have := (valuation k).map_sub_le h hy
  rwa [add_sub_cancel_right] at this

theorem isClopen_ball {c : k} (hc : c ≠ 0) : IsClopen {x : k | valuation k x ≤ valuation k c} := by
  have := Valuation.isClopen_closedBall (v := valuation k) (r := (valuation k).restrict c) (by simpa using hc)
  simpa only [Valuation.restrict_le_iff] using this

theorem lc_ind {c : k} (hc : c ≠ 0) : IsLocallyConstant (ind c) := by
  have := (LocallyConstant.indicator (LocallyConstant.const k (1 : ℂ)) (isClopen_ball hc)).isLocallyConstant
  convert this using 1
  funext x
  simp [ind, Set.indicator]

theorem lc_prod {X ι : Type} [TopologicalSpace X] (s : Finset ι) {f : ι → X → ℂ} (h : ∀ i ∈ s, IsLocallyConstant (f i)) :
    IsLocallyConstant fun x => ∏ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact IsLocallyConstant.const _
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem ind_ne {c x : k} (h : ind c x ≠ 0) : valuation k x ≤ valuation k c := by
  by_contra h'; exact h (if_neg h')

theorem one_mem_SB : one κ ∈ GlobalTheory.WeilM.SB (κ → k) := by
  refine ⟨lc_prod _ fun p _ => (lc_ind one_ne_zero).comp_continuous (continuous_apply p), ?_⟩
  refine HasCompactSupport.intro (isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k (valuation k 1))
    fun x hx => ?_
  by_contra h
  exact hx fun p _ => ind_ne (Finset.prod_ne_zero_iff.1 h p (Finset.mem_univ _))

theorem lc_wt (P : Finset κ) : IsLocallyConstant (wt (k := k) P) :=
  lc_prod _ fun p _ => by
    by_cases h : p ∈ P
    · simp only [h, if_true]; exact IsLocallyConstant.const _
    · simp only [h, if_false]; exact (lc_ind one_ne_zero).comp_continuous (continuous_apply p)

theorem continuous_cut (P : Finset κ) : Continuous (cut (k := k) P) :=
  continuous_pi fun p => by
    by_cases h : p ∈ P
    · simpa [cut, h] using continuous_apply p
    · simpa [cut, h] using continuous_const

theorem cut_mem {P : Finset κ} {Φ : (κ → k) → ℂ} (hΦ : Φ ∈ GlobalTheory.WeilM.SB (κ → k)) :
    (fun Z => Φ (cut P Z) * wt P Z) ∈ GlobalTheory.WeilM.SB (κ → k) := by
  refine ⟨(hΦ.1.comp_continuous (continuous_cut P)).mul (lc_wt P), ?_⟩
  refine HasCompactSupport.intro (isCompact_univ_pi (s := fun p => if p ∈ P then (fun x : κ → k => x p) '' tsupport Φ else
    {x : k | valuation k x ≤ valuation k 1}) fun p => ?_) fun x hx => ?_
  · split_ifs
    · exact IsCompact.image hΦ.2 (continuous_apply p)
    · exact IsNonarchimedeanLocalField.isCompact_closedBall k _
  · by_contra h
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
    refine hx fun p _ => ?_
    by_cases hp : p ∈ P
    · simp only [if_pos hp]; exact ⟨cut P x, subset_tsupport _ h1, by simp [cut, hp]⟩
    · simp only [if_neg hp]
      have := Finset.prod_ne_zero_iff.1 h2 p (Finset.mem_univ _)
      rw [if_neg hp] at this
      exact ind_ne this

variable [SecondCountableTopology k] [MeasurableSpace k] [BorelSpace k]

structure IsVol (m : Measure k) : Prop where
  haar : m.IsAddHaarMeasure
  one : m {x | valuation k x ≤ valuation k 1} = 1

theorem integrable_SB {m : Measure k} (hm : IsVol m) {Φ : (κ → k) → ℂ} (hΦ : Φ ∈ GlobalTheory.WeilM.SB (κ → k)) :
    Integrable Φ (Measure.pi fun _ : κ => m) := by
  haveI := hm.haar
  exact hΦ.1.continuous.integrable_of_hasCompactSupport hΦ.2

theorem int_ind {m : Measure k} {c : k} (hc : c ≠ 0) :
    ∫ x, ind c x ∂m = (m.real {x | valuation k x ≤ valuation k c} : ℂ) := by
  have : ind c = Set.indicator {x : k | valuation k x ≤ valuation k c} fun _ => (1 : ℂ) := by
    funext x; simp [ind, Set.indicator]
  rw [this, integral_indicator (isClopen_ball hc).2.measurableSet]
  simp

theorem int_ind_one {m : Measure k} (hm : IsVol m) : ∫ x, ind 1 x ∂m = 1 := by
  rw [int_ind one_ne_zero, Measure.real, hm.one]; simp

structure IsPsi (ψ : AddChar k ℂ) : Prop where
  cont : Continuous ψ
  norm : ∀ x, ‖ψ x‖ = 1
  cond : ∀ x, (∀ y, valuation k y ≤ 1 → ψ (x * y) = 1) ↔ valuation k x ≤ 1

omit [SecondCountableTopology k] [MeasurableSpace k] [BorelSpace k] in
theorem IsPsi.triv {ψ : AddChar k ℂ} (h : IsPsi ψ) {x : k} (hx : valuation k x ≤ 1) : ψ x = 1 := by
  simpa using (h.cond x).2 hx 1 (by simp)

omit [SecondCountableTopology k] [MeasurableSpace k] [BorelSpace k] in
theorem IsPsi.ex {ψ : AddChar k ℂ} (h : IsPsi ψ) {x : k} (hx : ¬ valuation k x ≤ 1) : ∃ y, valuation k y ≤ 1 ∧ ψ (x * y) ≠ 1 := by
  by_contra h'
  push Not at h'
  exact hx ((h.cond x).1 h')

omit [SecondCountableTopology k] [MeasurableSpace k] [BorelSpace k] in
theorem IsPsi.ne {ψ : AddChar k ℂ} (h : IsPsi ψ) : ψ ≠ 1 := by
  rintro rfl
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif (k := k)
  have := (h.cond (ϖ⁻¹ : kˣ)).1 fun _ _ => rfl
  have h2 : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  rw [Units.val_inv_eq_inv_val, map_inv₀, inv_le_one₀ (zero_lt_iff.2 (by simp))] at this
  exact absurd this (not_le.2 h2)

omit [SecondCountableTopology k] [MeasurableSpace k] [BorelSpace k] [DecidableEq κ] in
theorem val_dot {x y : κ → k} (hx : ∀ p, valuation k (x p) ≤ 1) (hy : ∀ p, valuation k (y p) ≤ 1) : valuation k (x ⬝ᵥ y) ≤ 1 :=
  (valuation k).map_sum_le fun p _ => by rw [map_mul]; exact mul_le_one' (hx p) (hy p)

omit [SecondCountableTopology k] [MeasurableSpace k] [BorelSpace k] [DecidableEq κ] in
theorem one_add {x y : κ → k} (hy : ∀ p, valuation k (y p) ≤ 1) : one κ (x + y) = one κ x :=
  Finset.prod_congr rfl fun p _ => ind_add (by simpa using hy p)

omit [SecondCountableTopology k] [MeasurableSpace k] [BorelSpace k] [DecidableEq κ] in
theorem one_mul_psi {ψ : AddChar k ℂ} (h : IsPsi ψ) {x y : κ → k} (hy : ∀ p, valuation k (y p) ≤ 1) :
    ψ (x ⬝ᵥ y) * one κ x = one κ x := by
  by_cases h0 : one κ x = 0
  · rw [h0, mul_zero]
  · rw [h.triv (val_dot (fun p => by simpa using ind_ne (Finset.prod_ne_zero_iff.1 h0 p (Finset.mem_univ _))) hy), one_mul]

theorem evInt [Invertible (2 : k)] {m : Measure k} (hm : IsVol m) {ψ : AddChar k ℂ} (hψ : IsPsi ψ) (P : Finset κ)
    (l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ)
    (hT : ∀ Z : κ → k, (∀ p ∉ P, Z p = 0) → ∀ Φ ∈ GlobalTheory.WeilM.SB (κ → k), l (fun Y => Φ (Y + Z)) = l Φ)
    (hM : ∀ Z : κ → k, (∀ p ∈ P, Z p = 0) → ∀ Φ ∈ GlobalTheory.WeilM.SB (κ → k), l (fun Y => ψ (Y ⬝ᵥ Z) * Φ Y) = l Φ)
    (h1 : l (one κ) = 1) : ∀ Φ ∈ GlobalTheory.WeilM.SB (κ → k), l Φ = ∫ Z, Φ (cut P Z) * wt P Z ∂(Measure.pi fun _ : κ => m) := by
  haveI := hm.haar
  let l₀ : GlobalTheory.WeilM.SB (κ → k) →ₗ[ℂ] ℂ :=
    { toFun := fun Φ => ∫ Z, Φ.1 (cut P Z) * wt P Z ∂(Measure.pi fun _ : κ => m)
      map_add' := fun a b => by
        rw [← integral_add (integrable_SB hm (cut_mem a.2)) (integrable_SB hm (cut_mem b.2))]
        simp [add_mul]
      map_smul' := fun c a => by simp [← integral_const_mul, mul_assoc] }
  obtain ⟨l', hl'⟩ := l₀.exists_extend
  have e : ∀ Φ ∈ GlobalTheory.WeilM.SB (κ → k), l' Φ = ∫ Z, Φ (cut P Z) * wt P Z ∂(Measure.pi fun _ : κ => m) := fun Φ h =>
    LinearMap.congr_fun hl' ⟨Φ, h⟩
  have dot0 : ∀ Z Z' : κ → k, (∀ p ∉ P, Z p = 0) → (∀ p ∈ P, Z' p = 0) → Z ⬝ᵥ Z' = 0 := fun Z Z' a b =>
    Finset.sum_eq_zero fun p _ => by
      by_cases hp : p ∈ P
      · rw [b p hp, mul_zero]
      · rw [a p hp, zero_mul]
  have key := PositivityTheory.ThKH.Evl.core hψ.cont hψ.norm hψ.ne (one_mem_SB (κ := κ) (k := k))
    (fun h => by have := congrFun h 0; simp [one, ind] at this)
    {w | (∀ p ∉ P, w.1 p = 0) ∧ ∀ p ∈ P, w.2 p = 0} (l - l') ?_ ?_ ?_
  · intro Φ hΦ
    rw [← e Φ hΦ, ← sub_eq_zero]; exact key Φ hΦ
  · rintro ⟨Z, Z'⟩ ⟨a, b⟩ φ hφ
    have hs := PositivityTheory.ThKH.Evl.schr_mem hψ.cont (Z, Z') hφ
    have hs0 := PositivityTheory.ThKH.Evl.schr_mem hψ.cont (Z, 0) hφ
    have e0 : GlobalTheory.WeilM.schr ψ (Z, (0 : κ → k)) φ = fun Y => φ (Y + Z) := by funext x; simp [GlobalTheory.WeilM.schr]
    have e1 : GlobalTheory.WeilM.schr ψ (Z, Z') φ = fun Y => ψ (Y ⬝ᵥ Z') * φ (Y + Z) := by
      funext x; simp [GlobalTheory.WeilM.schr, dot0 Z Z' a b]
    rw [e0] at hs0
    simp only [LinearMap.sub_apply]
    rw [e _ hs, e φ hφ, e1, hM Z' b _ hs0, hT Z a φ hφ]
    congr 1
    rw [← integral_add_right_eq_self (fun Y => φ (cut P Y) * wt P Y) Z]
    congr 1
    funext Y
    beta_reduce
    rw [dot0 (cut P Y) Z' (fun p hp => if_neg hp) b, AddChar.map_zero_eq_one, one_mul]
    congr 1
    · congr 1
      funext p
      by_cases hp : p ∈ P
      · simp [cut, hp]
      · simp [cut, hp, show Z p = 0 from a p hp]
    · refine Finset.prod_congr rfl fun p _ => ?_
      by_cases hp : p ∈ P
      · simp [hp]
      · simp [hp, show Z p = 0 from a p hp]
  · intro w
    let b1 : κ → k := fun p => if p ∈ P then 0 else w.1 p
    let b2 : κ → k := cut P w.2
    refine ⟨(cut P w.1, fun p => if p ∈ P then 0 else w.2 p), ⟨fun p hp => if_neg hp, fun p hp => if_pos hp⟩, (b1, b2), ?_, ?_⟩
    · refine Prod.ext (funext fun p => ?_) (funext fun p => ?_) <;> by_cases hp : p ∈ P <;> simp [cut, b1, b2, hp]
    have d12 : b1 ⬝ᵥ b2 = 0 := by rw [dotProduct_comm]; exact dot0 _ _ (fun p hp => if_neg hp) fun p hp => if_pos hp
    by_cases c1 : ∀ p, valuation k (b1 p) ≤ 1
    · by_cases c2 : ∀ p, valuation k (b2 p) ≤ 1
      · refine Or.inl ⟨1, funext fun x => ?_⟩
        simp only [GlobalTheory.WeilM.schr, d12, mul_zero, add_zero, one_add c1, one_mul_psi hψ c2, one_smul]
      · push Not at c2
        obtain ⟨p, hp⟩ := c2
        obtain ⟨y, hy, hy'⟩ := hψ.ex (not_le.2 hp)
        have hP : p ∈ P := by by_contra h; simp [b2, cut, h] at hp
        refine Or.inr ⟨(Pi.single p y, 0), ⟨fun q hq => Pi.single_eq_of_ne (fun h : q = p => hq (h ▸ hP)) _, fun _ _ => rfl⟩,
          funext fun x => ?_, by simpa [mul_comm] using hy'⟩
        have : ∀ q, valuation k ((Pi.single p y : κ → k) q) ≤ 1 := fun q => by
          by_cases h : q = p
          · subst h; simpa using hy
          · simp [Pi.single_eq_of_ne h]
        simp [GlobalTheory.WeilM.schr, one_add this]
    · push Not at c1
      obtain ⟨p, hp⟩ := c1
      obtain ⟨y, hy, hy'⟩ := hψ.ex (not_le.2 hp)
      have hP : p ∉ P := by intro h; simp [b1, h] at hp
      refine Or.inr ⟨(0, Pi.single p (-y)), ⟨fun _ _ => rfl, fun q hq => Pi.single_eq_of_ne (fun h : q = p => hP (h ▸ hq)) _⟩,
        funext fun x => ?_, by simpa using hy'⟩
      have : ∀ q, valuation k ((Pi.single p (-y) : κ → k) q) ≤ 1 := fun q => by
        by_cases h : q = p
        · subst h; simpa using hy
        · simp [Pi.single_eq_of_ne h]
      simp only [GlobalTheory.WeilM.schr, zero_dotProduct, mul_zero, add_zero, one_mul_psi hψ this]
  · rw [LinearMap.sub_apply, h1, e _ one_mem_SB]
    have : (fun Z : κ → k => one κ (cut P Z) * wt P Z) = fun Z => ∏ p, ind 1 (Z p) := by
      funext Z
      rw [one, wt, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun p _ => ?_
      by_cases hp : p ∈ P <;> simp [cut, hp, ind]
    rw [this, integral_fintype_prod_eq_prod (fun _ : κ => ind (1 : k))]
    simp [int_ind_one hm]

end PositivityTheory.ThKG.Std
