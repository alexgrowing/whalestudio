import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContrFactor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEmbXMul
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option linter.unusedSectionVars false

noncomputable section
namespace GlobalTheory.LocFlat.UnramFlat
open GlobalTheory.RootEx.Unram GlobalTheory.LocFlat

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem coe_psi_sum {ι : Type} (ψ : AddChar k Circle) (s : Finset ι) (f : ι → k) :
    (ψ (∑ i ∈ s, f i) : ℂ) = ∏ i ∈ s, (ψ (f i) : ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddChar.map_zero_eq_one]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, Circle.coe_mul, ih]

theorem intM_add_of_disj {m m' : Type} {A B : Matrix m m' k} (h : ∀ r s, B r s = 0 ∨ A r s = 0) :
    IntM (A + B) ↔ IntM A ∧ IntM B := by
  constructor
  · intro hAB
    refine ⟨fun r s => ?_, fun r s => ?_⟩ <;> rcases h r s with h0 | h0
    · simpa [h0] using hAB r s
    · rw [h0]; exact zero_mem _
    · rw [h0]; exact zero_mem _
    · simpa [h0] using hAB r s
  · rintro ⟨hA, hB⟩ r s
    exact add_mem (hA r s) (hB r s)

variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c p : ℕ}

theorem intM_colAt (y : n → k) :
    IntM (colAt (k := k) n' c p y) ↔ ∀ i : Fin (c + 1), i.val + 1 = p → ∀ r, y r ∈ 𝒪[k] := by
  constructor
  · intro h i hi r
    simpa [colAt, hi] using h (Sum.inl r) (Sum.inr i)
  · intro h r s
    rcases r with r | r <;> rcases s with s | s
    · simp [colAt]
    · simp only [colAt, fromBlocks_apply₁₂, Matrix.of_apply]
      split_ifs with hs
      exacts [h s hs r, zero_mem _]
    · simp [colAt]
    · simp [colAt]

theorem intM_rowAt (u : n' → k) :
    IntM (rowAt (k := k) n c p u) ↔ ∀ l : Fin c, l.val + 1 = p → ∀ s, u s ∈ 𝒪[k] := by
  constructor
  · intro h l hl s
    simpa [rowAt, hl] using h (Sum.inr l) (Sum.inl s)
  · intro h r s
    rcases r with r | r <;> rcases s with s | s
    · simp [rowAt]
    · simp [rowAt]
    · simp only [rowAt, fromBlocks_apply₂₁, Matrix.of_apply]
      split_ifs with hs
      exacts [h r hs s, zero_mem _]
    · simp [rowAt]

theorem colAt_disj (x₀ : Matrix n n' k) (e) (y : n → k) (r : n ⊕ Fin c) (s : n' ⊕ Fin (c + 1)) :
    colAt n' c p y r s = 0 ∨ affPt (c := c) p x₀ e r s = 0 := by
  rcases r with r | r <;> rcases s with s | s
  · left; simp [colAt]
  · by_cases h : s.val + 1 = p
    · right
      subst h
      simp [affPt, basePt, Free]
    · left; simp [colAt, h]
  · left; simp [colAt]
  · left; simp [colAt]

theorem rowAt_disj (x₀ : Matrix n n' k) (e) (u : n' → k) (r : n ⊕ Fin c) (s : n' ⊕ Fin (c + 1)) :
    rowAt n c p u r s = 0 ∨ affPt (c := c) p x₀ e r s = 0 := by
  rcases r with r | r <;> rcases s with s | s
  · left; simp [rowAt]
  · left; simp [rowAt]
  · by_cases h : r.val + 1 = p
    · right
      subst h
      simp [affPt, basePt, Free]
    · left; simp [rowAt, h]
  · left; simp [rowAt]

end GlobalTheory.LocFlat.UnramFlat

namespace GlobalTheory.LocFlat.UnramFlat
open GlobalTheory.RootEx.Unram GlobalTheory.LocFlat

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

theorem flCol_intInd {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k} (hν : IsUnitVol ν) (p : ℕ) :
    flCol ψ ν p (Set.indicator {x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1) =
      (if p = 0 ∨ c + 1 < p then fun x => Set.indicator {x : Matrix n n' k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) x.toCols₁
        else Set.indicator {x | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1) := by
  classical
  funext x
  unfold flCol
  rw [opE_of_ite hψ hν _ x.toCols₁
    (IntM x.toCols₁ ∧ ∀ i : Fin (c + 1), i.val + 1 = p → ∀ r, x r (Sum.inr ()) ∈ 𝒪[k]) fun e => ?_]
  · by_cases hp : p = 0 ∨ c + 1 < p
    · rw [if_pos hp]
      by_cases hP : IntM x.toCols₁
      · rw [if_pos ⟨hP, fun i hi => by omega⟩,
          Set.indicator_of_mem (show x.toCols₁ ∈ {x : Matrix n n' k | ∀ r q, x r q ∈ 𝒪[k]} from hP)]
      · rw [if_neg (fun h => hP h.1),
          Set.indicator_of_notMem (show x.toCols₁ ∉ {x : Matrix n n' k | ∀ r q, x r q ∈ 𝒪[k]} from hP)]
    rw [if_neg hp]
    split_ifs with hP
    · rw [Set.indicator_of_mem (show x ∈ {x : Matrix n (n' ⊕ Unit) k | ∀ r q, x r q ∈ 𝒪[k]} from by
        rintro r (q | ⟨⟩)
        · exact hP.1 r q
        · exact hP.2 ⟨p - 1, by omega⟩ (by simp; omega) r)]
    · rw [Set.indicator_of_notMem (show x ∉ {x : Matrix n (n' ⊕ Unit) k | ∀ r q, x r q ∈ 𝒪[k]} from
        fun h => hP ⟨fun r q => h r (Sum.inl q), fun i _ r => h r (Sum.inr ())⟩)]
  · have key := (intM_add_of_disj (colAt_disj (p := p) x.toCols₁ e fun r => x r (Sum.inr ()))).trans
      (and_congr (intM_affPt (c := c) (p := p) x.toCols₁ e) (intM_colAt (n' := n') (c := c) (p := p) fun r => x r (Sum.inr ())))
    by_cases h : IntM (affPt (c := c) p x.toCols₁ e + colAt n' c p fun r => x r (Sum.inr ()))
    · rw [Set.indicator_of_mem (show _ ∈ {x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k | ∀ r q, x r q ∈ 𝒪[k]} from h),
        if_pos (by tauto)]
    · rw [Set.indicator_of_notMem (show _ ∉ {x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k | ∀ r q, x r q ∈ 𝒪[k]} from h),
        if_neg (by tauto)]

theorem flRow_intInd {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k} (hν : IsUnitVol ν) (p : ℕ)
    (hp1 : 1 ≤ p) (hpc : p ≤ c) :
    flRow ψ ν p (Set.indicator {x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1) =
      Set.indicator {x | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1 := by
  classical
  funext x
  unfold flRow
  rw [opE_of_ite hψ hν _ x.toRows₁
    (IntM x.toRows₁ ∧ ∀ l : Fin c, l.val + 1 = p → ∀ s, x (Sum.inr ()) s ∈ 𝒪[k]) fun e => ?_]
  · split_ifs with hP
    · rw [Set.indicator_of_mem (show x ∈ {x : Matrix (n ⊕ Unit) n' k | ∀ r q, x r q ∈ 𝒪[k]} from by
        rintro (r | ⟨⟩) q
        · exact hP.1 r q
        · exact hP.2 ⟨p - 1, by omega⟩ (by simp; omega) q)]
    · rw [Set.indicator_of_notMem (show x ∉ {x : Matrix (n ⊕ Unit) n' k | ∀ r q, x r q ∈ 𝒪[k]} from
        fun h => hP ⟨fun r q => h (Sum.inl r) q, fun l _ s => h (Sum.inr ()) s⟩)]
  · have key := (intM_add_of_disj (rowAt_disj (p := p) x.toRows₁ e (x (Sum.inr ())))).trans
      (and_congr (intM_affPt (c := c) (p := p) x.toRows₁ e) (intM_rowAt (n := n) (c := c) (p := p) (x (Sum.inr ()))))
    by_cases h : IntM (affPt (c := c) p x.toRows₁ e + rowAt n c p (x (Sum.inr ())))
    · rw [Set.indicator_of_mem (show _ ∈ {x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k | ∀ r q, x r q ∈ 𝒪[k]} from h),
        if_pos (by tauto)]
    · rw [Set.indicator_of_notMem (show _ ∉ {x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k | ∀ r q, x r q ∈ 𝒪[k]} from h),
        if_neg (by tauto)]

end GlobalTheory.LocFlat.UnramFlat

namespace GlobalTheory.LocFlat.UnramFlat
open GlobalTheory.RootEx.Unram GlobalTheory.LocFlat

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]

open Classical in

theorem integral_psi_O {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k} (hν : IsUnitVol ν) (a : k) :
    ∫ t, (if t ∈ 𝒪[k] then (1 : ℂ) else 0) * (ψ (-1 * (a * t)) : ℂ) ∂ν = if a ∈ 𝒪[k] then 1 else 0 := by
  haveI := hν.1
  have hO : MeasurableSet (𝒪[k] : Set k) := (Valuation.isOpen_integer (v := valuation k)).measurableSet
  by_cases ha : a ∈ 𝒪[k]
  · rw [if_pos ha]
    have : (fun t => (if t ∈ 𝒪[k] then (1 : ℂ) else 0) * (ψ (-1 * (a * t)) : ℂ)) =
        Set.indicator (𝒪[k] : Set k) (fun _ => 1) := by
      funext t
      by_cases ht : t ∈ 𝒪[k]
      · rw [if_pos ht, Set.indicator_of_mem (show t ∈ (𝒪[k] : Set k) from ht),
          psi_eq_one hψ (by simpa using neg_mem (mul_mem ha ht))]
        simp
      · rw [if_neg ht, Set.indicator_of_notMem (show t ∉ (𝒪[k] : Set k) from ht), zero_mul]
    rw [this, integral_indicator_const _ hO]
    simp [Measure.real, hν.2]
  · rw [if_neg ha]
    obtain ⟨t₀, ht₀, hne⟩ : ∃ t₀ ∈ 𝒪[k], ψ (t₀ * (-a)) ≠ 1 := by
      by_contra h
      push_neg at h
      exact ha (by simpa using neg_mem (mem_of_psi hψ h))
    set F : k → ℂ := fun t => (if t ∈ 𝒪[k] then (1 : ℂ) else 0) * (ψ (-1 * (a * t)) : ℂ) with hF
    have hFt : ∀ t, F (t₀ + t) = (ψ (t₀ * (-a)) : ℂ) * F t := by
      intro t
      simp only [hF]
      have hm : t₀ + t ∈ 𝒪[k] ↔ t ∈ 𝒪[k] :=
        ⟨fun h => by simpa using sub_mem h ht₀, fun h => add_mem ht₀ h⟩
      rw [if_congr hm rfl rfl, show -1 * (a * (t₀ + t)) = t₀ * (-a) + -1 * (a * t) by ring,
        AddChar.map_add_eq_mul, Circle.coe_mul]
      ring
    have hI := integral_add_left_eq_self (μ := ν) F t₀
    simp_rw [hFt] at hI
    rw [integral_const_mul] at hI
    have hne' : (ψ (t₀ * (-a)) : ℂ) ≠ 1 := fun h => hne (Circle.coe_inj.1 (by simpa using h))
    have h3 : ((ψ (t₀ * (-a)) : ℂ) - 1) * ∫ t, F t ∂ν = 0 := by rw [sub_mul, hI]; ring
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd (sub_eq_zero.1 h) hne'
    · exact h

variable {n : Type} [Fintype n] [DecidableEq n]

open Classical in

theorem integral_psi_box {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k} (hν : IsUnitVol ν) (u : n → k) :
    ∫ y, (if ∀ r, y r ∈ 𝒪[k] then (1 : ℂ) else 0) * (ψ (-1 * (u ⬝ᵥ y)) : ℂ) ∂(Measure.pi fun _ : n => ν) =
      if ∀ r, u r ∈ 𝒪[k] then 1 else 0 := by
  haveI := hν.1
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have e : (fun y : n → k => (if ∀ r, y r ∈ 𝒪[k] then (1 : ℂ) else 0) * (ψ (-1 * (u ⬝ᵥ y)) : ℂ)) =
      fun y => ∏ r, (fun r t => (if t ∈ 𝒪[k] then (1 : ℂ) else 0) * (ψ (-1 * (u r * t)) : ℂ)) r (y r) := by
    funext y
    simp only [Finset.prod_mul_distrib, Finset.prod_boole, Finset.mem_univ, true_imp_iff]
    rw [← coe_psi_sum, dotProduct, Finset.mul_sum]
  rw [e, integral_fintype_prod_eq_prod (fun r t => (if t ∈ 𝒪[k] then (1 : ℂ) else 0) * (ψ (-1 * (u r * t)) : ℂ))]
  simp only [integral_psi_O hψ hν, Finset.prod_boole, Finset.mem_univ, true_imp_iff]

open Classical in
theorem ind_eq_ite {m m' : Type} (x : Matrix m m' k) :
    Set.indicator {x : Matrix m m' k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => (1 : ℂ)) x = if IntM x then 1 else 0 := by
  rw [Set.indicator_apply]
  exact if_congr Iff.rfl rfl rfl

variable {n' n'' : Type} [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n'']

theorem contr_intInd {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k} (hν : IsUnitVol ν)
    (q : Matrix n n' k × Matrix n'' n k) :
    contr ψ ν (Set.indicator {x : Matrix n (n' ⊕ Unit) k | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1)
      (Set.indicator {x : Matrix (n'' ⊕ Unit) n k | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1) q =
    Set.indicator {x : Matrix n n' k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) q.1 *
      Set.indicator {x : Matrix n'' n k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) q.2 := by
  classical
  have h1 : ∀ y : n → k, IntM (fromCols q.1 (Matrix.of fun r (_ : Unit) => y r)) ↔ IntM q.1 ∧ ∀ r, y r ∈ 𝒪[k] := by
    intro y
    constructor
    · intro h
      exact ⟨fun r s => by simpa using h r (Sum.inl s), fun r => by simpa using h r (Sum.inr ())⟩
    · rintro ⟨h, h'⟩ r (s | ⟨⟩)
      · simpa using h r s
      · simpa using h' r
  have h2 : ∀ u : n → k, IntM (fromRows q.2 (Matrix.of fun (_ : Unit) => u)) ↔ IntM q.2 ∧ ∀ r, u r ∈ 𝒪[k] := by
    intro u
    constructor
    · intro h
      exact ⟨fun r s => by simpa using h (Sum.inl r) s, fun r => by simpa using h (Sum.inr ()) r⟩
    · rintro ⟨h, h'⟩ (r | ⟨⟩) s
      · simpa using h r s
      · simpa using h' s
  have hhat : ∀ u, hat ψ ν (-1) (fun y => Set.indicator {x : Matrix n (n' ⊕ Unit) k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => (1 : ℂ))
      (fromCols q.1 (Matrix.of fun r _ => y r))) u =
      (if IntM q.1 then 1 else 0) * (if ∀ r, u r ∈ 𝒪[k] then 1 else 0) := by
    intro u
    rw [← integral_psi_box hψ hν u, ← integral_const_mul]
    unfold hat
    congr 1
    funext y
    beta_reduce
    rw [ind_eq_ite, if_congr (h1 y) rfl rfl]
    by_cases a : IntM q.1 <;> by_cases b : ∀ r, y r ∈ 𝒪[k] <;> simp [a, b]
  unfold contr
  refine (integral_congr_ae (μ := Measure.pi fun _ : n => ν)
    (g := fun u => ((if IntM q.1 then (1 : ℂ) else 0) * (if IntM q.2 then 1 else 0)) *
      ((if ∀ r, u r ∈ 𝒪[k] then (1 : ℂ) else 0) * (ψ (-1 * ((0 : n → k) ⬝ᵥ u)) : ℂ)))
    (Filter.Eventually.of_forall fun u => ?_)).trans ?_
  · dsimp only
    rw [hhat, ind_eq_ite, if_congr (h2 u) rfl rfl]
    simp only [zero_dotProduct, mul_zero, AddChar.map_zero_eq_one, Circle.coe_one, mul_one]
    by_cases a : IntM q.1 <;> by_cases b : IntM q.2 <;> by_cases c : ∀ r, u r ∈ 𝒪[k] <;> simp [a, b, c]
  · rw [integral_const_mul, integral_psi_box hψ hν 0, ind_eq_ite, ind_eq_ite]
    simp

end GlobalTheory.LocFlat.UnramFlat

open GlobalTheory.LocFlat.UnramFlat in

theorem GlobalTheory.LocFlat.flat_contr_intIndicator : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), HasConductor ψ 1 → IsUnitVol ν → ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (c p : ℕ), GlobalTheory.LocFlat.flCol ψ ν p (Set.indicator {x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1) = (if p = 0 ∨ c + 1 < p then fun x => Set.indicator {x : Matrix n n' k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) x.toCols₁ else Set.indicator {x | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1) ∧ (1 ≤ p → p ≤ c → GlobalTheory.LocFlat.flRow ψ ν p (Set.indicator {x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1) = Set.indicator {x | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1) ∧ ∀ q, GlobalTheory.LocFlat.contr ψ ν (Set.indicator {x : Matrix n (n' ⊕ Unit) k | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1) (Set.indicator {x : Matrix (n'' ⊕ Unit) n k | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1) q = Set.indicator {x : Matrix n n' k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) q.1 * Set.indicator {x : Matrix n'' n k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) q.2 := by
  intro k _ _ _ _ _ _ ψ ν hψ hν n n' n'' _ _ _ _ _ _ c p
  exact ⟨flCol_intInd hψ hν p, fun h1 h2 => flRow_intInd hψ hν p h1 h2, fun q => contr_intInd hψ hν q⟩
