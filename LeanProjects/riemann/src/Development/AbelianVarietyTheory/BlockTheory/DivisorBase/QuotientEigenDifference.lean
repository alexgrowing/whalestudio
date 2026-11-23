import Mathlib

open scoped NNReal

namespace GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference

noncomputable section Defs

variable {C : Type} [Field C] (w : Valuation C ℝ≥0)

noncomputable def addVal (ℓ c : C) : ℝ := Real.log (w c : ℝ) / Real.log (w ℓ : ℝ)

def HasVal (ℓ c : C) (y : ℝ) : Prop := c ≠ 0 ∧ addVal w ℓ c = y

def IsLatticeBasis {W : Type} [AddCommGroup W] [Module C W] [Module w.valuationSubring W]
    [IsScalarTower w.valuationSubring C W] {n : ℕ} (x : Fin n → W)
    (X : Submodule w.valuationSubring W) : Prop :=
  LinearIndependent C x ∧ Submodule.span w.valuationSubring (Set.range x) = X

def HasLength (ℓ : C) {W : Type} [AddCommGroup W] [Module C W] [Module w.valuationSubring W]
    [IsScalarTower w.valuationSubring C W] (X X' : Submodule w.valuationSubring W) (t : ℝ) :
    Prop :=
  X' ≤ X ∧ ∃ (n : ℕ) (x x' : Fin n → W) (M : Matrix (Fin n) (Fin n) C),
    IsLatticeBasis w x X ∧ IsLatticeBasis w x' X' ∧ (∀ i, x' i = ∑ j, M i j • x j) ∧
      HasVal w ℓ M.det t

def DetRel (ℓ : C) {p q : ℕ} (F : Submodule C (Fin (p + q) → C))
    (X : Submodule w.valuationSubring (Fin (p + q) → C))
    (L : Submodule w.valuationSubring ((Fin (p + q) → C) ⧸ F))
    (M : Submodule w.valuationSubring (Fin (p + q) → C)) (y : ℝ) : Prop :=
  ∃ (x : Fin (p + q) → Fin (p + q) → C) (u : Fin p → Fin (p + q) → C)
    (m : Fin q → Fin (p + q) → C) (c : C),
    IsLatticeBasis w x X ∧ IsLatticeBasis w (fun i => F.mkQ (u i)) L ∧ IsLatticeBasis w m M ∧
      (∀ i, m i ∈ F) ∧ HasVal w ℓ c y ∧
      (Matrix.of x).det = c * (Matrix.of (Fin.append u m)).det

variable {w}

def eigenSub {S : Type} [DecidableEq S] {W : S → Type} [∀ s, AddCommGroup (W s)]
    [∀ s, Module w.valuationSubring (W s)] (X : Submodule w.valuationSubring (∀ s, W s))
    (τ : S) : Submodule w.valuationSubring (W τ) :=
  X.comap (LinearMap.single w.valuationSubring W τ)

def eigenQuot {S : Type} {W : S → Type} [∀ s, AddCommGroup (W s)]
    [∀ s, Module w.valuationSubring (W s)] (X : Submodule w.valuationSubring (∀ s, W s))
    (τ : S) : Submodule w.valuationSubring (W τ) :=
  X.map (LinearMap.proj τ)

def freeLattice {S : Type} (a : S → w.valuationSubring) (r : ℕ) :
    Submodule w.valuationSubring (S → Fin r → C) where
  carrier := {x | ∀ i, ∃ f : Polynomial w.valuationSubring, ∀ s,
    x s i = ((f.eval (a s) : w.valuationSubring) : C)}
  zero_mem' := fun _ => ⟨0, fun _ => by simp⟩
  add_mem' := by
    intro x y hx hy i
    obtain ⟨f, hf⟩ := hx i
    obtain ⟨g, hg⟩ := hy i
    exact ⟨f + g, fun s => by simp [hf s, hg s]⟩
  smul_mem' := by
    intro c x hx i
    obtain ⟨f, hf⟩ := hx i
    exact ⟨Polynomial.C c * f, fun s => by simp [hf s, Algebra.smul_def]⟩

def unif {S : Type} {r : ℕ} (a : S → w.valuationSubring) (x : S → Fin r → C) :
    S → Fin r → C := fun s => (a s : C) • x s

def filSpace {S : Type} {r : ℕ} (Fil : Submodule w.valuationSubring (S → Fin r → C)) (s : S) :
    Submodule C (Fin r → C) :=
  Submodule.span C (eigenQuot (W := fun _ => Fin r → C) Fil s : Set (Fin r → C))

def quotMap {r : ℕ} (F : Submodule C (Fin r → C)) :
    (Fin r → C) →ₗ[w.valuationSubring] ((Fin r → C) ⧸ F) :=
  F.mkQ.restrictScalars w.valuationSubring

def lie {S : Type} {r : ℕ} (H Fil : Submodule w.valuationSubring (S → Fin r → C)) :
    Submodule w.valuationSubring (∀ s, (Fin r → C) ⧸ filSpace Fil s) :=
  H.map (LinearMap.pi fun s => quotMap (filSpace Fil s) ∘ₗ LinearMap.proj s)

def dualLie {S : Type} [DecidableEq S] {r : ℕ}
    (β : (S → Fin r → C) →ₗ[C] (S → Fin r → C) →ₗ[C] C)
    (Fil H' Fil' : Submodule w.valuationSubring (S → Fin r → C)) (τ : S) :
    Submodule w.valuationSubring (Fin r → C) where
  carrier := {x | x ∈ filSpace Fil τ ∧ ∀ y : Fin r → C,
    (filSpace Fil' τ).mkQ y ∈ eigenSub (lie H' Fil') τ →
      β (Pi.single τ x) (Pi.single τ y) ∈ w.valuationSubring}
  zero_mem' := ⟨zero_mem _, fun y _ => by simp⟩
  add_mem' := by
    rintro x x' ⟨hx, h⟩ ⟨hx', h'⟩
    refine ⟨add_mem hx hx', fun y hy => ?_⟩
    rw [Pi.single_add, map_add, LinearMap.add_apply]
    exact add_mem (h y hy) (h' y hy)
  smul_mem' := by
    rintro c x ⟨hx, h⟩
    refine ⟨Submodule.smul_mem _ (c : C) hx, fun y hy => ?_⟩
    have : (Pi.single τ (c • x) : S → Fin r → C) = (c : C) • (Pi.single τ x : S → Fin r → C) :=
      Pi.single_smul' τ (c : C) x
    rw [this, map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact mul_mem c.2 (h y hy)

structure IsFiltration {S : Type} {r : ℕ} (a : S → w.valuationSubring)
    (Fil : Submodule w.valuationSubring (S → Fin r → C)) : Prop where
  le : Fil ≤ freeLattice a r
  stable : ∀ x ∈ Fil, unif a x ∈ Fil
  saturated : ∀ x ∈ freeLattice a r, ∀ c : w.valuationSubring, c ≠ 0 → c • x ∈ Fil → x ∈ Fil

structure IsDualDatum {S : Type} {r : ℕ} (a : S → w.valuationSubring)
    (β : (S → Fin r → C) →ₗ[C] (S → Fin r → C) →ₗ[C] C)
    (Fil Fil' : Submodule w.valuationSubring (S → Fin r → C)) : Prop where
  fil : IsFiltration a Fil
  fil' : IsFiltration a Fil'
  adjoint : ∀ x y, β (unif a x) y = β x (unif a y)
  perfect_left : ∀ x, x ∈ freeLattice a r ↔
    ∀ y ∈ freeLattice a r, β x y ∈ w.valuationSubring
  perfect_right : ∀ y, y ∈ freeLattice a r ↔
    ∀ x ∈ freeLattice a r, β x y ∈ w.valuationSubring
  ann_left : ∀ x ∈ freeLattice a r, (x ∈ Fil ↔ ∀ y ∈ Fil', β x y = 0)
  ann_right : ∀ y ∈ freeLattice a r, (y ∈ Fil' ↔ ∀ x ∈ Fil, β x y = 0)

def diffGen {S : Type} [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (τ : S) :
    w.valuationSubring := ∏ s ∈ Finset.univ.erase τ, (a τ - a s)

def flatLattice {S : Type} {r : ℕ} (a : S → w.valuationSubring) (τ : S)
    (d : w.valuationSubring) : Submodule w.valuationSubring (Fin r → C) :=
  (eigenQuot (W := fun _ => Fin r → C) (freeLattice a r) τ).map
    (LinearMap.lsmul w.valuationSubring (Fin r → C) d)

end Defs

section Stmt

variable {C : Type} [Field C] (w : Valuation C ℝ≥0) (ℓ : C)

def TypeOne : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (p q : ℕ)
    (β : (S → Fin (p + q) → C) →ₗ[C] (S → Fin (p + q) → C) →ₗ[C] C)
    (Fil Fil' : Submodule w.valuationSubring (S → Fin (p + q) → C)) (τ : S),
    Function.Injective a → IsDualDatum a β Fil Fil' →
    (∀ s, Module.finrank C (filSpace Fil s) = q) →
    let H := freeLattice a (p + q)
    let vd := addVal w ℓ (diffGen a τ : C)
    let HH := flatLattice (r := p + q) a τ (diffGen a τ)
    let FilSub := eigenSub (W := fun _ => Fin (p + q) → C) Fil τ
    let FilQuot := eigenQuot (W := fun _ => Fin (p + q) → C) Fil τ
    HH = eigenSub (W := fun _ => Fin (p + q) → C) H τ ∧
    DetRel w ℓ (filSpace Fil τ) HH (eigenSub (lie H Fil) τ) (dualLie β Fil H Fil' τ)
      ((q : ℝ) * vd) ∧
    HH ⊓ LinearMap.ker (quotMap (filSpace Fil τ)) = FilSub ∧
    ∃ t : ℝ, HasLength w ℓ FilQuot FilSub t ∧
      HasLength w ℓ (eigenSub (lie H Fil) τ) (HH.map (quotMap (filSpace Fil τ)))
        ((q : ℝ) * vd - t) ∧
      0 ≤ (q : ℝ) * vd - t ∧ (q : ℝ) * vd - t ≤ (q : ℝ) * vd

def TypeTwo : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (p q : ℕ)
    (β : (S → Fin (p + q) → C) →ₗ[C] (S → Fin (p + q) → C) →ₗ[C] C)
    (Fil Fil' : Submodule w.valuationSubring (S → Fin (p + q) → C)) (τ τ' : S),
    τ ≠ τ' → (∀ s, s = τ ∨ s = τ') →
    HasVal w ℓ ((a τ : C) - (a τ' : C)) (1 / 2) → IsDualDatum a β Fil Fil' →
    Module.finrank C (filSpace Fil τ) = q → Module.finrank C (filSpace Fil τ') = p →
    let H := freeLattice a (p + q)
    let HH := flatLattice (r := p + q) a τ 1
    let FilSub := eigenSub (W := fun _ => Fin (p + q) → C) Fil τ
    let FilQuot := eigenQuot (W := fun _ => Fin (p + q) → C) Fil τ
    HH = eigenQuot (W := fun _ => Fin (p + q) → C) H τ ∧
    DetRel w ℓ (filSpace Fil τ) HH (eigenSub (lie H Fil) τ) (dualLie β Fil H Fil' τ)
      (-((q : ℝ) / 2)) ∧
    HH.map (quotMap (filSpace Fil τ)) = eigenQuot (lie H Fil) τ ∧
    (∃ la : ℝ, HasLength w ℓ (eigenQuot (lie H Fil) τ) (eigenSub (lie H Fil) τ) la ∧
      0 ≤ la ∧ la ≤ (q : ℝ) / 2 ∧
      HasLength w ℓ (HH ⊓ LinearMap.ker (quotMap (filSpace Fil τ))) FilQuot
        ((q : ℝ) / 2 - la)) ∧
    ∃ t : ℝ, HasLength w ℓ FilQuot FilSub t ∧ t ≤ (q : ℝ) / 2

def Unramified : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (p q : ℕ)
    (β : (S → Fin (p + q) → C) →ₗ[C] (S → Fin (p + q) → C) →ₗ[C] C)
    (Fil Fil' : Submodule w.valuationSubring (S → Fin (p + q) → C)) (τ : S),
    (∀ s, s = τ) → IsDualDatum a β Fil Fil' →
    Module.finrank C (filSpace Fil τ) = q →
    let H := freeLattice a (p + q)
    DetRel w ℓ (filSpace Fil τ) (flatLattice (r := p + q) a τ 1) (eigenSub (lie H Fil) τ)
      (dualLie β Fil H Fil' τ) 0

def ValuedFieldThreeCases : Prop := TypeOne w ℓ ∧ TypeTwo w ℓ ∧ Unramified w ℓ

end Stmt

def Stmt : Prop :=
  ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (ℓ : C), 0 < w ℓ → w ℓ < 1 → ValuedFieldThreeCases w ℓ

def PadicComplexThreeCases : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], ValuedFieldThreeCases (PadicComplex.valued l).v (l : ℂ_[l])

theorem stmtPadic_of_stmt (h : Stmt) : PadicComplexThreeCases := by
  intro l hl
  have h1 : (1 : ℝ≥0) < (l : ℝ≥0) := by exact_mod_cast hl.out.one_lt
  have h0 : (0 : ℝ≥0) < (l : ℝ≥0) := lt_trans zero_lt_one h1
  refine h _ _ _ ?_ ?_
  · rw [PadicComplex.valuation_p]; positivity
  · rw [PadicComplex.valuation_p, div_lt_one h0]; exact h1

noncomputable section Example

variable {C : Type} [Field C] {w : Valuation C ℝ≥0}

theorem mem_freeLattice_bool (a : Bool → w.valuationSubring) (h : a true ≠ a false) {r : ℕ}
    (x : Bool → Fin r → C) :
    x ∈ freeLattice a r ↔ ∀ i, x false i ∈ w.valuationSubring ∧
      (x true i - x false i) / ((a true : C) - a false) ∈ w.valuationSubring := by
  have hδ : (a true : C) - a false ≠ 0 := sub_ne_zero.2 fun e => h (Subtype.ext e)
  constructor
  · intro hx i
    obtain ⟨f, hf⟩ := hx i
    obtain ⟨t, ht⟩ := Polynomial.sub_dvd_eval_sub (a true) (a false) f
    refine ⟨by rw [hf]; exact Subtype.prop _, ?_⟩
    have := congrArg (fun z : w.valuationSubring => (z : C)) ht
    push_cast at this
    rw [hf, hf, this, mul_div_cancel_left₀ _ hδ]
    exact t.2
  · intro hx i
    obtain ⟨h0, h1⟩ := hx i
    refine ⟨Polynomial.C ⟨_, h0⟩ + Polynomial.C ⟨_, h1⟩ * (Polynomial.X - Polynomial.C (a false)),
      fun s => ?_⟩
    cases s
    · simp
    · simp [div_mul_cancel₀ _ hδ]

def resPair (a : Bool → w.valuationSubring) (r : ℕ) :
    (Bool → Fin r → C) →ₗ[C] (Bool → Fin r → C) →ₗ[C] C :=
  LinearMap.mk₂ C
    (fun x y => ∑ i, (x true i * y true i - x false i * y false i) / ((a true : C) - a false))
    (fun x x' y => by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by simp only [Pi.add_apply]; ring)
    (fun c x y => by
      rw [smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun x y y' => by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by simp only [Pi.add_apply]; ring)
    (fun c x y => by
      rw [smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring)

theorem resPair_apply (a : Bool → w.valuationSubring) (r : ℕ) (x y : Bool → Fin r → C) :
    resPair a r x y =
      ∑ i, (x true i * y true i - x false i * y false i) / ((a true : C) - a false) := rfl

theorem resPair_comm (a : Bool → w.valuationSubring) (r : ℕ) (x y : Bool → Fin r → C) :
    resPair a r x y = resPair a r y x := by
  rw [resPair_apply, resPair_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem resPair_perfect (a : Bool → w.valuationSubring) (h : a true ≠ a false) (r : ℕ)
    (x : Bool → Fin r → C) :
    x ∈ freeLattice a r ↔ ∀ y ∈ freeLattice a r, resPair a r x y ∈ w.valuationSubring := by
  have hδ : (a true : C) - a false ≠ 0 := sub_ne_zero.2 fun e => h (Subtype.ext e)
  have hδm : (a true : C) - a false ∈ w.valuationSubring := sub_mem (a true).2 (a false).2
  constructor
  · intro hx y hy
    rw [mem_freeLattice_bool a h] at hx hy
    rw [resPair_apply]
    refine sum_mem fun i _ => ?_
    obtain ⟨x0, x1⟩ := hx i
    obtain ⟨y0, y1⟩ := hy i
    have : (x true i * y true i - x false i * y false i) / ((a true : C) - a false) =
        (x true i - x false i) / ((a true : C) - a false) * y false i +
        x false i * ((y true i - y false i) / ((a true : C) - a false)) +
        ((a true : C) - a false) * ((x true i - x false i) / ((a true : C) - a false)) *
          ((y true i - y false i) / ((a true : C) - a false)) := by
      field_simp; ring
    rw [this]
    exact add_mem (add_mem (mul_mem x1 y0) (mul_mem x0 y1)) (mul_mem (mul_mem hδm x1) y1)
  · intro hx
    rw [mem_freeLattice_bool a h]
    intro i
    have h1 := hx (fun _ => Pi.single i 1) ((mem_freeLattice_bool a h _).2 fun j => by
      by_cases e : j = i <;> simp [e])
    have h2 := hx (fun s => Pi.single i (if s then (a true : C) - a false else 0))
      ((mem_freeLattice_bool a h _).2 fun j => by
        by_cases e : j = i <;> simp [e, hδ])
    rw [resPair_apply, Finset.sum_eq_single i (fun j _ e => by simp [e]) (by simp)] at h1 h2
    simp only [Pi.single_eq_same, mul_one] at h1
    simp only [Pi.single_eq_same, if_true, Bool.false_eq_true, if_false, mul_zero, sub_zero,
      mul_div_cancel_right₀ _ hδ] at h2
    refine ⟨?_, h1⟩
    have : x false i = x true i - ((a true : C) - a false) *
        ((x true i - x false i) / ((a true : C) - a false)) := by field_simp; ring
    rw [this]
    exact sub_mem h2 (mul_mem hδm h1)

def coordFil (a : Bool → w.valuationSubring) (κ : Bool → Fin 2) :
    Submodule w.valuationSubring (Bool → Fin 2 → C) where
  carrier := {x | x ∈ freeLattice a 2 ∧ ∀ s, x s (κ s) = 0}
  zero_mem' := ⟨zero_mem _, fun _ => rfl⟩
  add_mem' := fun hx hy => ⟨add_mem hx.1 hy.1, fun s => by simp [hx.2 s, hy.2 s]⟩
  smul_mem' := fun c _ hx => ⟨Submodule.smul_mem _ c hx.1, fun s => by simp [hx.2 s]⟩

theorem coordFil_isFiltration (a : Bool → w.valuationSubring) (κ : Bool → Fin 2) :
    IsFiltration a (coordFil a κ) where
  le := fun _ hx => hx.1
  stable := by
    rintro x ⟨hx, h0⟩
    refine ⟨fun i => ?_, fun s => by simp [unif, h0 s]⟩
    obtain ⟨f, hf⟩ := hx i
    exact ⟨Polynomial.X * f, fun s => by simp [unif, hf s, mul_comm]⟩
  saturated := by
    rintro x hx c hc ⟨-, h0⟩
    refine ⟨hx, fun s => ?_⟩
    have := h0 s
    have hc' : (c : C) ≠ 0 := fun e => hc (Subtype.ext e)
    simpa [Algebra.smul_def, hc, hc'] using this

theorem single_mem_coordFil (a : Bool → w.valuationSubring) (h : a true ≠ a false)
    (κ : Bool → Fin 2) (s : Bool) (i : Fin 2) (hi : i ≠ κ s) :
    (Pi.single s (Pi.single i ((a true : C) - a false)) : Bool → Fin 2 → C) ∈ coordFil a κ := by
  have hδ : (a true : C) - a false ≠ 0 := sub_ne_zero.2 fun e => h (Subtype.ext e)
  have hδm : (a true : C) - a false ∈ w.valuationSubring := sub_mem (a true).2 (a false).2
  refine ⟨(mem_freeLattice_bool a h _).2 fun j => ?_, fun t => ?_⟩
  · have hsw : w ((a false : C) - a true) = w ((a true : C) - a false) := w.map_sub_swap _ _
    cases s <;> by_cases e : j = i <;> simp [e, hδ, hδm, neg_div, hsw]
  · by_cases e : t = s
    · subst e; simp [hi.symm]
    · simp [e]

theorem coordFil_ann (a : Bool → w.valuationSubring) (h : a true ≠ a false)
    (κ κ' : Bool → Fin 2) (hκ : ∀ s, κ s ≠ κ' s) (x : Bool → Fin 2 → C)
    (hx : x ∈ freeLattice a 2) :
    x ∈ coordFil a κ ↔ ∀ y ∈ coordFil a κ', resPair a 2 x y = 0 := by
  have hδ : (a true : C) - a false ≠ 0 := sub_ne_zero.2 fun e => h (Subtype.ext e)
  constructor
  · rintro ⟨-, h0⟩ y ⟨-, h1⟩
    have key : ∀ s i, x s i * y s i = 0 := by
      intro s i
      by_cases e : i = κ s
      · rw [e, h0, zero_mul]
      · have : i = κ' s := by
          have := hκ s
          omega
        rw [this, h1, mul_zero]
    rw [resPair_apply]
    simp [key]
  · intro H
    refine ⟨hx, fun s => ?_⟩
    have := H _ (single_mem_coordFil a h κ' s (κ s) (hκ s))
    rw [resPair_apply, Finset.sum_eq_single (κ s)
      (fun j _ e => by cases s <;> simp [e]) (by simp)] at this
    cases s <;> simpa [hδ] using this

theorem finrank_filSpace_coordFil (a : Bool → w.valuationSubring) (h : a true ≠ a false)
    (κ κ' : Bool → Fin 2) (hκ : ∀ s, κ s ≠ κ' s) (s : Bool) :
    Module.finrank C (filSpace (coordFil a κ) s) = 1 := by
  have hδ : (a true : C) - a false ≠ 0 := sub_ne_zero.2 fun e => h (Subtype.ext e)
  have hne : (Pi.single (κ' s) ((a true : C) - a false) : Fin 2 → C) ≠ 0 := by
    intro e
    have := congrFun e (κ' s)
    simp [hδ] at this
  have : filSpace (coordFil a κ) s =
      Submodule.span C {(Pi.single (κ' s) ((a true : C) - a false) : Fin 2 → C)} := by
    apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨x, ⟨-, h0⟩, rfl⟩
      refine Submodule.mem_span_singleton.2 ⟨x s (κ' s) / ((a true : C) - a false), ?_⟩
      funext i
      by_cases e : i = κ' s
      · simp [e, hδ]
      · have : i = κ s := by
          have := hκ s
          omega
        rw [this]
        simp [hκ s, h0 s]
    · refine Submodule.span_mono ?_
      rintro _ rfl
      exact ⟨_, single_mem_coordFil a h κ s (κ' s) (hκ s).symm, by simp⟩
  rw [this, finrank_span_singleton hne]

theorem exists_isDualDatum (a : Bool → w.valuationSubring) (h : a true ≠ a false) :
    IsDualDatum a (resPair a (1 + 1)) (coordFil a fun s => if s then 0 else 1)
        (coordFil a fun s => if s then 1 else 0) ∧
      ∀ s, Module.finrank C (filSpace (coordFil a fun s => if s then 0 else 1) s) = 1 := by
  have hκ : ∀ s : Bool, (if s then (0 : Fin 2) else 1) ≠ (if s then (1 : Fin 2) else 0) := by
    decide
  refine ⟨⟨coordFil_isFiltration a _, coordFil_isFiltration a _, fun x y => ?_,
    resPair_perfect a h _, fun y => ?_, fun x hx => coordFil_ann a h _ _ hκ x hx,
    fun y hy => ?_⟩, finrank_filSpace_coordFil a h _ _ hκ⟩
  · rw [resPair_apply, resPair_apply]
    exact Finset.sum_congr rfl fun i _ => by simp only [unif, Pi.smul_apply, smul_eq_mul]; ring
  · simp only [resPair_comm a _ _ y]
    exact resPair_perfect a h _ y
  · simp only [resPair_comm a _ _ y]
    exact coordFil_ann a h _ _ (fun s => (hκ s).symm) y hy

end Example

end GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference
