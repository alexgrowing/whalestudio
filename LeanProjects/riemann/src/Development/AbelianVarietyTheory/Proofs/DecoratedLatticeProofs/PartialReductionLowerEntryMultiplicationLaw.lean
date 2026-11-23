import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChLApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatCompAffineMatrixStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralCoordinateShearHaarLocalFieldStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

noncomputable section
namespace GlobalTheory.PartRed.LowLaw

section Alg
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

omit [Fintype n'] [DecidableEq n'] in

theorem rowAdd_mul_apply (r l : Fin c) (a : k) (t : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)
    (p : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)) :
    ((fromBlocks 1 0 0 (transvection r l a) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * t) p q =
      t p q + if p = Sum.inr r then a * t (Sum.inr l) q else 0 := by
  rw [mul_apply]
  rcases p with p | p
  · simp [Fintype.sum_sum_type, one_apply]
  · simp [Fintype.sum_sum_type, transvection, add_mul, Finset.sum_add_distrib, one_apply, single_apply,
      ite_and, eq_comm]

theorem mem_trans {ρ : ℕ} {e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))} :
    e ∈ transSet ρ ↔ Free (ρ + 1) e ∧ ∀ i, e.2 = Sum.inr i → ρ < i.val := by simp [transSet]

theorem mem_fix {ρ : ℕ} {e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))} :
    e ∈ fixSet ρ ↔ (∃ i, e.2 = Sum.inr i ∧ i.val ≤ ρ ∧ ¬ Free (ρ + 1) e) ∨
      (∃ l s, e.1 = Sum.inr l ∧ ρ < l.val ∧ e.2 = Sum.inl s) := by simp [fixSet]

theorem mem_low {ρ : ℕ} {e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))} :
    e ∈ lowSet ρ ↔ ∃ (l : Fin c) (i : Fin (c + 1)), e = (Sum.inr l, Sum.inr i) ∧ ρ < i.val ∧ i.val ≤ l.val := by simp [lowSet]

theorem fill_row_zero (ρ : ℕ) (l r : Fin c) (i : Fin (c + 1)) (hi : ρ < i.val) (hil : i.val ≤ l.val)
    (hr : r.val + 1 = i.val) (E : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))) (hfix : fixSet ρ ⊆ E)
    (hlow : (lowSet ρ).filter (fun e => colIx e < i.val) ⊆ E)
    (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (y : (transSet (n := n) (n' := n') (c := c) ρ) → k)
    (q : n' ⊕ Fin (c + 1)) (hq : (Sum.inr r, q) ∉ transSet (n := n) (n' := n') (c := c) ρ) :
    fillAt (basePt c (0 : Matrix n n' k)) E (transSet ρ) x y (Sum.inr l) q = 0 := by
  simp only [fillAt, of_apply]
  rcases q with s | j
  · have h1 : (Sum.inr l, Sum.inl s) ∉ transSet (n := n) (n' := n') (c := c) ρ := by
      rw [mem_trans]; simp [Free]; omega
    have h2 : (Sum.inr l, Sum.inl s) ∈ E := hfix (by rw [mem_fix]; right; exact ⟨l, s, rfl, by omega, rfl⟩)
    rw [dif_neg h1, if_pos h2]
    simp [basePt]
  · rw [mem_trans] at hq
    simp [Free] at hq
    have hj : j.val ≤ r.val := by omega
    have h1 : (Sum.inr l, Sum.inr j) ∉ transSet (n := n) (n' := n') (c := c) ρ := by
      rw [mem_trans]; simp [Free]; omega
    have h2 : (Sum.inr l, Sum.inr j) ∈ E := by
      by_cases hjρ : j.val ≤ ρ
      · exact hfix (by rw [mem_fix]; left; exact ⟨j, rfl, hjρ, by simp [Free]; omega⟩)
      · exact hlow (by
          rw [Finset.mem_filter, mem_low]
          exact ⟨⟨l, j, rfl, by omega, by omega⟩, by simp [colIx]; omega⟩)
    have hlj : l.val ≠ j.val := by omega
    rw [dif_neg h1, if_pos h2]
    simp [basePt, hlj]

theorem rowAdd_fill (ρ : ℕ) (l r : Fin c) (i : Fin (c + 1)) (hi : ρ < i.val) (hil : i.val ≤ l.val)
    (hr : r.val + 1 = i.val) (E : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))) (hfix : fixSet ρ ⊆ E)
    (hlow : (lowSet ρ).filter (fun e => colIx e < i.val) ⊆ E) (b : k)
    (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (y : (transSet (n := n) (n' := n') (c := c) ρ) → k) :
    (fromBlocks 1 0 0 (transvection r l b) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) *
        fillAt (basePt c (0 : Matrix n n' k)) E (transSet ρ) x y =
      fillAt (basePt c (0 : Matrix n n' k)) E (transSet ρ) x (y + fun j => if j.1.1 = Sum.inr r then
        b * fillAt (basePt c (0 : Matrix n n' k)) E (transSet ρ) x y (Sum.inr l) j.1.2 else 0) := by
  ext p q
  rw [rowAdd_mul_apply]
  by_cases hpq : (p, q) ∈ transSet (n := n) (n' := n') (c := c) ρ
  · conv_rhs => rw [fillAt, of_apply, dif_pos hpq]
    conv_lhs => rw [fillAt, of_apply, dif_pos hpq]
    rfl
  · have h0 : (if p = Sum.inr r then
        b * fillAt (basePt c (0 : Matrix n n' k)) E (transSet ρ) x y (Sum.inr l) q else 0) = 0 := by
      split_ifs with hp
      · subst hp
        rw [fill_row_zero ρ l r i hi hil hr E hfix hlow x y q hpq, mul_zero]
      · rfl
    rw [h0, add_zero]
    simp only [fillAt, of_apply, dif_neg hpq]

omit [Fintype n'] [DecidableEq n'] in
theorem ch_rowAdd (l r : Fin c) (i : Fin (c + 1)) (hr : r.val + 1 = i.val) (b : k)
    (t : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :
    ch ((fromBlocks 1 0 0 (transvection r l b) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * t) =
      ch t + b * t (Sum.inr l) (Sum.inr i) := by
  have hsi : r.succ = i := Fin.ext (by simp [hr])
  simp [ch, rowAdd_mul_apply, Finset.sum_add_distrib, hsi]

def elem (r l : Fin c) (h : r ≠ l) (a : k) : GL (Fin c) k :=
  ⟨transvection r l a, transvection r l (-a),
    by rw [transvection_mul_transvection_same _ _ h]; simp,
    by rw [transvection_mul_transvection_same _ _ h]; simp⟩

theorem embA_elem_val (r l : Fin c) (h : r ≠ l) (a : k) :
    (embA n (elem r l h a)).val = fromBlocks 1 0 0 (transvection r l a) := rfl

theorem embA_elem_inv_val (r l : Fin c) (h : r ≠ l) (a : k) :
    ((embA n (elem r l h a))⁻¹).val = fromBlocks 1 0 0 (transvection r l (-a)) := rfl

theorem embA_elem_mem (r l : Fin c) (h : r ≠ l) (hrl : r.val < l.val) (a : k) (p : ℕ) :
    embA n (elem r l h a) ∈ N k n c p := by
  apply Subgroup.subset_closure
  show InN p _
  intro r' s hrs
  rw [embA_elem_val]
  rcases r' with r' | r' <;> rcases s with s | s
  · simp [one_apply]
  · simp [one_apply]
  · simp [one_apply]
  · simp only [lev, Sum.elim_inr] at hrs
    simp only [fromBlocks_apply₂₂, transvection, Matrix.add_apply, single_apply, one_apply, Sum.inr.injEq]
    have : ¬ (r = r' ∧ l = s) := by
      rintro ⟨rfl, rfl⟩
      omega
    rw [if_neg this, add_zero]

theorem simpleSum_elem (r l : Fin c) (h : r ≠ l) (a : k) :
    simpleSum (embA n (elem r l h a)) = if l.val = r.val + 1 then a else 0 := by
  rw [simpleSum, embA_elem_val]
  have key : ∀ i j : Fin c, (if j.val = i.val + 1 then
      (fromBlocks 1 0 0 (transvection r l a) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inr i) (Sum.inr j) else 0) =
      if j = l then (if i = r then (if l.val = r.val + 1 then a else 0) else 0) else 0 := by
    intro i j
    simp only [fromBlocks_apply₂₂, transvection, Matrix.add_apply, single_apply]
    by_cases hij : j.val = i.val + 1
    · have hne : i ≠ j := fun h => by rw [h] at hij; omega
      rw [if_pos hij, one_apply_ne hne, zero_add]
      by_cases hi : i = r
      · subst hi
        by_cases hj : j = l
        · subst hj; simp [hij]
        · simp [hj, Ne.symm hj]
      · simp [hi, Ne.symm hi]
    · rw [if_neg hij]
      by_cases hi : i = r
      · subst hi
        by_cases hj : j = l
        · subst hj; simp [hij]
        · simp [hj]
      · simp [hi]
  simp only [key]
  simp

end Alg

theorem evalLaw_low : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), c = 2 * ρ + 1 → (∀ u : GL (Fin c) k, embA n u ∈ N k n c (ρ + 1) → ∀ (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (((embA n u)⁻¹).val * t)) → L Φ' = (ψ (-simpleSum (embA n u)) : ℂ) • L Φ) → ∀ (l : Fin c) (i : Fin (c + 1)), ρ < i.val → i.val ≤ l.val → ∀ E : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))), GlobalTheory.PartRed.fixSet ρ ⊆ E → (GlobalTheory.PartRed.lowSet ρ).filter (fun e => GlobalTheory.PartRed.colIx e < i.val) ⊆ E → E ⊆ GlobalTheory.PartRed.fixSet ρ ∪ GlobalTheory.PartRed.lowSet ρ → (Sum.inr l, Sum.inr i) ∉ E → GlobalTheory.PartRed.EvalLaw L ψ ν GlobalTheory.PartRed.chL (basePt c (0 : Matrix n n' k)) E (GlobalTheory.PartRed.transSet ρ) (Sum.inr l, Sum.inr i) := by
  intro k _ _ _ _ _ _ ψ ν hψ hν n n' _ _ _ _ c ρ M _ _ L hc hL l i hi hil E hfix hlow hEsub hlE
  unfold GlobalTheory.PartRed.EvalLaw
  intro b Φ
  have hlc := l.isLt
  let r : Fin c := ⟨i.val - 1, by omega⟩
  have hr : r.val + 1 = i.val := by show i.val - 1 + 1 = i.val; omega
  have hrl' : r.val < l.val := by show i.val - 1 < l.val; omega
  have hrl : r ≠ l := fun h => by rw [h] at hrl'; exact lt_irrefl _ hrl'
  set β := basePt c (0 : Matrix n n' k) with hβ
  set T := GlobalTheory.PartRed.transSet (n := n) (n' := n') (c := c) ρ with hT
  set u := elem (k := k) r l hrl (-b) with hu
  have hgN : embA n u ∈ N k n c (ρ + 1) := embA_elem_mem r l hrl hrl' (-b) (ρ + 1)
  have hmem := GlobalTheory.T.schwartzBruhat_comp_affine_matrix k (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) (embA n u)⁻¹ 0 Φ.1 Φ.2
  let Φ₁ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) := ⟨_, hmem⟩
  have hΦ₁ : ∀ t, Φ₁.1 t = Φ.1 (((embA n u)⁻¹).val * t) := fun t => by simp [Φ₁]
  have hL1 := hL u hgN Φ Φ₁ hΦ₁
  have hinv : ((embA n u)⁻¹).val = fromBlocks 1 0 0 (transvection r l b) := by
    rw [hu, embA_elem_inv_val, neg_neg]
  have hβli : β (Sum.inr l) (Sum.inr i) = if l.val = i.val then 1 else 0 := by
    simp [hβ, basePt]
  have hss : simpleSum (embA n u) = -(b * β (Sum.inr l) (Sum.inr i)) := by
    rw [hu, simpleSum_elem, hβli]
    by_cases h : l.val = i.val
    · rw [if_pos (by omega), if_pos h]; ring
    · rw [if_neg (by omega), if_neg h]; ring
  have hxli : ∀ x y, GlobalTheory.PartRed.fillAt β E T x y (Sum.inr l) (Sum.inr i) = x (Sum.inr l) (Sum.inr i) := by
    intro x y
    have h1 : (Sum.inr l, Sum.inr i) ∉ T := by rw [hT, mem_trans]; simp [Free]; omega
    simp only [GlobalTheory.PartRed.fillAt, of_apply, dif_neg h1, if_neg hlE]
  refine ⟨(ψ (-(b * β (Sum.inr l) (Sum.inr i))) : ℂ) • Φ₁, ?_, ?_⟩
  · rw [map_smul, hL1, smul_smul, hss, neg_neg, ← Circle.coe_mul, ← AddChar.map_add_eq_mul,
      neg_add_cancel, AddChar.map_zero_eq_one, Circle.coe_one, one_smul]
  · intro x
    dsimp only
    let s : (T → k) → (T → k) := fun y j =>
      if j.1.1 = Sum.inr r then b * GlobalTheory.PartRed.fillAt β E T x y (Sum.inr l) j.1.2 else 0
    have hfill : ∀ y, (fromBlocks 1 0 0 (transvection r l b) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) *
        GlobalTheory.PartRed.fillAt β E T x y = GlobalTheory.PartRed.fillAt β E T x (y + s y) :=
      fun y => rowAdd_fill ρ l r i hi hil hr E hfix hlow b x y
    have hch : ∀ y, ch (GlobalTheory.PartRed.fillAt β E T x (y + s y)) =
        ch (GlobalTheory.PartRed.fillAt β E T x y) + b * x (Sum.inr l) (Sum.inr i) := fun y => by
      rw [← hfill, ch_rowAdd l r i hr b, hxli]
    have hone : (ψ (b * x (Sum.inr l) (Sum.inr i)) : ℂ) * ψ (-(b * x (Sum.inr l) (Sum.inr i))) = 1 := by
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, Circle.coe_one]
    let G : (T → k) → ℂ := fun y => Φ.1 (GlobalTheory.PartRed.fillAt β E T x y) *
      (ψ (-ch (GlobalTheory.PartRed.fillAt β E T x y)) : ℂ)
    have key : ∀ y, Φ₁.1 (GlobalTheory.PartRed.fillAt β E T x y) * (ψ (-ch (GlobalTheory.PartRed.fillAt β E T x y)) : ℂ) =
        (ψ (b * x (Sum.inr l) (Sum.inr i)) : ℂ) * G (y + s y) := by
      intro y
      simp only [G]
      rw [hΦ₁, hinv, hfill, hch, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]
      linear_combination (-(Φ.1 (GlobalTheory.PartRed.fillAt β E T x (y + s y)) *
        (ψ (-ch (GlobalTheory.PartRed.fillAt β E T x y)) : ℂ))) * hone
    let S : Finset T := Finset.univ.filter fun j => j.1.1 = Sum.inr r
    have hs_cont : Continuous s := by
      refine continuous_pi fun j => ?_
      simp only [s]
      split_ifs
      · refine continuous_const.mul ?_
        simp only [GlobalTheory.PartRed.fillAt, of_apply]
        split_ifs <;> first | exact continuous_apply _ | exact continuous_const
      · exact continuous_const
    have hs_dep : ∀ y y' : T → k, (∀ j, j ∉ S → y j = y' j) → s y = s y' := by
      intro y y' h
      funext j
      simp only [s]
      split_ifs
      · congr 1
        simp only [GlobalTheory.PartRed.fillAt, of_apply]
        split_ifs <;> first | rfl | exact h _ (by simp [S]; exact Ne.symm hrl)
      · rfl
    have hs_supp : ∀ (y : T → k) j, j ∉ S → s y j = 0 := by
      intro y j hj
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp only [s, if_neg hj]
    have hchg := GlobalTheory.T.integral_coordinate_shear_haar_localField k ν hν T S s hs_cont hs_dep hs_supp G
    simp only [GlobalTheory.PartRed.red, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, GlobalTheory.PartRed.chL_apply]
    calc ∫ y : T → k, (ψ (-(b * β (Sum.inr l) (Sum.inr i))) : ℂ) * Φ₁.1 (GlobalTheory.PartRed.fillAt β E T x y) *
          (ψ (-ch (GlobalTheory.PartRed.fillAt β E T x y)) : ℂ) ∂(Measure.pi fun _ => ν)
        = ∫ y : T → k, ((ψ (-(b * β (Sum.inr l) (Sum.inr i))) : ℂ) * ψ (b * x (Sum.inr l) (Sum.inr i))) *
          G (y + s y) ∂(Measure.pi fun _ => ν) := by
          congr 1; funext y; rw [mul_assoc, key, mul_assoc]
      _ = ((ψ (-(b * β (Sum.inr l) (Sum.inr i))) : ℂ) * ψ (b * x (Sum.inr l) (Sum.inr i))) *
          ∫ y : T → k, G y ∂(Measure.pi fun _ => ν) := by rw [integral_const_mul, hchg]
      _ = _ := by
          rw [show b * (x (Sum.inr l) (Sum.inr i) - β (Sum.inr l) (Sum.inr i)) =
            -(b * β (Sum.inr l) (Sum.inr i)) + b * x (Sum.inr l) (Sum.inr i) by ring,
            AddChar.map_add_eq_mul, Circle.coe_mul]

end GlobalTheory.PartRed.LowLaw
