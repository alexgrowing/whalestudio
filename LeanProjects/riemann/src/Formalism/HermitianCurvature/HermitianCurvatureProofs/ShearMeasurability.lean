import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LowerParabolicCoordinates

open Matrix MeasureTheory Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P

namespace ShearMeasurability

section Shear

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def lvl (ρ : ι → ℕ) (F : (ι → ℂ) → ι → ℂ) (n : ℕ) (x : ι → ℂ) : ι → ℂ :=
  fun q => if ρ q = n then F x q else x q

def upto (ρ : ι → ℕ) (F : (ι → ℂ) → ι → ℂ) (n : ℕ) (x : ι → ℂ) : ι → ℂ :=
  fun q => if ρ q < n then F x q else x q

def ShearCond (ρ : ι → ℕ) (F : (ι → ℂ) → ι → ℂ) : Prop :=
  ∀ q (x y : ι → ℂ), (∀ p, ρ p < ρ q → x p = y p) → F x q - x q = F y q - y q

lemma upto_succ {ρ : ι → ℕ} {F : (ι → ℂ) → ι → ℂ} (hF : ShearCond ρ F) (n : ℕ) :
    upto ρ F (n + 1) = upto ρ F n ∘ lvl ρ F n := by
  funext x q
  show (if ρ q < n + 1 then F x q else x q) =
    (if ρ q < n then F (lvl ρ F n x) q else lvl ρ F n x q)
  have hlv : ∀ p, ρ p ≠ n → lvl ρ F n x p = x p := fun p hp => by
    simp only [lvl]
    rw [if_neg hp]
  by_cases h1 : ρ q < n
  · rw [if_pos (by omega), if_pos h1]
    have h2 := hF q x (lvl ρ F n x) (fun p hp => (hlv p (by omega)).symm)
    rw [hlv q (by omega)] at h2
    linear_combination h2
  · by_cases h2 : ρ q = n
    · rw [if_pos (by omega), if_neg h1]
      simp only [lvl]
      rw [if_pos h2]
    · rw [if_neg (by omega), if_neg h1, hlv q h2]

lemma lvl_mp {ρ : ι → ℕ} {F : (ι → ℂ) → ι → ℂ} (hFm : Measurable F) (hF : ShearCond ρ F) (n : ℕ) :
    MeasurePreserving (lvl ρ F n) volume volume := by
  classical
  let p : ι → Prop := fun q => ρ q ≠ n
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℂ) p
  have he : MeasurePreserving e volume
      ((volume : Measure ({q // p q} → ℂ)).prod (volume : Measure ({q // ¬ p q} → ℂ))) :=
    measurePreserving_piEquivPiSubtypeProd (fun _ => (volume : Measure ℂ)) p
  let x0 : ({q // p q} → ℂ) → ι → ℂ := fun z => e.symm (z, 0)
  let φ : ({q // p q} → ℂ) → {q // ¬ p q} → ℂ := fun z q => F (x0 z) q - x0 z q
  have hx0 : Measurable x0 := e.symm.measurable.comp (measurable_id.prodMk measurable_const)
  have hφ : Measurable φ := by
    apply measurable_pi_lambda
    intro q
    exact ((measurable_pi_apply _).comp (hFm.comp hx0)).sub ((measurable_pi_apply _).comp hx0)
  let T : ({q // p q} → ℂ) × ({q // ¬ p q} → ℂ) → ({q // p q} → ℂ) × ({q // ¬ p q} → ℂ) :=
    fun pr => (pr.1, pr.2 + φ pr.1)
  have hT : MeasurePreserving T ((volume : Measure ({q // p q} → ℂ)).prod volume)
      ((volume : Measure ({q // p q} → ℂ)).prod volume) :=
    (MeasurePreserving.id _).skew_product (g := fun z y => y + φ z)
      (measurable_snd.add (hφ.comp measurable_fst))
      (Filter.Eventually.of_forall fun z => (measurePreserving_add_right _ (φ z)).map_eq)
  have heq : lvl ρ F n = e.symm ∘ T ∘ e := by
    funext x
    apply e.injective
    simp only [Function.comp, MeasurableEquiv.apply_symm_apply]
    rw [MeasurableEquiv.piEquivPiSubtypeProd_apply]
    ext q
    · have hq : ρ q.1 ≠ n := q.2
      simp [T, lvl, hq]
    · have hq : ρ q.1 = n := not_not.1 q.2
      simp only [T, φ, x0, lvl, Pi.add_apply]
      rw [if_pos hq]
      have hagree : ∀ r, ρ r < ρ q.1 →
          x r = e.symm ((fun r : {q // p q} => x r), 0) r := by
        intro r hr
        have hpr : p r := by
          show ρ r ≠ n
          omega
        simp [e, MeasurableEquiv.piEquivPiSubtypeProd, hpr]
      have h2 := hF q.1 x _ hagree
      linear_combination h2
  rw [heq]
  exact (he.symm e).comp (hT.comp he)

theorem shear_mp (ρ : ι → ℕ) (F : (ι → ℂ) → ι → ℂ) (hFm : Measurable F) (hF : ShearCond ρ F) :
    MeasurePreserving F volume volume := by
  classical
  have hN : ∀ q, ρ q < Finset.univ.sup ρ + 1 := fun q =>
    Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ q))
  have hall : ∀ n, MeasurePreserving (upto ρ F n) volume volume := by
    intro n
    induction n with
    | zero =>
      have h0 : upto ρ F 0 = id := by
        funext x q
        simp [upto]
      rw [h0]
      exact MeasurePreserving.id _
    | succ n ih =>
      rw [upto_succ hF n]
      exact ih.comp (lvl_mp hFm hF n)
  have hF' : upto ρ F (Finset.univ.sup ρ + 1) = F := by
    funext x q
    simp [upto, hN q]
  rw [← hF']
  exact hall _

end Shear

section Low

variable {m : ℕ} (w : Equiv.Perm (Fin m))

def gap (q : C2.Lidx m) : ℕ := q.1.1.val - q.1.2.val

def splitEquiv : C2.Lidx m ≃ C2.LPidx w ⊕ C2.Lstidx w where
  toFun q := if h : w.symm q.1.2 < w.symm q.1.1 then Sum.inl ⟨q.1, q.2, h⟩
    else Sum.inr ⟨q.1, q.2, lt_of_le_of_ne (not_lt.mp h)
      (fun e => (ne_of_lt q.2) (w.symm.injective e).symm)⟩
  invFun := Sum.elim (fun q => ⟨q.1, q.2.1⟩) (fun q => ⟨q.1, q.2.1⟩)
  left_inv q := by
    by_cases h : w.symm q.1.2 < w.symm q.1.1 <;> simp [h]
  right_inv s := by
    rcases s with q | q
    · simp [q.2.2]
    · simp [not_lt.mpr (le_of_lt q.2.2)]

noncomputable def eSplit : (C2.Lidx m → ℂ) ≃ᵐ (C2.LPidx w → ℂ) × (C2.Lstidx w → ℂ) :=
  ((MeasurableEquiv.piCongrLeft (fun _ => ℂ) (splitEquiv w).symm).symm).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ => ℂ))

lemma eSplit_mp : MeasurePreserving (eSplit w) volume volume :=
  (measurePreserving_sumPiEquivProdPi (fun _ => (volume : Measure ℂ))).comp
    ((measurePreserving_piCongrLeft (fun _ => (volume : Measure ℂ)) (splitEquiv w).symm).symm _)

lemma eSplit_apply (x : C2.Lidx m → ℂ) :
    eSplit w x = (fun a => x ⟨a.1, a.2.1⟩, fun b => x ⟨b.1, b.2.1⟩) := by rfl

def mulMap (p : (C2.LPidx w → ℂ) × (C2.Lstidx w → ℂ)) : C2.Lidx m → ℂ := fun q =>
  (C2.lowOf (fun q : C2.LPidx w => q.1) p.1 * C2.lowOf (fun q : C2.Lstidx w => q.1) p.2) q.1.1 q.1.2

def aX (x : C2.Lidx m → ℂ) (i k : Fin m) : ℂ :=
  if h : k < i ∧ w.symm k < w.symm i then x ⟨(i, k), h.1⟩ else 0

def bX (x : C2.Lidx m → ℂ) (k j : Fin m) : ℂ :=
  if h : j < k ∧ w.symm k < w.symm j then x ⟨(k, j), h.1⟩ else 0

lemma shearMap_apply (x : C2.Lidx m → ℂ) (q : C2.Lidx m) :
    mulMap w (eSplit w x) q = x q + ∑ k, aX w x q.1.1 k * bX w x k q.1.2 := by
  classical
  have hA : ∀ i k, (∑ t : C2.LPidx w, if t.1 = (i, k) then x ⟨t.1, t.2.1⟩ else 0) = aX w x i k := by
    intro i k
    unfold aX
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨(i, k), h⟩]
      · simp
      · intro t _ ht
        rw [if_neg]
        intro e
        exact ht (Subtype.ext e)
      · simp
    · apply Finset.sum_eq_zero
      intro t _
      rw [if_neg]
      intro e
      apply h
      have h2 := t.2
      rw [e] at h2
      exact h2
  have hB : ∀ k j, (∑ t : C2.Lstidx w, if t.1 = (k, j) then x ⟨t.1, t.2.1⟩ else 0) = bX w x k j := by
    intro k j
    unfold bX
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨(k, j), h⟩]
      · simp
      · intro t _ ht
        rw [if_neg]
        intro e
        exact ht (Subtype.ext e)
      · simp
    · apply Finset.sum_eq_zero
      intro t _
      rw [if_neg]
      intro e
      apply h
      have h2 := t.2
      rw [e] at h2
      exact h2
  have hexp : ∀ i j, (C2.lowOf (fun t : C2.LPidx w => t.1) (fun t => x ⟨t.1, t.2.1⟩) *
      C2.lowOf (fun t : C2.Lstidx w => t.1) (fun t => x ⟨t.1, t.2.1⟩)) i j =
      (1 : Matrix (Fin m) (Fin m) ℂ) i j + bX w x i j + aX w x i j + ∑ k, aX w x i k * bX w x k j := by
    intro i j
    simp only [C2.lowOf]
    rw [add_mul, mul_add, mul_add]
    simp only [one_mul, mul_one, Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, hA, hB]
    ring
  have hne : q.1.1 ≠ q.1.2 := (ne_of_lt q.2).symm
  have hab : aX w x q.1.1 q.1.2 + bX w x q.1.1 q.1.2 = x q := by
    unfold aX bX
    by_cases h : w.symm q.1.2 < w.symm q.1.1
    · rw [dif_pos ⟨q.2, h⟩, dif_neg (fun h' => lt_asymm h h'.2)]
      simp
    · have h' : w.symm q.1.1 < w.symm q.1.2 :=
        lt_of_le_of_ne (not_lt.1 h) (fun e => hne (w.symm.injective e))
      rw [dif_neg (fun h'' => h h''.2), dif_pos ⟨q.2, h'⟩]
      simp
  simp only [mulMap, eSplit_apply]
  rw [hexp, Matrix.one_apply_ne hne]
  linear_combination hab

lemma shear_cond : ShearCond (gap (m := m)) (fun x => mulMap w (eSplit w x)) := by
  intro q x y hxy
  show mulMap w (eSplit w x) q - x q = mulMap w (eSplit w y) q - y q
  rw [shearMap_apply, shearMap_apply, add_sub_cancel_left, add_sub_cancel_left]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h1 : q.1.2 < k
  · by_cases h2 : k < q.1.1
    · have ea : aX w x q.1.1 k = aX w y q.1.1 k := by
        unfold aX
        split_ifs with h
        · apply hxy
          rw [Fin.lt_iff_val_lt_val] at h1 h2
          show q.1.1.val - k.val < q.1.1.val - q.1.2.val
          omega
        · rfl
      have eb : bX w x k q.1.2 = bX w y k q.1.2 := by
        unfold bX
        split_ifs with h
        · apply hxy
          rw [Fin.lt_iff_val_lt_val] at h1 h2
          show k.val - q.1.2.val < q.1.1.val - q.1.2.val
          omega
        · rfl
      rw [ea, eb]
    · have h0 : ∀ z, aX w z q.1.1 k = 0 := fun z => by
        unfold aX
        rw [dif_neg (fun h => h2 h.1)]
      rw [h0, h0, zero_mul, zero_mul]
  · have h0 : ∀ z, bX w z k q.1.2 = 0 := fun z => by
      unfold bX
      rw [dif_neg (fun h => h1 h.1)]
    rw [h0, h0, mul_zero, mul_zero]

lemma shear_meas : Measurable (fun x => mulMap w (eSplit w x)) := by
  have e : (fun x => mulMap w (eSplit w x)) =
      fun x q => x q + ∑ k, aX w x q.1.1 k * bX w x k q.1.2 := by
    funext x q
    exact shearMap_apply w x q
  rw [e]
  have ha : ∀ i k, Measurable fun x : C2.Lidx m → ℂ => aX w x i k := by
    intro i k
    by_cases h : k < i ∧ w.symm k < w.symm i
    · simp only [aX, dif_pos h]
      exact measurable_pi_apply _
    · simp only [aX, dif_neg h]
      exact measurable_const
  have hb : ∀ k j, Measurable fun x : C2.Lidx m → ℂ => bX w x k j := by
    intro k j
    by_cases h : j < k ∧ w.symm k < w.symm j
    · simp only [bX, dif_pos h]
      exact measurable_pi_apply _
    · simp only [bX, dif_neg h]
      exact measurable_const
  apply measurable_pi_lambda
  intro q
  exact (measurable_pi_apply q).add (Finset.measurable_sum _ fun k _ => (ha _ _).mul (hb _ _))

end Low

end ShearMeasurability

open ShearMeasurability

theorem lower_splitting_measurable : C2.LowSplitMeas := by
  intro m w
  have h1 := shear_mp gap (fun x => mulMap w (eSplit w x)) (shear_meas w) (shear_cond w)
  have h2 := (eSplit_mp w).symm (eSplit w)
  have h3 := h1.comp h2
  convert h3 using 1
  all_goals try rfl
  funext p
  simp only [Function.comp, MeasurableEquiv.apply_symm_apply]
  rfl

end Formalism.FourierDecayAlt.P
