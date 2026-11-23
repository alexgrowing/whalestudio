import Mathlib
import GroundTheory.AutomorphicForms.PartialDifferential.AnalyticHypoCalc

namespace GroundTheory.Automorphic.Sobolev

open scoped ContDiff
open Finset

noncomputable section

variable {n : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin n)

def tupleOp (m : ℕ) (a : (k : ℕ) → (Fin k → Fin n) → 𝔼 → ℂ) (u : 𝔼 → ℂ) (x : 𝔼) : ℂ :=
  ∑ k ∈ range (m + 1), ∑ J : Fin k → Fin n, a k J x * pdT J u x

def tupleSymbol (m : ℕ) (a : (k : ℕ) → (Fin k → Fin n) → 𝔼 → ℂ) (x ξ : 𝔼) : ℂ :=
  ∑ J : Fin m → Fin n, a m J x * ∏ l, ((ξ (J l) : ℝ) : ℂ)

def vfOp (c : 𝔼 → 𝔼) (u : 𝔼 → ℂ) (x : 𝔼) : ℂ := fderiv ℝ u x (c x)

def idCoeff : (k : ℕ) → (Fin k → Fin n) → 𝔼 → ℂ := fun k _ _ => if k = 0 then 1 else 0

theorem tupleOp_idCoeff (u : 𝔼 → ℂ) (x : 𝔼) : tupleOp 0 (idCoeff (n := n)) u x = u x := by
  simp [tupleOp, idCoeff, pdT_zero]

theorem tupleSymbol_idCoeff (x ξ : 𝔼) : tupleSymbol 0 (idCoeff (n := n)) x ξ = 1 := by
  simp [tupleSymbol, idCoeff]

theorem analyticOnNhd_idCoeff (k : ℕ) (J : Fin k → Fin n) (s : Set 𝔼) :
    AnalyticOnNhd ℝ (idCoeff k J) s :=
  analyticOnNhd_const

theorem tupleOp_add (m : ℕ) (a b : (k : ℕ) → (Fin k → Fin n) → 𝔼 → ℂ) (u : 𝔼 → ℂ) (x : 𝔼) :
    tupleOp m (a + b) u x = tupleOp m a u x + tupleOp m b u x := by
  simp only [tupleOp, Pi.add_apply, add_mul, sum_add_distrib]

theorem tupleOp_smul (m : ℕ) (c : ℂ) (a : (k : ℕ) → (Fin k → Fin n) → 𝔼 → ℂ) (u : 𝔼 → ℂ)
    (x : 𝔼) : tupleOp m (c • a) u x = c * tupleOp m a u x := by
  simp only [tupleOp, Pi.smul_apply, smul_eq_mul, mul_sum, mul_assoc]

theorem tupleOp_sum {ι : Type*} (s : Finset ι) (m : ℕ)
    (a : ι → (k : ℕ) → (Fin k → Fin n) → 𝔼 → ℂ) (u : 𝔼 → ℂ) (x : 𝔼) :
    tupleOp m (∑ i ∈ s, a i) u x = ∑ i ∈ s, tupleOp m (a i) u x := by
  simp only [tupleOp, Finset.sum_apply, sum_mul]
  symm
  rw [sum_comm]
  refine sum_congr rfl fun k _ => ?_
  rw [sum_comm]

theorem tupleSymbol_add (m : ℕ) (a b : (k : ℕ) → (Fin k → Fin n) → 𝔼 → ℂ) (x ξ : 𝔼) :
    tupleSymbol m (a + b) x ξ = tupleSymbol m a x ξ + tupleSymbol m b x ξ := by
  simp only [tupleSymbol, Pi.add_apply, add_mul, sum_add_distrib]

theorem tupleSymbol_smul (m : ℕ) (c : ℂ) (a : (k : ℕ) → (Fin k → Fin n) → 𝔼 → ℂ) (x ξ : 𝔼) :
    tupleSymbol m (c • a) x ξ = c * tupleSymbol m a x ξ := by
  simp only [tupleSymbol, Pi.smul_apply, smul_eq_mul, mul_sum, mul_assoc]

theorem tupleSymbol_sum {ι : Type*} (s : Finset ι) (m : ℕ)
    (a : ι → (k : ℕ) → (Fin k → Fin n) → 𝔼 → ℂ) (x ξ : 𝔼) :
    tupleSymbol m (∑ i ∈ s, a i) x ξ = ∑ i ∈ s, tupleSymbol m (a i) x ξ := by
  simp only [tupleSymbol, Finset.sum_apply, sum_mul]
  rw [sum_comm]

theorem analyticOnNhd_add_coeff {Ω : Set 𝔼} {a b : (k : ℕ) → (Fin k → Fin n) → 𝔼 → ℂ}
    (ha : ∀ k J, AnalyticOnNhd ℝ (a k J) Ω) (hb : ∀ k J, AnalyticOnNhd ℝ (b k J) Ω) (k : ℕ)
    (J : Fin k → Fin n) : AnalyticOnNhd ℝ ((a + b) k J) Ω :=
  (ha k J).add (hb k J)

theorem analyticOnNhd_smul_coeff {Ω : Set 𝔼} (c : ℂ) {a : (k : ℕ) → (Fin k → Fin n) → 𝔼 → ℂ}
    (ha : ∀ k J, AnalyticOnNhd ℝ (a k J) Ω) (k : ℕ) (J : Fin k → Fin n) :
    AnalyticOnNhd ℝ ((c • a) k J) Ω := by
  have e : (c • a) k J = fun x => c * a k J x := by funext x; simp
  rw [e]
  exact analyticOnNhd_const.mul (ha k J)

theorem analyticOnNhd_sum_coeff {ι : Type*} (s : Finset ι) {Ω : Set 𝔼}
    {a : ι → (k : ℕ) → (Fin k → Fin n) → 𝔼 → ℂ}
    (ha : ∀ i ∈ s, ∀ k J, AnalyticOnNhd ℝ (a i k J) Ω) (k : ℕ) (J : Fin k → Fin n) :
    AnalyticOnNhd ℝ ((∑ i ∈ s, a i) k J) Ω := by
  have e : (∑ i ∈ s, a i) k J = ∑ i ∈ s, a i k J := by simp only [Finset.sum_apply]
  rw [e]
  exact Finset.analyticOnNhd_sum s fun i hi => ha i hi k J

def raiseCoeff (m : ℕ) (a : (k : ℕ) → (Fin k → Fin n) → 𝔼 → ℂ) :
    (k : ℕ) → (Fin k → Fin n) → 𝔼 → ℂ :=
  fun k J x => if k ≤ m then a k J x else 0

theorem tupleOp_raiseCoeff {m m' : ℕ} (h : m ≤ m') (a : (k : ℕ) → (Fin k → Fin n) → 𝔼 → ℂ)
    (u : 𝔼 → ℂ) (x : 𝔼) : tupleOp m' (raiseCoeff m a) u x = tupleOp m a u x := by
  unfold tupleOp
  rw [← sum_subset (range_subset_range.2 (Nat.succ_le_succ h))]
  · refine sum_congr rfl fun k hk => ?_
    have hk' : k ≤ m := Nat.lt_succ_iff.1 (mem_range.1 hk)
    simp [raiseCoeff, hk']
  · intro k _ hk
    have hk' : ¬ k ≤ m := fun h' => hk (mem_range.2 (Nat.lt_succ_of_le h'))
    simp [raiseCoeff, hk']

theorem tupleSymbol_raiseCoeff (m : ℕ) (a : (k : ℕ) → (Fin k → Fin n) → 𝔼 → ℂ) (x ξ : 𝔼) :
    tupleSymbol m (raiseCoeff m a) x ξ = tupleSymbol m a x ξ := by
  simp [tupleSymbol, raiseCoeff]

theorem tupleSymbol_raiseCoeff_of_lt {m m' : ℕ} (h : m < m')
    (a : (k : ℕ) → (Fin k → Fin n) → 𝔼 → ℂ) (x ξ : 𝔼) :
    tupleSymbol m' (raiseCoeff m a) x ξ = 0 := by
  simp [tupleSymbol, raiseCoeff, not_le.2 h]

theorem analyticOnNhd_raiseCoeff {Ω : Set 𝔼} (m : ℕ) {a : (k : ℕ) → (Fin k → Fin n) → 𝔼 → ℂ}
    (ha : ∀ k J, AnalyticOnNhd ℝ (a k J) Ω) (k : ℕ) (J : Fin k → Fin n) :
    AnalyticOnNhd ℝ (raiseCoeff m a k J) Ω := by
  by_cases hk : k ≤ m
  · have e : raiseCoeff m a k J = a k J := by funext x; simp [raiseCoeff, hk]
    rw [e]; exact ha k J
  · have e : raiseCoeff m a k J = fun _ => 0 := by funext x; simp [raiseCoeff, hk]
    rw [e]; exact analyticOnNhd_const

theorem eq_sum_ev (v : 𝔼) : v = ∑ j, v j • ev j := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v]
  simp [ev]

theorem fderiv_apply_eq_sum (f : 𝔼 → ℂ) (x v : 𝔼) :
    fderiv ℝ f x v = ∑ j, ((v j : ℝ) : ℂ) * fderiv ℝ f x (ev j) := by
  conv_lhs => rw [eq_sum_ev v]
  simp [map_sum, map_smul, Complex.real_smul]

theorem analyticOnNhd_coord {Ω : Set 𝔼} {c : 𝔼 → 𝔼} (hc : AnalyticOnNhd ℝ c Ω) (j : Fin n) :
    AnalyticOnNhd ℝ (fun x => ((c x j : ℝ) : ℂ)) Ω := by
  have h1 : AnalyticOnNhd ℝ ((Complex.ofRealCLM.comp (EuclideanSpace.proj j : 𝔼 →L[ℝ] ℝ)) ∘ c)
      Ω :=
    ((Complex.ofRealCLM.comp (EuclideanSpace.proj j : 𝔼 →L[ℝ] ℝ)).analyticOnNhd _).comp hc
      (Set.mapsTo_univ _ _)
  exact h1

theorem analyticOnNhd_fderiv_apply {Ω : Set 𝔼} {f : 𝔼 → ℂ} {c : 𝔼 → 𝔼}
    (hf : AnalyticOnNhd ℝ f Ω) (hc : AnalyticOnNhd ℝ c Ω) :
    AnalyticOnNhd ℝ (fun x => fderiv ℝ f x (c x)) Ω := by
  have e : (fun x => fderiv ℝ f x (c x)) =
      ∑ j, fun x => ((c x j : ℝ) : ℂ) * fderiv ℝ f x (ev j) := by
    funext x
    rw [fderiv_apply_eq_sum f x (c x), Finset.sum_apply]
  rw [e]
  refine Finset.analyticOnNhd_sum _ fun j _ => (analyticOnNhd_coord hc j).mul ?_
  have h1 : AnalyticOnNhd ℝ ((ContinuousLinearMap.apply ℝ ℂ (ev j)) ∘ fderiv ℝ f) Ω :=
    ((ContinuousLinearMap.apply ℝ ℂ (ev j)).analyticOnNhd _).comp hf.fderiv (Set.mapsTo_univ _ _)
  exact h1

def shiftCoeff (c : 𝔼 → 𝔼) (m : ℕ) (a : (k : ℕ) → (Fin k → Fin n) → 𝔼 → ℂ) :
    (k : ℕ) → (Fin k → Fin n) → 𝔼 → ℂ
  | 0, _, _ => 0
  | k + 1, J, x => if k ≤ m then ((c x (J 0) : ℝ) : ℂ) * a k (Fin.tail J) x else 0

def vfCoeff (c : 𝔼 → 𝔼) (m : ℕ) (a : (k : ℕ) → (Fin k → Fin n) → 𝔼 → ℂ) :
    (k : ℕ) → (Fin k → Fin n) → 𝔼 → ℂ :=
  raiseCoeff m (fun k J x => fderiv ℝ (a k J) x (c x)) + shiftCoeff c m a

theorem tupleOp_shiftCoeff (c : 𝔼 → 𝔼) (m : ℕ) (a : (k : ℕ) → (Fin k → Fin n) → 𝔼 → ℂ)
    (u : 𝔼 → ℂ) (x : 𝔼) :
    tupleOp (m + 1) (shiftCoeff c m a) u x =
      ∑ k ∈ range (m + 1), ∑ j : Fin n, ∑ J : Fin k → Fin n,
        ((c x j : ℝ) : ℂ) * a k J x * pdT (Fin.cons j J) u x := by
  rw [tupleOp, sum_range_succ']
  simp only [shiftCoeff, zero_mul, sum_const_zero, add_zero]
  refine sum_congr rfl fun k hk => ?_
  have hkm : k ≤ m := Nat.lt_succ_iff.1 (mem_range.1 hk)
  simp only [if_pos hkm]
  rw [← (Fin.consEquiv fun _ : Fin (k + 1) => Fin n).sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun j _ => sum_congr rfl fun J _ => ?_
  simp [Fin.consEquiv]

theorem tupleSymbol_shiftCoeff (c : 𝔼 → 𝔼) (m : ℕ) (a : (k : ℕ) → (Fin k → Fin n) → 𝔼 → ℂ)
    (x ξ : 𝔼) :
    tupleSymbol (m + 1) (shiftCoeff c m a) x ξ =
      (∑ j, ((c x j : ℝ) : ℂ) * ((ξ j : ℝ) : ℂ)) * tupleSymbol m a x ξ := by
  simp only [tupleSymbol, shiftCoeff, le_refl, if_true]
  rw [← (Fin.consEquiv fun _ : Fin (m + 1) => Fin n).sum_comp, Fintype.sum_prod_type, sum_mul]
  refine sum_congr rfl fun j _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun J _ => ?_
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, Fin.tail_cons, Fin.prod_univ_succ,
    Fin.cons_succ]
  ring

theorem analyticOnNhd_shiftCoeff {Ω : Set 𝔼} {c : 𝔼 → 𝔼} (hc : AnalyticOnNhd ℝ c Ω) (m : ℕ)
    {a : (k : ℕ) → (Fin k → Fin n) → 𝔼 → ℂ} (ha : ∀ k J, AnalyticOnNhd ℝ (a k J) Ω) :
    ∀ (k : ℕ) (J : Fin k → Fin n), AnalyticOnNhd ℝ (shiftCoeff c m a k J) Ω
  | 0, J => by
      have e : shiftCoeff c m a 0 J = fun _ => 0 := by funext x; simp [shiftCoeff]
      rw [e]; exact analyticOnNhd_const
  | k + 1, J => by
      by_cases hk : k ≤ m
      · have e : shiftCoeff c m a (k + 1) J =
            fun x => ((c x (J 0) : ℝ) : ℂ) * a k (Fin.tail J) x := by
          funext x; simp [shiftCoeff, hk]
        rw [e]; exact (analyticOnNhd_coord hc (J 0)).mul (ha k _)
      · have e : shiftCoeff c m a (k + 1) J = fun _ => 0 := by funext x; simp [shiftCoeff, hk]
        rw [e]; exact analyticOnNhd_const

theorem vfOp_tupleOp_eq {Ω : Set 𝔼} {c : 𝔼 → 𝔼} {m : ℕ}
    {a : (k : ℕ) → (Fin k → Fin n) → 𝔼 → ℂ} (ha : ∀ k J, AnalyticOnNhd ℝ (a k J) Ω)
    {u : 𝔼 → ℂ} (hu : ContDiff ℝ ∞ u) {x : 𝔼} (hx : x ∈ Ω) :
    vfOp c (tupleOp m a u) x = ∑ k ∈ range (m + 1), ∑ J : Fin k → Fin n,
      (fderiv ℝ (a k J) x (c x) * pdT J u x +
        a k J x * ∑ j : Fin n, ((c x j : ℝ) : ℂ) * pdT (Fin.cons j J) u x) := by
  have hterm : ∀ (k : ℕ) (J : Fin k → Fin n), HasFDerivAt (fun y => a k J y * pdT J u y)
      (a k J x • fderiv ℝ (pdT J u) x + pdT J u x • fderiv ℝ (a k J) x) x := fun k J =>
    ((ha k J x hx).differentiableAt.hasFDerivAt).mul
      (((contDiff_pdT hu J).differentiable (by simp)) x).hasFDerivAt
  have hsum : HasFDerivAt (tupleOp m a u) (∑ k ∈ range (m + 1), ∑ J : Fin k → Fin n,
      (a k J x • fderiv ℝ (pdT J u) x + pdT J u x • fderiv ℝ (a k J) x)) x :=
    HasFDerivAt.fun_sum fun k _ => HasFDerivAt.fun_sum fun J _ => hterm k J
  rw [vfOp, hsum.fderiv]
  simp only [FunLike.coe_sum, Finset.sum_apply, add_apply, FunLike.coe_smul, Pi.smul_apply,
    smul_eq_mul]
  refine sum_congr rfl fun k _ => sum_congr rfl fun J _ => ?_
  rw [fderiv_apply_eq_sum (pdT J u) x (c x)]
  have e : ∀ j, fderiv ℝ (pdT J u) x (ev j) = pdT (Fin.cons j J) u x := fun j => by
    rw [pdT_cons hu j J]; rfl
  simp only [e]
  ring

theorem exists_vfOp_tupleOp {Ω : Set 𝔼} {c : 𝔼 → 𝔼} (hc : AnalyticOnNhd ℝ c Ω) {m : ℕ}
    {a : (k : ℕ) → (Fin k → Fin n) → 𝔼 → ℂ} (ha : ∀ k J, AnalyticOnNhd ℝ (a k J) Ω) :
    ∃ a' : (k : ℕ) → (Fin k → Fin n) → 𝔼 → ℂ, (∀ k J, AnalyticOnNhd ℝ (a' k J) Ω) ∧
      (∀ x ξ : 𝔼, tupleSymbol (m + 1) a' x ξ =
        (∑ j, ((c x j : ℝ) : ℂ) * ((ξ j : ℝ) : ℂ)) * tupleSymbol m a x ξ) ∧
      ∀ u : 𝔼 → ℂ, ContDiff ℝ ∞ u → ∀ x ∈ Ω, vfOp c (tupleOp m a u) x = tupleOp (m + 1) a' u x := by
  refine ⟨vfCoeff c m a, ?_, ?_, ?_⟩
  · intro k J
    exact analyticOnNhd_add_coeff
      (analyticOnNhd_raiseCoeff m fun k J => analyticOnNhd_fderiv_apply (ha k J) hc)
      (analyticOnNhd_shiftCoeff hc m ha) k J
  · intro x ξ
    rw [vfCoeff, tupleSymbol_add, tupleSymbol_raiseCoeff_of_lt (Nat.lt_succ_self m),
      tupleSymbol_shiftCoeff, zero_add]
  · intro u hu x hx
    rw [vfOp_tupleOp_eq ha hu hx, vfCoeff, tupleOp_add, tupleOp_raiseCoeff (Nat.le_succ m),
      tupleOp_shiftCoeff]
    have e2 : ∀ k ∈ range (m + 1), (∑ j : Fin n, ∑ J : Fin k → Fin n,
        ((c x j : ℝ) : ℂ) * a k J x * pdT (Fin.cons j J) u x) =
        ∑ J : Fin k → Fin n, a k J x * ∑ j : Fin n, ((c x j : ℝ) : ℂ) * pdT (Fin.cons j J) u x := by
      intro k _
      rw [sum_comm]
      refine sum_congr rfl fun J _ => ?_
      rw [mul_sum]
      exact sum_congr rfl fun j _ => by ring
    rw [sum_congr rfl e2, tupleOp, ← sum_add_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [← sum_add_distrib]

theorem vfOp_congr_of_eqOn {Ω : Set 𝔼} (hΩ : IsOpen Ω) {u v : 𝔼 → ℂ} (h : Set.EqOn u v Ω)
    (c : 𝔼 → 𝔼) {x : 𝔼} (hx : x ∈ Ω) : vfOp c u x = vfOp c v x := by
  simp only [vfOp]
  rw [Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (hΩ.mem_nhds hx) h)]

def dList : List 𝔼 → (𝔼 → ℂ) → 𝔼 → ℂ
  | [], f => f
  | a :: L, f => fun x => fderiv ℝ (dList L f) x a

theorem contDiff_dList {f : 𝔼 → ℂ} (hf : ContDiff ℝ ∞ f) : ∀ L : List 𝔼, ContDiff ℝ ∞ (dList L f)
  | [] => hf
  | a :: L => contDiff_fderiv_apply (contDiff_dList hf L) a

theorem dT_eq_dList {f : 𝔼 → ℂ} (hf : ContDiff ℝ ∞ f) :
    ∀ {k : ℕ} (v : Fin k → 𝔼), dT v f = dList (List.ofFn v) f
  | 0, v => by simp [dT_zero, dList]
  | k + 1, v => by
      have e : List.ofFn v = v 0 :: List.ofFn (Fin.tail v) := by
        rw [List.ofFn_succ]
        rfl
      rw [e]
      conv_lhs => rw [← Fin.cons_self_tail v]
      rw [dT_cons hf, dT_eq_dList hf (Fin.tail v)]
      rfl

theorem dList_perm {f : 𝔼 → ℂ} (hf : ContDiff ℝ ∞ f) {L L' : List 𝔼} (h : L.Perm L') :
    dList L f = dList L' f := by
  induction h with
  | nil => rfl
  | cons a _ ih =>
    show (fun x => fderiv ℝ (dList _ f) x a) = (fun x => fderiv ℝ (dList _ f) x a)
    rw [ih]
  | swap a b L =>
    funext z
    exact fderiv_fderiv_apply_comm (contDiff_dList hf L) z b a
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

def tupleCount {k : ℕ} (J : Fin k → Fin n) : Fin n → ℕ :=
  fun i => (univ.filter fun l => J l = i).card

theorem mabs_tupleCount {k : ℕ} (J : Fin k → Fin n) : mabs (tupleCount J) = k := by
  simp only [mabs, tupleCount]
  rw [← card_eq_sum_card_fiberwise (f := J) (s := univ) (t := univ)
    (fun _ _ => mem_coe.2 (mem_univ _))]
  simp

theorem count_ofFn {k : ℕ} (J : Fin k → Fin n) (i : Fin n) :
    (List.ofFn J).count i = tupleCount J i := by
  rw [← Multiset.coe_count, ← Fin.univ_val_map, Multiset.count_map]
  simp [tupleCount, Finset.card, Finset.filter_val, eq_comm]

theorem ofFn_perm_flatMap {k : ℕ} (J : Fin k → Fin n) :
    (List.ofFn J).Perm ((List.finRange n).flatMap fun i => List.replicate (tupleCount J i) i) := by
  rw [List.perm_iff_count]
  intro i
  rw [count_ofFn, List.count_flatMap]
  simp only [Function.comp_def, List.count_replicate, beq_iff_eq]
  rw [← Fin.sum_univ_def]
  simp

theorem mdirList_eq_map (α : Fin n → ℕ) :
    mdirList α = ((List.finRange n).flatMap fun i => List.replicate (α i) i).map ev := by
  simp [mdirList, List.map_flatMap, List.map_replicate, ev]

theorem ofFn_mdir (α : Fin n → ℕ) : List.ofFn (mdir α) = mdirList α := by
  apply List.ext_getElem (by simp [length_mdirList])
  intro i h1 h2
  simp [mdir]

theorem pdT_eq_pderiv {u : 𝔼 → ℂ} (hu : ContDiff ℝ ∞ u) {k : ℕ} (J : Fin k → Fin n) :
    pdT J u = pderiv (tupleCount J) u := by
  rw [pdT, pderiv_eq_dT', dT_eq_dList hu, dT_eq_dList hu, ofFn_mdir, mdirList_eq_map]
  apply dList_perm hu
  rw [show List.ofFn (fun l => ev (J l)) = (List.ofFn J).map ev by simp [List.map_ofFn, Function.comp_def]]
  exact (ofFn_perm_flatMap J).map ev

theorem prod_eq_mpow {k : ℕ} (J : Fin k → Fin n) (ξ : 𝔼) :
    ∏ l, ((ξ (J l) : ℝ) : ℂ) = ((mpow (tupleCount J) ξ : ℝ) : ℂ) := by
  classical
  rw [mpow, Complex.ofReal_prod]
  push_cast
  rw [Finset.prod_comp (fun i => ((ξ i : ℝ) : ℂ)) J]
  apply Finset.prod_subset (subset_univ _)
  intro i _ hi
  have h0 : (univ.filter fun l => J l = i).card = 0 := by
    rw [card_eq_zero, filter_eq_empty_iff]
    intro l _ hl
    exact hi (mem_image.2 ⟨l, mem_univ _, hl⟩)
  simp [h0]

theorem exists_diffOp_eq_tupleOp {Ω : Set 𝔼} (m : ℕ) (a : (k : ℕ) → (Fin k → Fin n) → 𝔼 → ℂ)
    (ha : ∀ k J, AnalyticOnNhd ℝ (a k J) Ω) :
    ∃ (A : Finset (Fin n → ℕ)) (b : (Fin n → ℕ) → 𝔼 → ℂ), (∀ α ∈ A, mabs α ≤ m) ∧
      (∀ α ∈ A, AnalyticOnNhd ℝ (b α) Ω) ∧
      (∀ x ξ : 𝔼, prinSymbol A b m x ξ = tupleSymbol m a x ξ) ∧
      ∀ u : 𝔼 → ℂ, ContDiff ℝ ∞ u → ∀ x, diffOp A b u x = tupleOp m a u x := by
  classical
  let A : Finset (Fin n → ℕ) :=
    (range (m + 1)).biUnion fun k => univ.image fun J : Fin k → Fin n => tupleCount J
  let b : (Fin n → ℕ) → 𝔼 → ℂ := fun α x =>
    ∑ k ∈ range (m + 1), ∑ J : Fin k → Fin n, if tupleCount J = α then a k J x else 0
  have hmemA : ∀ k ∈ range (m + 1), ∀ J : Fin k → Fin n, tupleCount J ∈ A := fun k hk J =>
    mem_biUnion.2 ⟨k, hk, mem_image_of_mem _ (mem_univ J)⟩
  have hb : ∀ (α : Fin n → ℕ) (x : 𝔼) (z : ℂ), b α x * z = ∑ k ∈ range (m + 1),
      ∑ J : Fin k → Fin n, if tupleCount J = α then a k J x * z else 0 := by
    intro α x z
    simp only [b, sum_mul]
    refine sum_congr rfl fun k _ => sum_congr rfl fun J _ => ?_
    split_ifs <;> simp
  refine ⟨A, b, ?_, ?_, ?_, ?_⟩
  · intro α hα
    obtain ⟨k, hk, hα'⟩ := mem_biUnion.1 hα
    obtain ⟨J, _, rfl⟩ := mem_image.1 hα'
    rw [mabs_tupleCount]
    exact Nat.lt_succ_iff.1 (mem_range.1 hk)
  · intro α _
    have e : b α = ∑ k ∈ range (m + 1), ∑ J : Fin k → Fin n,
        (fun x => if tupleCount J = α then a k J x else 0) := by
      funext x
      simp only [b, Finset.sum_apply]
    rw [e]
    refine Finset.analyticOnNhd_sum _ fun k _ => Finset.analyticOnNhd_sum _ fun J _ => ?_
    by_cases h : tupleCount J = α
    · simpa [h] using ha k J
    · simpa [h] using (analyticOnNhd_const (v := (0 : ℂ)) (s := Ω) (𝕜 := ℝ))
  · intro x ξ
    simp only [prinSymbol, tupleSymbol, hb]
    rw [sum_comm]
    have e2 : ∀ k ∈ range (m + 1), (∑ α ∈ A with mabs α = m, ∑ J : Fin k → Fin n,
        if tupleCount J = α then a k J x * ((mpow α ξ : ℝ) : ℂ) else 0) =
        if k = m then ∑ J : Fin k → Fin n, a k J x * ((mpow (tupleCount J) ξ : ℝ) : ℂ)
        else 0 := by
      intro k hk
      rw [sum_comm]
      split_ifs with hkm
      · refine sum_congr rfl fun J _ => ?_
        rw [sum_ite_eq, if_pos]
        exact mem_filter.2 ⟨hmemA k hk J, by rw [mabs_tupleCount, hkm]⟩
      · refine sum_eq_zero fun J _ => ?_
        rw [sum_ite_eq, if_neg]
        intro h
        have := (mem_filter.1 h).2
        rw [mabs_tupleCount] at this
        exact hkm this
    rw [sum_congr rfl e2, sum_ite_eq' (range (m + 1)) m, if_pos (self_mem_range_succ m)]
    refine sum_congr rfl fun J _ => ?_
    rw [prod_eq_mpow]
  · intro u hu x
    simp only [diffOp, hb]
    rw [sum_comm]
    refine sum_congr rfl fun k hk => ?_
    rw [sum_comm]
    refine sum_congr rfl fun J _ => ?_
    rw [sum_ite_eq, if_pos (hmemA k hk J), pdT_eq_pderiv hu]

end

end GroundTheory.Automorphic.Sobolev
