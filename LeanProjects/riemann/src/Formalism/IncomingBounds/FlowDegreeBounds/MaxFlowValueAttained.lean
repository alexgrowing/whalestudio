import Mathlib
import Formalism.IncomingBounds.IncomingBound

noncomputable section
open scoped BigOperators
open Set
open scoped Pointwise

namespace Formalism.IncomingBounds

namespace FlowLoadBounds

variable {l d : ℕ} [NeZero d]

def dpLoad (l d : ℕ) [NeZero d] (x : ZMod d → ℕ → ℝ) (s : ZMod d) : ℝ :=
  (∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i) + ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i

theorem load_zero (s : ZMod d) : dpLoad l d 0 s = 0 := by simp [dpLoad]

theorem flowVal_zero : flowVal d (0 : ZMod d → ℕ → ℝ) = 0 := by simp [Formalism.IncomingBounds.flowVal]

theorem pair_eq (x : ZMod d → ℕ → ℝ) (a : ZMod d → ℝ) :
    ∑ s, a s * dpLoad l d x s =
      ∑ s, ∑ i ∈ oddLevels d, ((l : ℝ) ^ i * a s + a (s + (i : ZMod d))) * x s i := by
  have h2 : ∀ i : ℕ, ∑ s, a s * x (s - (i : ZMod d)) i = ∑ s, a (s + (i : ZMod d)) * x s i :=
    fun i => Fintype.sum_equiv (Equiv.subRight (i : ZMod d)) _ _ (fun s => by simp)
  simp only [dpLoad, mul_add, add_mul, Finset.mul_sum, Finset.sum_add_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => by ring
  · rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => h2 i

theorem weak_core {D : ZMod d → ℝ} {x : ZMod d → ℕ → ℝ} {sig : ZMod d → ℝ}
    (hx : IsFlow l d D x) (h0 : ∀ s, 0 ≤ sig s)
    (h1 : ∀ s, ∀ i ∈ oddLevels d, 1 ≤ (l : ℝ) ^ i * sig s + sig (s + (i : ZMod d))) :
    flowVal d x ≤ ∑ s, D s * sig s := by
  calc Formalism.IncomingBounds.flowVal d x = ∑ s, ∑ i ∈ oddLevels d, 1 * x s i := by simp [Formalism.IncomingBounds.flowVal]
    _ ≤ ∑ s, ∑ i ∈ oddLevels d, ((l : ℝ) ^ i * sig s + sig (s + (i : ZMod d))) * x s i :=
        Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun i hi =>
          mul_le_mul_of_nonneg_right (h1 s i hi) (hx.1 s i)
    _ = ∑ s, sig s * dpLoad l d x s := (pair_eq x sig).symm
    _ ≤ ∑ s, D s * sig s := Finset.sum_le_sum fun s _ => by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (hx.2 s) (h0 s)

theorem coord_le_load (hl : 1 ≤ l) {x : ZMod d → ℕ → ℝ} (hx : ∀ s i, 0 ≤ x s i) (s : ZMod d)
    {i : ℕ} (hi : i ∈ oddLevels d) : x s i ≤ dpLoad l d x s := by
  have hl' : (1 : ℝ) ≤ (l : ℝ) ^ i := by
    have h : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
    exact one_le_pow₀ h
  have h1 : x s i ≤ (l : ℝ) ^ i * x s i := le_mul_of_one_le_left (hx s i) hl'
  have h2 : (l : ℝ) ^ i * x s i ≤ ∑ j ∈ oddLevels d, (l : ℝ) ^ j * x s j :=
    Finset.single_le_sum (f := fun j => (l : ℝ) ^ j * x s j)
      (fun j _ => mul_nonneg (by positivity) (hx s j)) hi
  have h3 : 0 ≤ ∑ j ∈ oddLevels d, x (s - (j : ZMod d)) j := Finset.sum_nonneg fun j _ => hx _ _
  unfold dpLoad
  linarith

theorem continuous_load (s : ZMod d) : Continuous fun x : ZMod d → ℕ → ℝ => dpLoad l d x s := by
  unfold dpLoad
  fun_prop

theorem continuous_flowVal : Continuous fun x : ZMod d → ℕ → ℝ => flowVal d x := by
  unfold Formalism.IncomingBounds.flowVal
  fun_prop

def trunc (d : ℕ) [NeZero d] (x : ZMod d → ℕ → ℝ) : ZMod d → ℕ → ℝ :=
  fun s i => if i ∈ oddLevels d then x s i else 0

theorem load_trunc (x : ZMod d → ℕ → ℝ) (s : ZMod d) :
    dpLoad l d (trunc d x) s = dpLoad l d x s := by
  simp only [dpLoad, trunc]
  congr 1 <;> refine Finset.sum_congr rfl fun i hi => ?_ <;> simp [hi]

theorem flowVal_trunc (x : ZMod d → ℕ → ℝ) : flowVal d (trunc d x) = flowVal d x := by
  simp only [Formalism.IncomingBounds.flowVal, trunc]
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i hi => if_pos hi

theorem trunc_nonneg {x : ZMod d → ℕ → ℝ} (hx : ∀ s i, 0 ≤ x s i) : ∀ s i, 0 ≤ trunc d x s i := by
  intro s i
  simp only [trunc]
  split_ifs
  · exact hx s i
  · exact le_rfl

theorem trunc_le (hl : 1 ≤ l) {x : ZMod d → ℕ → ℝ} (hx : ∀ s i, 0 ≤ x s i) {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ s, dpLoad l d x s ≤ R) : ∀ s i, trunc d x s i ≤ R := by
  intro s i
  simp only [trunc]
  split_ifs with hi
  · exact (coord_le_load hl hx s hi).trans (h s)
  · exact hR

def box (d : ℕ) (R : ℝ) : Set (ZMod d → ℕ → ℝ) := Set.pi univ fun _ => Set.pi univ fun _ => Icc 0 R

theorem isCompact_box (R : ℝ) : IsCompact (box d R) := by
  unfold box
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc

theorem mem_box {R : ℝ} {x : ZMod d → ℕ → ℝ} : x ∈ box d R ↔ ∀ s i, 0 ≤ x s i ∧ x s i ≤ R := by
  simp only [box, Set.mem_univ_pi, Set.mem_Icc]

private theorem isFlow_zero_of_nonneg {D : ZMod d → ℝ} (hD : 0 ≤ D) : IsFlow l d D 0 := by
  unfold IsFlow
  exact ⟨fun s i => by simp, fun s => by simpa using hD s⟩

theorem exists_opt_flow (hl : 1 ≤ l) (D : ZMod d → ℝ) (hD : 0 ≤ D) :
    ∃ x, IsFlow l d D x ∧ ∀ y, IsFlow l d D y → flowVal d y ≤ flowVal d x := by
  have hclosed : IsClosed {x : ZMod d → ℕ → ℝ | IsFlow l d D x} := by
    have e : {x : ZMod d → ℕ → ℝ | IsFlow l d D x} =
        (⋂ s, ⋂ i, {x : ZMod d → ℕ → ℝ | 0 ≤ x s i}) ∩ ⋂ s, {x | dpLoad l d x s ≤ D s} := by
      ext x
      simp [IsFlow, dpLoad]
    rw [e]
    exact (isClosed_iInter fun s => isClosed_iInter fun i =>
      isClosed_le continuous_const
        (by fun_prop : Continuous fun x : ZMod d → ℕ → ℝ => x s i)).inter
      (isClosed_iInter fun s : ZMod d =>
        isClosed_le (continuous_load (l := l) (d := d) s) continuous_const)
  have hR : 0 ≤ ∑ s, D s := Finset.sum_nonneg fun s _ => hD s
  have hK : IsCompact (box d (∑ s, D s) ∩ {x | IsFlow l d D x}) :=
    (isCompact_box _).inter_right hclosed
  have h0 : (0 : ZMod d → ℕ → ℝ) ∈ box d (∑ s, D s) ∩ {x | IsFlow l d D x} :=
    ⟨mem_box.2 fun s i => ⟨by simp, by simpa using hR⟩, isFlow_zero_of_nonneg hD⟩
  obtain ⟨x, hxK, hxmax⟩ := hK.exists_isMaxOn ⟨0, h0⟩ continuous_flowVal.continuousOn
  refine ⟨x, hxK.2, fun y hy => ?_⟩
  have hyF : IsFlow l d D (trunc d y) := by
    unfold IsFlow
    exact ⟨trunc_nonneg hy.1, fun s => (load_trunc (l := l) y s).trans_le (hy.2 s)⟩
  have hyK : trunc d y ∈ box d (∑ s, D s) ∩ {x | IsFlow l d D x} :=
    ⟨mem_box.2 fun s i => ⟨trunc_nonneg hy.1 s i, trunc_le hl hy.1 hR
      (fun s => (hy.2 s).trans (Finset.single_le_sum (fun t _ => hD t) (Finset.mem_univ s))) s i⟩, hyF⟩
  calc Formalism.IncomingBounds.flowVal d y = Formalism.IncomingBounds.flowVal d (trunc d y) := (flowVal_trunc y).symm
    _ ≤ Formalism.IncomingBounds.flowVal d x := isMaxOn_iff.1 hxmax _ hyK

theorem maxFlow_eq {D : ZMod d → ℝ} {x : ZMod d → ℕ → ℝ} (hx : IsFlow l d D x)
    (hmax : ∀ y, IsFlow l d D y → flowVal d y ≤ flowVal d x) : maxFlow l d D = flowVal d x := by
  unfold Formalism.IncomingBounds.maxFlow
  refine IsGreatest.csSup_eq ⟨⟨x, hx, rfl⟩, ?_⟩
  rintro t ⟨y, hy, rfl⟩
  exact hmax y hy

theorem sum_comb {ι : Type*} (S : Finset ι) (f g c : ι → ℝ) (a b : ℝ) :
    ∑ i ∈ S, c i * (a * f i + b * g i) = a * ∑ i ∈ S, c i * f i + b * ∑ i ∈ S, c i * g i := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem sum_comb' {ι : Type*} (S : Finset ι) (f g : ι → ℝ) (a b : ℝ) :
    ∑ i ∈ S, (a * f i + b * g i) = a * ∑ i ∈ S, f i + b * ∑ i ∈ S, g i := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]

theorem load_comb (x y : ZMod d → ℕ → ℝ) (a b : ℝ) (s : ZMod d) :
    dpLoad l d (fun s i => a * x s i + b * y s i) s = a * dpLoad l d x s + b * dpLoad l d y s := by
  have e1 : ∑ i ∈ oddLevels d, (l : ℝ) ^ i * (a * x s i + b * y s i) =
      a * ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i + b * ∑ i ∈ oddLevels d, (l : ℝ) ^ i * y s i :=
    sum_comb _ _ _ _ _ _
  have e2 : ∑ i ∈ oddLevels d, (a * x (s - (i : ZMod d)) i + b * y (s - (i : ZMod d)) i) =
      a * ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i + b * ∑ i ∈ oddLevels d, y (s - (i : ZMod d)) i :=
    sum_comb' _ _ _ _ _
  simp only [dpLoad]
  rw [e1, e2]
  ring

theorem flowVal_comb (x y : ZMod d → ℕ → ℝ) (a b : ℝ) :
    flowVal d (fun s i => a * x s i + b * y s i) = a * flowVal d x + b * flowVal d y := by
  calc Formalism.IncomingBounds.flowVal d (fun s i => a * x s i + b * y s i)
        = ∑ s, (a * ∑ i ∈ oddLevels d, x s i + b * ∑ i ∈ oddLevels d, y s i) :=
          Finset.sum_congr rfl fun s _ => sum_comb' _ _ _ _ _
    _ = a * Formalism.IncomingBounds.flowVal d x + b * Formalism.IncomingBounds.flowVal d y := sum_comb' _ _ _ _ _

def Kset (l d : ℕ) [NeZero d] : Set ((ZMod d → ℝ) × ℝ) :=
  {q | ∃ x : ZMod d → ℕ → ℝ, (∀ s i, 0 ≤ x s i) ∧ (∀ s, dpLoad l d x s ≤ q.1 s) ∧
    q.2 ≤ flowVal d x}

private theorem mem_Kset_iff' {q : (ZMod d → ℝ) × ℝ} :
    q ∈ Kset l d ↔ ∃ x : ZMod d → ℕ → ℝ, (∀ s i, 0 ≤ x s i) ∧
      (∀ s, dpLoad l d x s ≤ q.1 s) ∧ q.2 ≤ Formalism.IncomingBounds.flowVal d x := Iff.rfl

theorem convex_K : Convex ℝ (Kset l d) := by
  intro q1 hq1 q2 hq2 a b ha hb hab
  obtain ⟨x1, h1n, h1l, h1v⟩ := mem_Kset_iff'.1 hq1
  obtain ⟨x2, h2n, h2l, h2v⟩ := mem_Kset_iff'.1 hq2
  refine mem_Kset_iff'.2 ⟨fun s i => a * x1 s i + b * x2 s i,
    fun s i => add_nonneg (mul_nonneg ha (h1n s i)) (mul_nonneg hb (h2n s i)), fun s => ?_, ?_⟩
  · rw [load_comb]
    simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left (h1l s) ha) (mul_le_mul_of_nonneg_left (h2l s) hb)
  · rw [flowVal_comb]
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left h1v ha) (mul_le_mul_of_nonneg_left h2v hb)

def gmap (l d : ℕ) [NeZero d] (x : ZMod d → ℕ → ℝ) : (ZMod d → ℝ) × ℝ :=
  (fun s => dpLoad l d x s, flowVal d x)

def Cset (d : ℕ) : Set ((ZMod d → ℝ) × ℝ) := {q | (∀ s, 0 ≤ q.1 s) ∧ q.2 ≤ 0}

theorem isClosed_K (hl : 1 ≤ l) : IsClosed (Kset l d) := by
  refine IsSeqClosed.isClosed ?_
  intro q p hq hlim
  have hq' : ∀ n, ∃ x : ZMod d → ℕ → ℝ, (∀ s i, 0 ≤ x s i) ∧ (∀ s, dpLoad l d x s ≤ (q n).1 s) ∧
      (q n).2 ≤ Formalism.IncomingBounds.flowVal d x := fun n => mem_Kset_iff'.1 (hq n)
  choose x hxn hxl hxv using hq'
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto q hlim).exists_norm_le
  have hC' : ∀ n s, (q n).1 s ≤ C := fun n s => by
    have h1 : ‖(q n).1 s‖ ≤ C :=
      (norm_le_pi_norm (q n).1 s).trans ((norm_fst_le (q n)).trans (hC _ ⟨n, rfl⟩))
    rw [Real.norm_eq_abs] at h1
    exact (le_abs_self _).trans h1
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC _ ⟨0, rfl⟩)
  have hy : ∀ n, trunc d (x n) ∈ box d C := fun n => mem_box.2 fun s i =>
    ⟨trunc_nonneg (hxn n) s i,
      trunc_le hl (hxn n) hC0 (fun s => (hxl n s).trans (hC' n s)) s i⟩
  obtain ⟨z, hz, φ, hφ, hzlim⟩ := (isCompact_box C).tendsto_subseq hy
  have hqφ : Filter.Tendsto (q ∘ φ) Filter.atTop (nhds p) := hlim.comp hφ.tendsto_atTop
  refine mem_Kset_iff'.2 ⟨z, fun s i => ((mem_box.1 hz) s i).1, fun s => ?_, ?_⟩
  · have h1 : Filter.Tendsto (fun n => dpLoad l d (trunc d (x (φ n))) s) Filter.atTop
        (nhds (dpLoad l d z s)) := ((continuous_load (l := l) s).tendsto z).comp hzlim
    have h2 : Filter.Tendsto (fun n => (q (φ n)).1 s) Filter.atTop (nhds (p.1 s)) :=
      (((continuous_apply s).comp continuous_fst).tendsto p).comp hqφ
    exact le_of_tendsto_of_tendsto' h1 h2 fun n =>
      (load_trunc (l := l) (x (φ n)) s).trans_le (hxl (φ n) s)
  · have h1 : Filter.Tendsto (fun n => (q (φ n)).2) Filter.atTop (nhds p.2) :=
      (continuous_snd.tendsto p).comp hqφ
    have h2 : Filter.Tendsto (fun n => Formalism.IncomingBounds.flowVal d (trunc d (x (φ n)))) Filter.atTop
        (nhds (Formalism.IncomingBounds.flowVal d z)) := (continuous_flowVal.tendsto z).comp hzlim
    exact le_of_tendsto_of_tendsto' h1 h2 fun n =>
      (hxv (φ n)).trans (flowVal_trunc (x (φ n))).ge

theorem exists_dual_lt (hl : 1 ≤ l) (D : ZMod d → ℝ) (hD : 0 ≤ D) {v : ℝ}
    (hv : ∀ y, IsFlow l d D y → flowVal d y ≤ v) {ε : ℝ} (hε : 0 < ε) :
    ∃ sig : ZMod d → ℝ, (∀ s, 0 ≤ sig s) ∧
      (∀ s, ∀ i ∈ oddLevels d, 1 ≤ (l : ℝ) ^ i * sig s + sig (s + (i : ZMod d))) ∧
      ∑ s, D s * sig s < v + ε := by
  have hv0 : 0 ≤ v := by simpa [flowVal_zero] using hv 0 (isFlow_zero_of_nonneg hD)
  have hnot : ((D, v + ε) : (ZMod d → ℝ) × ℝ) ∉ Kset l d := by
    intro hmem
    obtain ⟨x, hxn, hxl, hxv⟩ := mem_Kset_iff'.1 hmem
    have hxF : IsFlow l d D x := by
      unfold IsFlow
      exact ⟨hxn, hxl⟩
    have h1 := hv x hxF
    have h2 : v + ε ≤ Formalism.IncomingBounds.flowVal d x := hxv
    linarith
  obtain ⟨f, u, hfu, hfb⟩ :=
    geometric_hahn_banach_point_closed (convex_K (l := l) (d := d))
      (isClosed_K hl) hnot
  have key : ∀ q : (ZMod d → ℝ) × ℝ, f q = ∑ t, q.1 t * f ((Pi.single t (1 : ℝ) : ZMod d → ℝ), (0 : ℝ)) +
      q.2 * f ((0 : ZMod d → ℝ), (1 : ℝ)) := by
    intro q
    have hq : q = ∑ t, q.1 t • ((Pi.single t (1 : ℝ) : ZMod d → ℝ), (0 : ℝ)) +
        q.2 • ((0 : ZMod d → ℝ), (1 : ℝ)) := by
      refine Prod.ext ?_ ?_
      · funext t'
        simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
      · simp [Prod.snd_sum]
    conv_lhs => rw [hq]
    simp only [map_add, map_sum, map_smul, smul_eq_mul]
  obtain ⟨a, c, key'⟩ : ∃ (a : ZMod d → ℝ) (c : ℝ),
      ∀ q : (ZMod d → ℝ) × ℝ, f q = ∑ t, q.1 t * a t + q.2 * c := ⟨_, _, key⟩
  have hrec : ∀ q : (ZMod d → ℝ) × ℝ, (∀ s, 0 ≤ q.1 s) → q.2 ≤ 0 → q ∈ Kset l d :=
    fun q h1 h2 => mem_Kset_iff'.2 ⟨0, fun _ _ => by simp,
      fun s => by simpa [load_zero] using h1 s, by simpa [flowVal_zero] using h2⟩
  have hu : u < 0 := by simpa using hfb 0 (hrec 0 (fun s => by simp) (by simp))
  have hat : ∀ t, f ((Pi.single t (1 : ℝ) : ZMod d → ℝ), (0 : ℝ)) = a t := by
    intro t
    rw [key']
    simp [Pi.single_apply]
  have ha : ∀ t, 0 ≤ a t := by
    intro t
    by_contra hneg
    push_neg at hneg
    have hq : ((u / a t) • ((Pi.single t (1 : ℝ) : ZMod d → ℝ), (0 : ℝ))) ∈ Kset l d := by
      refine hrec _ (fun s => ?_) (by simp)
      simp only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
      refine mul_nonneg (div_pos_iff.2 (Or.inr ⟨hu, hneg⟩)).le ?_
      rw [Pi.single_apply]
      split_ifs <;> norm_num
    have h1 := hfb _ hq
    rw [map_smul, hat, smul_eq_mul, div_mul_cancel₀ _ hneg.ne] at h1
    exact lt_irrefl _ h1
  have hc : c < 0 := by
    by_contra hc'
    push_neg at hc'
    have h1 := key' (D, v + ε)
    dsimp only at h1
    have h2 : 0 ≤ ∑ t, D t * a t := Finset.sum_nonneg fun t _ => mul_nonneg (hD t) (ha t)
    have h3 : 0 ≤ (v + ε) * c := mul_nonneg (by linarith) hc'
    linarith
  have hcpos : 0 < -c := neg_pos.2 hc
  have hw : ∀ s, ∀ i ∈ oddLevels d, 0 ≤ (l : ℝ) ^ i * a s + a (s + (i : ZMod d)) + c := by
    intro s i hi
    by_contra hw0
    push_neg at hw0
    obtain ⟨W, hW⟩ : ∃ W : ℝ, W = (l : ℝ) ^ i * a s + a (s + (i : ZMod d)) + c := ⟨_, rfl⟩
    rw [← hW] at hw0
    have hτ : 0 < u / W := div_pos_iff.2 (Or.inr ⟨hu, hw0⟩)
    obtain ⟨x, hxdef⟩ : ∃ x : ZMod d → ℕ → ℝ,
        x = fun t j => if j = i then (if t = s then u / W else 0) else 0 := ⟨_, rfl⟩
    have hx0 : ∀ t j, 0 ≤ x t j := by
      intro t j
      simp only [hxdef]
      split_ifs <;> first | exact hτ.le | exact le_rfl
    have hsum : ∀ g : ZMod d → ℕ → ℝ, ∑ t, ∑ j ∈ oddLevels d, g t j * x t j = g s i * (u / W) := by
      intro g
      simp [hxdef, mul_ite, Finset.sum_ite_eq', hi]
    have hflow : Formalism.IncomingBounds.flowVal d x = u / W := by
      have h := hsum (fun _ _ => 1)
      simp only [one_mul] at h
      exact h
    have hq : ((fun t => dpLoad l d x t, Formalism.IncomingBounds.flowVal d x) : (ZMod d → ℝ) × ℝ) ∈ Kset l d :=
      mem_Kset_iff'.2 ⟨x, hx0, fun t => le_rfl, le_rfl⟩
    have h1 := hfb _ hq
    rw [key'] at h1
    dsimp only at h1
    have h2 : ∑ t, dpLoad l d x t * a t = ((l : ℝ) ^ i * a s + a (s + (i : ZMod d))) * (u / W) := by
      rw [← hsum (fun t j => (l : ℝ) ^ j * a t + a (t + (j : ZMod d))), ← pair_eq]
      exact Finset.sum_congr rfl fun t _ => mul_comm _ _
    rw [h2, hflow] at h1
    have h3 : u / W * W = u := div_mul_cancel₀ _ hw0.ne
    have h4 : ((l : ℝ) ^ i * a s + a (s + (i : ZMod d))) * (u / W) + u / W * c = u / W * W := by
      rw [hW]
      ring
    linarith
  refine ⟨fun s => a s / -c, fun s => div_nonneg (ha s) hcpos.le, fun s i hi => ?_, ?_⟩
  · show 1 ≤ (l : ℝ) ^ i * (a s / -c) + a (s + (i : ZMod d)) / -c
    rw [show (l : ℝ) ^ i * (a s / -c) + a (s + (i : ZMod d)) / -c =
        ((l : ℝ) ^ i * a s + a (s + (i : ZMod d))) / -c by ring, le_div_iff₀ hcpos]
    linarith [hw s i hi]
  · show ∑ s, D s * (a s / -c) < v + ε
    have h1 := key' (D, v + ε)
    dsimp only at h1
    rw [show ∑ s, D s * (a s / -c) = (∑ s, D s * a s) / -c by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun s _ => by ring, div_lt_iff₀ hcpos]
    linarith

theorem clip_dual (hl : 1 ≤ l) {τ : ZMod d → ℝ} (h0 : ∀ s, 0 ≤ τ s)
    (h1 : ∀ s, ∀ i ∈ oddLevels d, 1 ≤ (l : ℝ) ^ i * τ s + τ (s + (i : ZMod d))) :
    IsDual l d (fun s => min (τ s) 1) := by
  refine ⟨fun s => ⟨le_min (h0 s) zero_le_one, min_le_right _ _⟩, fun s i hi => ?_⟩
  show 1 ≤ (l : ℝ) ^ i * min (τ s) 1 + min (τ (s + (i : ZMod d))) 1
  have hl' : (1 : ℝ) ≤ (l : ℝ) ^ i := by
    have h : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
    exact one_le_pow₀ h
  have hτ := h1 s i hi
  have hp : 0 ≤ (l : ℝ) ^ i * τ s := mul_nonneg (by positivity) (h0 s)
  have hq := h0 (s + (i : ZMod d))
  rcases le_total (τ s) 1 with h | h <;> rcases le_total (τ (s + (i : ZMod d))) 1 with h' | h'
  · rw [min_eq_left h, min_eq_left h']
    exact hτ
  · rw [min_eq_left h, min_eq_right h']
    linarith
  · rw [min_eq_right h, min_eq_left h']
    linarith
  · rw [min_eq_right h, min_eq_right h']
    linarith

theorem isCompact_dual : IsCompact {sig : ZMod d → ℝ | IsDual l d sig} := by
  have e : {sig : ZMod d → ℝ | Formalism.IncomingBounds.IsDual l d sig} =
      ((⋂ s, {sig : ZMod d → ℝ | 0 ≤ sig s}) ∩ ⋂ s, {sig : ZMod d → ℝ | sig s ≤ 1}) ∩
        ⋂ s, ⋂ i ∈ oddLevels d, {sig : ZMod d → ℝ | 1 ≤ (l : ℝ) ^ i * sig s + sig (s + (i : ZMod d))} := by
    ext sig
    simp only [Formalism.IncomingBounds.IsDual, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, forall_and]
  have hclosed : IsClosed {sig : ZMod d → ℝ | Formalism.IncomingBounds.IsDual l d sig} := by
    rw [e]
    exact ((isClosed_iInter fun s => isClosed_le continuous_const (continuous_apply s)).inter
      (isClosed_iInter fun s => isClosed_le (continuous_apply s) continuous_const)).inter
      (isClosed_iInter fun s => isClosed_biInter fun i _ =>
        isClosed_le continuous_const (by fun_prop))
  refine (isCompact_univ_pi fun _ : ZMod d => isCompact_Icc (a := (0 : ℝ)) (b := 1)).of_isClosed_subset
    hclosed ?_
  intro sig hsig
  have hs : Formalism.IncomingBounds.IsDual l d sig := hsig
  exact Set.mem_univ_pi.2 fun s => hs.1 s

theorem strong (hl : 1 ≤ l) (D : ZMod d → ℝ) (hD : 0 ≤ D) :
    ∃ sig, IsDual l d sig ∧ ∑ s, D s * sig s = maxFlow l d D := by
  obtain ⟨x, hx, hmax⟩ := exists_opt_flow hl D hD
  rw [maxFlow_eq hx hmax]
  have hone : (fun _ => (1 : ℝ)) ∈ {sig : ZMod d → ℝ | Formalism.IncomingBounds.IsDual l d sig} := by
    show Formalism.IncomingBounds.IsDual l d (fun _ => (1 : ℝ))
    refine ⟨fun s => ⟨zero_le_one, le_rfl⟩, fun s i _ => ?_⟩
    show 1 ≤ (l : ℝ) ^ i * 1 + 1
    have : (0 : ℝ) ≤ (l : ℝ) ^ i := by positivity
    linarith
  obtain ⟨σ, hσ, hmin⟩ := (isCompact_dual (l := l) (d := d)).exists_isMinOn ⟨_, hone⟩
    (by fun_prop : Continuous fun σ : ZMod d → ℝ => ∑ s, D s * σ s).continuousOn
  have hσ' : Formalism.IncomingBounds.IsDual l d σ := hσ
  refine ⟨σ, hσ', le_antisymm ?_ (weak_core hx (fun s => (hσ'.1 s).1) hσ'.2)⟩
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨τ, h0, h1, hlt⟩ := exists_dual_lt hl D hD (fun y hy => hmax y hy) hε
  have hfeas := clip_dual hl h0 h1
  have h2 : ∑ s, D s * σ s ≤ ∑ s, D s * min (τ s) 1 := isMinOn_iff.1 hmin _ hfeas
  have h3 : ∑ s, D s * min (τ s) 1 ≤ ∑ s, D s * τ s :=
    Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (min_le_left _ _) (hD s)
  linarith

theorem dualAll_of_dual (hl : 1 ≤ l) (hev : Even d) {σ : ZMod d → ℝ} (h : IsDual l d σ) :
    IsDualAll l d σ := by
  intro s i hi
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hr : i % d ∈ oddLevels d := by
    simp only [oddLevels, Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.mod_lt _ hd, ?_⟩
    rw [Nat.odd_iff, Nat.mod_mod_of_dvd _ (even_iff_two_dvd.mp hev)]
    exact Nat.odd_iff.mp hi
  have h1 := h.2 s (i % d) hr
  rw [ZMod.natCast_mod] at h1
  have hpow : (l : ℝ) ^ (i % d) ≤ (l : ℝ) ^ i := by
    have h' : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
    exact pow_le_pow_right₀ h' (Nat.mod_le i d)
  have h2 := mul_le_mul_of_nonneg_right hpow (h.1 s).1
  linarith

end FlowLoadBounds

open FlowLoadBounds

theorem weakDuality (l d : ℕ) [NeZero d] (D : ZMod d → ℝ) (x : ZMod d → ℕ → ℝ)
    (sig : ZMod d → ℝ) (hx : IsFlow l d D x) (hsig : IsDual l d sig) :
    flowVal d x ≤ ∑ s, D s * sig s :=
  Formalism.IncomingBounds.FlowLoadBounds.weak_core hx (fun s => (hsig.1 s).1) hsig.2

theorem maxFlowValueAttained : FlowAttained := by
  intro l d _ hl hd hev D hD
  obtain ⟨x, hx, hmax⟩ := Formalism.IncomingBounds.FlowLoadBounds.exists_opt_flow (by omega : 1 ≤ l) D hD
  exact ⟨x, hx, (Formalism.IncomingBounds.FlowLoadBounds.maxFlow_eq hx hmax).symm⟩

theorem strongDuality : LemmaFa := by
  intro l d _ hl hd hev D hD
  have hl1 : 1 ≤ l := by omega
  obtain ⟨σ, hσ, heq⟩ := Formalism.IncomingBounds.FlowLoadBounds.strong hl1 D hD
  obtain ⟨x, hx, hmax⟩ := Formalism.IncomingBounds.FlowLoadBounds.exists_opt_flow hl1 D hD
  have hdef : Fnum l d D = ∑ s, D s * (gam l - σ s) := by
    unfold Fnum
    rw [← heq]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    ring
  refine ⟨⟨σ, hσ, Formalism.IncomingBounds.FlowLoadBounds.dualAll_of_dual hl1 hev hσ, hdef⟩, ⟨σ, hσ, hdef⟩, ?_⟩
  rintro t ⟨τ, hτ, rfl⟩
  have h1 : ∑ s, D s * σ s ≤ ∑ s, D s * τ s := by
    rw [heq, Formalism.IncomingBounds.FlowLoadBounds.maxFlow_eq hx hmax]
    exact weakDuality l d D x τ hx hτ
  rw [hdef]
  simp only [mul_sub, Finset.sum_sub_distrib]
  linarith

end Formalism.IncomingBounds
