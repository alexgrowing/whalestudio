import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.TopBasisCons

variable {S A : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S} {ι : Type} {b : ι → A}

variable (s I b) in

def Approx (x : A) (f : ι → S) : Prop :=
  ∀ n : ℕ, ∃ F : Finset ι, (∀ i, i ∉ F → f i ∈ I ^ n) ∧ x - ∑ i ∈ F, s (f i) * b i ∈ (I ^ n).map s

theorem smodEq_iff (x y : S) (n : ℕ) : x ≡ y [SMOD (I ^ n • ⊤ : Submodule S S)] ↔ x - y ∈ I ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

theorem sum_sub_sum_mem {f : ι → S} {n : ℕ} {F G : Finset ι} (hF : ∀ i, i ∉ F → f i ∈ I ^ n)
    (hG : ∀ i, i ∉ G → f i ∈ I ^ n) :
    ∑ i ∈ F, s (f i) * b i - ∑ i ∈ G, s (f i) * b i ∈ (I ^ n).map s := by
  classical
  rw [← Finset.sum_sdiff (Finset.inter_subset_left : F ∩ G ⊆ F),
    ← Finset.sum_sdiff (Finset.inter_subset_right : F ∩ G ⊆ G), add_sub_add_right_eq_sub]
  refine sub_mem (Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem s (hG i fun h => ?_)))
    (Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem s (hF i fun h => ?_)))
  · exact (Finset.mem_sdiff.1 hi).2 (Finset.mem_inter.2 ⟨(Finset.mem_sdiff.1 hi).1, h⟩)
  · exact (Finset.mem_sdiff.1 hi).2 (Finset.mem_inter.2 ⟨h, (Finset.mem_sdiff.1 hi).1⟩)

theorem Approx.approx {x : A} {f : ι → S} (h : Approx s I b x f) (n : ℕ) (F : Finset ι)
    (hF : ∀ i, i ∉ F → f i ∈ I ^ n) : x - ∑ i ∈ F, s (f i) * b i ∈ (I ^ n).map s := by
  obtain ⟨G, hG, hx⟩ := h n
  have := sub_mem hx (sum_sub_sum_mem (s := s) (b := b) hF hG)
  rwa [sub_sub_sub_cancel_right] at this

theorem Approx.finite {x : A} {f : ι → S} (h : Approx s I b x f) (n : ℕ) : {i | f i ∉ I ^ n}.Finite := by
  obtain ⟨F, hF, -⟩ := h n
  exact F.finite_toSet.subset fun i hi => by_contra fun h' => hi (hF i h')

theorem Approx.add {x y : A} {f g : ι → S} (hx : Approx s I b x f) (hy : Approx s I b y g) :
    Approx s I b (x + y) (f + g) := by
  classical
  intro n
  obtain ⟨F, hF, -⟩ := hx n
  obtain ⟨G, hG, -⟩ := hy n
  refine ⟨F ∪ G, fun i hi => ?_, ?_⟩
  · simp only [Finset.mem_union, not_or] at hi
    exact add_mem (hF i hi.1) (hG i hi.2)
  · have h1 := hx.approx n (F ∪ G) fun i hi => hF i fun h => hi (Finset.mem_union_left _ h)
    have h2 := hy.approx n (F ∪ G) fun i hi => hG i fun h => hi (Finset.mem_union_right _ h)
    convert add_mem h1 h2 using 1
    simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
    ring

theorem Approx.mul {x : A} {f : ι → S} (hx : Approx s I b x f) (a : S) :
    Approx s I b (s a * x) (fun i => a * f i) := by
  intro n
  obtain ⟨F, hF, h⟩ := hx n
  refine ⟨F, fun i hi => Ideal.mul_mem_left _ _ (hF i hi), ?_⟩
  convert Ideal.mul_mem_left _ (s a) h using 1
  simp only [map_mul, mul_sub, Finset.mul_sum, mul_assoc]

theorem approx_single [DecidableEq ι] (i : ι) : Approx s I b (b i) (Pi.single i 1) := by
  intro n
  refine ⟨{i}, fun j hj => ?_, by simp⟩
  rw [Pi.single_eq_of_ne (by simpa using hj)]
  exact zero_mem _

theorem Approx.eq_zero (hH : IsHausdorff I S)
    (hst : ∀ n : ℕ, ∃ m : ℕ, ∀ a : ι →₀ S, a.sum (fun i y => s y * b i) ∈ (I ^ m).map s → ∀ i, a i ∈ I ^ n)
    {h : ι → S} (hh : Approx s I b 0 h) : h = 0 := by
  classical
  funext i
  refine hH.haus (h i) fun n => ?_
  rw [smodEq_iff, sub_zero]
  obtain ⟨m, hm⟩ := hst n
  obtain ⟨F, hF, hs⟩ := hh (max n m)
  by_cases hi : i ∈ F
  · have key := hm (Finsupp.onFinset F (fun j => if j ∈ F then h j else 0)
      (fun j hj => by by_contra hj'; simp [hj'] at hj)) ?_ i
    · simpa [hi] using key
    · rw [Finsupp.onFinset_sum _ (fun j => by simp)]
      have e : ∑ j ∈ F, s (if j ∈ F then h j else 0) * b j = -(0 - ∑ j ∈ F, s (h j) * b j) := by
        rw [zero_sub, neg_neg]
        exact Finset.sum_congr rfl fun j hj => by rw [if_pos hj]
      rw [e]
      exact neg_mem (Ideal.map_mono (Ideal.pow_le_pow_right (le_max_right n m)) hs)
  · exact Ideal.pow_le_pow_right (le_max_left n m) (hF i hi)

end GlobalTheory.BSP.TopBasisCons

namespace GlobalTheory.BSP.TopBasisCons

variable {S A : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S} {ι : Type} {b : ι → A}

theorem exists_step (hsp : ∀ x : A, ∃ a : ι →₀ S, x - a.sum (fun i y => s y * b i) ∈ I.map s) (n : ℕ) (y : A)
    (hy : y ∈ (I ^ n).map s) : ∃ a : ι →₀ S, (∀ i, a i ∈ I ^ n) ∧
      y - a.sum (fun i c => s c * b i) ∈ (I ^ (n + 1)).map s := by
  classical
  let T : A → Prop := fun y => ∃ a : ι →₀ S, (∀ i, a i ∈ I ^ n) ∧
      y - a.sum (fun i c => s c * b i) ∈ (I ^ (n + 1)).map s
  have T0 : T 0 := ⟨0, fun _ => zero_mem _, by simp⟩
  have Tadd : ∀ y y', T y → T y' → T (y + y') := by
    rintro y y' ⟨a, ha, hy⟩ ⟨a', ha', hy'⟩
    refine ⟨a + a', fun i => add_mem (ha i) (ha' i), ?_⟩
    rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by rw [map_add, add_mul])]
    convert add_mem hy hy' using 1
    ring
  have T1 : ∀ t ∈ I ^ n, ∀ w : A, T (s t * w) := by
    intro t ht w
    obtain ⟨a, ha⟩ := hsp w
    refine ⟨t • a, fun i => by rw [Finsupp.smul_apply, smul_eq_mul]; exact Ideal.mul_mem_right _ _ ht, ?_⟩
    rw [Finsupp.sum_smul_index (fun _ => by simp)]
    have e : s t * w - a.sum (fun i c => s (t * c) * b i) = s t * (w - a.sum (fun i c => s c * b i)) := by
      rw [mul_sub, Finsupp.mul_sum]
      simp only [map_mul, mul_assoc]
    rw [e, Ideal.map_pow, pow_succ]
    exact Ideal.mul_mem_mul (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem s ht) ha
  have key : ∀ y' ∈ Submodule.span A (s '' ((I ^ n : Ideal S) : Set S)), ∀ z, T (z * y') := by
    intro y' hy'
    induction hy' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, ht, rfl⟩ := hx
      exact fun z => by rw [mul_comm]; exact T1 t ht z
    | zero => exact fun z => by rw [mul_zero]; exact T0
    | add x x' _ _ hx hx' => exact fun z => by rw [mul_add]; exact Tadd _ _ (hx z) (hx' z)
    | smul a x _ hx => exact fun z => by rw [smul_eq_mul, ← mul_assoc]; exact hx (z * a)
  simpa using key y hy 1

theorem exists_approx (hS : IsPrecomplete I S) (g : ℕ → A → ι →₀ S)
    (hg1 : ∀ n y, y ∈ (I ^ n).map s → ∀ i, g n y i ∈ I ^ n)
    (hg2 : ∀ n y, y ∈ (I ^ n).map s → y - (g n y).sum (fun i c => s c * b i) ∈ (I ^ (n + 1)).map s) (x : A) :
    ∃ f, Approx s I b x f := by
  classical
  let r : ℕ → A := fun n => Nat.rec x (fun k rk => rk - (g k rk).sum (fun i c => s c * b i)) n
  have hrs : ∀ k, r (k + 1) = r k - (g k (r k)).sum (fun i c => s c * b i) := fun k => rfl
  have hrm : ∀ k, r k ∈ (I ^ k).map s := by
    intro k
    induction k with
    | zero => simp [r, Ideal.map_top]
    | succ k ih => rw [hrs]; exact hg2 k _ ih
  let a : ℕ → ι →₀ S := fun k => g k (r k)
  have ha : ∀ k i, a k i ∈ I ^ k := fun k => hg1 k _ (hrm k)
  have hrx : ∀ N, r N = x - ∑ k ∈ Finset.range N, (a k).sum (fun i c => s c * b i) := by
    intro N
    induction N with
    | zero => simp [r]
    | succ N ih => rw [hrs, Finset.sum_range_succ, ← sub_sub, ← ih]
  let P : ℕ → ι → S := fun N i => ∑ k ∈ Finset.range N, a k i
  have hP : ∀ i m n, m ≤ n → P n i - P m i ∈ I ^ m := by
    intro i m n hmn
    rw [← Finset.sum_Ico_eq_sub _ hmn]
    exact Ideal.sum_mem _ fun k hk => Ideal.pow_le_pow_right (Finset.mem_Ico.1 hk).1 (ha k i)
  have hlim : ∀ i, ∃ L, ∀ N, P N i - L ∈ I ^ N := by
    intro i
    obtain ⟨L, hL⟩ := hS.prec (f := fun N => P N i) fun {m n} hmn => by
      rw [smodEq_iff, ← neg_sub]; exact neg_mem (hP i m n hmn)
    exact ⟨L, fun N => (smodEq_iff _ _ _).1 (hL N)⟩
  choose f hf using hlim
  refine ⟨f, fun n => ?_⟩
  let F : Finset ι := (Finset.range n).biUnion fun k => (a k).support
  have hPF : ∀ i, i ∉ F → P n i = 0 := fun i hi => Finset.sum_eq_zero fun k hk => by
    by_contra h
    exact hi (Finset.mem_biUnion.2 ⟨k, hk, Finsupp.mem_support_iff.2 h⟩)
  refine ⟨F, fun i hi => ?_, ?_⟩
  · have := neg_mem (hf i n)
    rwa [hPF i hi, zero_sub, neg_neg] at this
  · have hsum : ∑ k ∈ Finset.range n, (a k).sum (fun i c => s c * b i) = ∑ i ∈ F, s (P n i) * b i := by
      rw [Finset.sum_congr rfl fun k hk => Finsupp.sum_of_support_subset (a k) (s := F)
        (fun i hi => Finset.mem_biUnion.2 ⟨k, hk, hi⟩) (fun i c => s c * b i) (fun _ _ => by simp),
        Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [P, map_sum, Finset.sum_mul]
    have e : x - ∑ i ∈ F, s (f i) * b i = r n + ∑ i ∈ F, s (P n i - f i) * b i := by
      rw [hrx, hsum]
      simp only [map_sub, sub_mul, Finset.sum_sub_distrib]
      ring
    rw [e]
    exact add_mem (hrm n) (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem s (hf i n)))

end GlobalTheory.BSP.TopBasisCons

open GlobalTheory.BSP.TopBasisCons in

theorem GlobalTheory.BSP.exists_topBasis_of_span_of_strict : ∀ (S A : Type) [CommRing S] [CommRing A] (s : S →+* A)
    (I : Ideal S) (ι : Type) (b : ι → A) (i₀ : ι), b i₀ = 1 → I.FG → IsAdicComplete I S →
    IsAdicComplete (I.map s) A → (∀ x : A, ∃ a : ι →₀ S, x - a.sum (fun i y => s y * b i) ∈ I.map s) →
    (∀ n : ℕ, ∃ m : ℕ, ∀ a : ι →₀ S, a.sum (fun i y => s y * b i) ∈ (I ^ m).map s → ∀ i, a i ∈ I ^ n) →
    ∃ TB : TopBasis s I ι, TB.b = b := by
  intro S A _ _ s I ι b i₀ hb0 _ hS hA hsp hst
  classical
  choose! g hg1 hg2 using exists_step (s := s) (I := I) (b := b) hsp
  have hex : ∀ x, ∃ f, Approx s I b x f := exists_approx hS.toIsPrecomplete g hg1 hg2
  choose coef hcoef using hex
  have huniq : ∀ {x : A} {f g : ι → S}, Approx s I b x f → Approx s I b x g → f = g := by
    intro x f g hf hg
    have h := hf.add (hg.mul (-1))
    have e : x + s (-1) * x = 0 := by simp
    rw [e] at h
    have := h.eq_zero hS.toIsHausdorff hst
    funext i
    have hi := congrFun this i
    simp only [Pi.add_apply, Pi.zero_apply, neg_one_mul] at hi
    exact sub_eq_zero.1 (by rw [sub_eq_add_neg]; exact hi)
  let c : ι → A →+ S := fun i =>
    AddMonoidHom.mk' (fun x => coef x i) fun x y => congrFun (huniq (hcoef (x + y)) ((hcoef x).add (hcoef y))) i
  refine ⟨⟨b, c, ?_, ?_, ?_, ?_, ?_, hA, i₀, hb0⟩, rfl⟩
  · intro i a x
    change coef (s a * x) i = a * coef x i
    rw [huniq (hcoef (s a * x)) ((hcoef x).mul a)]
  · intro i
    change coef (b i) i = 1
    rw [huniq (hcoef (b i)) (approx_single i)]
    simp
  · intro i j hij
    change coef (b j) i = 0
    rw [huniq (hcoef (b j)) (approx_single j)]
    exact Pi.single_eq_of_ne hij _
  · intro x n
    exact (hcoef x).finite n
  · intro x n F hF
    exact (hcoef x).approx n F hF
