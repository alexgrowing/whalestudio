import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.VermaCone
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.VermaProductIdentity
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.KhwWeightEqOfIrr

noncomputable section

open Finset Polynomial

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section KRel

variable {X : Type*} [AddCommGroup X] [Module ℂ X] {ε : Fin n → Bool} {A : Fin n → Fin n → Module.End ℂ X}

def IsKRel (ε : Fin n → Bool) (A : Fin n → Fin n → Module.End ℂ X) : Prop :=
  ∀ a b c d : Fin n, ε a = ε b → ε c = ε d → A a b * A c d - A c d * A a b =
    (if b = c then A a d else 0) - (if d = a then A c b else 0)

theorem word_isWeightVector (hA : IsKRel ε A) {ν : Fin n → ℝ} {u : X} (hu : ∀ a, A a a u = (ν a : ℂ) • u) :
    ∀ l, KirrLow ε l → ∀ a, A a a (kirrWord A u l) = (kirrWt ν l a : ℂ) • kirrWord A u l
  | [], _, a => by simpa [kirrWord, kirrWt] using hu a
  | p :: l, hl, a => by
    obtain ⟨b, c⟩ := p
    have hbc := (hl (b, c) List.mem_cons_self).2
    have ih := word_isWeightVector hA hu l (fun q hq => hl q (List.mem_cons_of_mem _ hq)) a
    have key := LinearMap.congr_fun (hA a a b c rfl hbc) (kirrWord A u l)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at key
    simp only [kirrWord, kirrWt]
    rw [sub_eq_iff_eq_add, ih, map_smul] at key
    rw [key]
    by_cases h1 : a = b <;> by_cases h2 : c = a
    · subst h1; subst h2; simp [root]
    · subst h1; (simp [root, h2, Ne.symm h2, add_smul]; abel)
    · subst h2; (simp [root, h1, add_smul]; abel)
    · simp [root, h1, h2, Ne.symm h2]

theorem compact_mem_wordSpan (hA : IsKRel ε A) {ν : Fin n → ℝ} {u : X} (hu : IsKHWVec ε A ν u) :
    ∀ l, KirrLow ε l → ∀ a b, ε a = ε b → A a b (kirrWord A u l) ∈ kirrSpan ε A u := by
  intro l
  induction l with
  | nil =>
    intro _ a b hab
    rcases lt_trichotomy a b with h | rfl | h
    · simp [kirrWord, hu.2 a b h hab]
    · simp only [kirrWord]; rw [hu.1 a]
      exact Submodule.smul_mem _ _ (kirrWord_mem (l := []) u (by simp [KirrLow]))
    · exact kirr_low_mem h hab (kirrWord_mem (l := []) u (by simp [KirrLow]))
  | cons p l ih =>
    intro hl a b hab
    have hl' : KirrLow ε l := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    rcases lt_trichotomy a b with h | rfl | h
    · obtain ⟨x, y⟩ := p
      have hxy := hl (x, y) List.mem_cons_self
      simp only at hxy
      have key := LinearMap.congr_fun (hA a b x y hab hxy.2) (kirrWord A u l)
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at key
      rw [sub_eq_iff_eq_add] at key
      simp only [kirrWord]
      rw [key]
      refine add_mem ?_ (kirr_low_mem hxy.1 hxy.2 (ih hl' a b hab))
      refine sub_mem ?_ ?_
      · split_ifs with h1
        · subst h1; exact ih hl' a y (hab.trans hxy.2)
        · simp
      · split_ifs with h1
        · subst h1; exact ih hl' x b (hxy.2.trans hab)
        · simp
    · rw [word_isWeightVector hA hu.1 _ hl]
      exact Submodule.smul_mem _ _ (kirrWord_mem u hl)
    · exact kirr_low_mem h hab (kirrWord_mem u hl)

theorem wordSpan_isKStable (hA : IsKRel ε A) {ν : Fin n → ℝ} {u : X} (hu : IsKHWVec ε A ν u) :
    IsKStableSub ε A (kirrSpan ε A u) := by
  intro a b hab v hv
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    exact compact_mem_wordSpan hA hu l hl a b hab
  | zero => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | smul c x _ hx => simpa using Submodule.smul_mem _ c hx

theorem commute_aeval_of_commute_alt {B : Module.End ℂ X} (hB : ∀ a b, ε a = ε b → Commute (A a b) B) (u : X) :
    ∀ l, KirrLow ε l → kirrWord A (B u) l = B (kirrWord A u l)
  | [], _ => rfl
  | p :: l, hl => by
    simp only [kirrWord]
    rw [commute_aeval_of_commute_alt hB u l (fun q hq => hl q (List.mem_cons_of_mem _ hq))]
    have := (hB p.1 p.2 (hl p List.mem_cons_self).2).eq
    exact LinearMap.congr_fun this _

end KRel

section Cone

theorem root_swap_eq_neg {x y : Fin n → ℝ} (hx : InRootCone x) (hy : InRootCone y) : InRootCone (x + y) := by
  obtain ⟨m, rfl⟩ := hx
  obtain ⟨m', rfl⟩ := hy
  refine ⟨fun a b => m a b + m' a b, ?_⟩
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs
  · push_cast; rw [add_smul]
  · simp

theorem root_mem_rootCone {a b : Fin n} (h : a < b) : InRootCone (root a b) := by
  simpa using vc_inRootCone_add_root vc_inRootCone_zero' h

theorem partialSum_finset_sum (a b : Fin n) : root b a = -root a b := by
  unfold root; abel

theorem weight_sub_mem_rootCone {ε : Fin n → Bool} (ν : Fin n → ℝ) :
    ∀ l, KirrLow ε l → InRootCone (ν - kirrWt ν l)
  | [], _ => by simpa [kirrWt] using (vc_inRootCone_zero' : InRootCone (0 : Fin n → ℝ))
  | p :: l, hl => by
    have ih := weight_sub_mem_rootCone ν l (fun q hq => hl q (List.mem_cons_of_mem _ hq))
    have hp := (hl p List.mem_cons_self).1
    have e : ν - kirrWt ν (p :: l) = (ν - kirrWt ν l) + root p.2 p.1 := by
      simp only [kirrWt, partialSum_finset_sum p.2 p.1]; abel
    rw [e]
    exact root_swap_eq_neg ih (root_mem_rootCone hp)

theorem wordAction_commute {ι : Type*} (t : Finset ι) (f : ι → Fin n → ℝ) (k : ℕ) :
    kirrPs k (∑ i ∈ t, f i) = ∑ i ∈ t, kirrPs k (f i) := by
  unfold kirrPs
  simp only [Finset.sum_apply]
  exact Finset.sum_comm

theorem partialSum_root_eq (k : ℕ) (x y : Fin n) :
    kirrPs k (root x y) = (if (x : ℕ) < k then 1 else 0) - (if (y : ℕ) < k then 1 else 0) := by
  unfold kirrPs root
  simp only [Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_pi_single', Finset.mem_filter,
    Finset.mem_univ, true_and]

theorem partialSum_nonneg_of_rootCone {β : Fin n → ℝ} (hβ : InRootCone β) (k : ℕ) : 0 ≤ kirrPs k β := by
  obtain ⟨m, rfl⟩ := hβ
  rw [wordAction_commute]
  refine Finset.sum_nonneg fun a _ => ?_
  rw [wordAction_commute]
  refine Finset.sum_nonneg fun b _ => ?_
  split_ifs with h
  · have e : kirrPs k ((m a b : ℝ) • root a b) = (m a b : ℝ) * kirrPs k (root a b) := by
      simp [kirrPs, Finset.mul_sum]
    rw [e, partialSum_root_eq]
    have : (a : ℕ) < b := h
    refine mul_nonneg (by positivity) ?_
    split_ifs <;> first | omega | norm_num
  · simp [kirrPs]

theorem not_rootCone_of_ne {ε : Fin n → Bool} (ν : Fin n → ℝ) :
    ∀ l, KirrLow ε l → l ≠ [] → ¬ InRootCone (kirrWt ν l - ν)
  | [], _, h => (h rfl).elim
  | p :: l, hl, _ => by
    intro hc
    have hp := (hl p List.mem_cons_self).1
    have hle := kirrPs_wt ((p.2 : ℕ) + 1) ν l (fun q hq => hl q (List.mem_cons_of_mem _ hq))
    have h1 := partialSum_nonneg_of_rootCone hc ((p.2 : ℕ) + 1)
    have e : kirrPs ((p.2 : ℕ) + 1) (kirrWt ν (p :: l) - ν) =
        kirrPs ((p.2 : ℕ) + 1) (kirrWt ν l) + kirrPs ((p.2 : ℕ) + 1) (root p.1 p.2) -
          kirrPs ((p.2 : ℕ) + 1) ν := by
      simp [kirrPs, kirrWt, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [e, partialSum_root_eq] at h1
    have : (p.2 : ℕ) < p.1 := hp
    rw [if_neg (by omega), if_pos (by omega)] at h1
    linarith

end Cone

section Poly

variable {U₁ U₂ : Type*} [AddCommGroup U₁] [Module ℂ U₁] [AddCommGroup U₂] [Module ℂ U₂]

theorem rootCone_add_mem (T : U₁ →ₗ[ℂ] U₂) (A : Module.End ℂ U₁) (B : Module.End ℂ U₂)
    (h : ∀ x, T (A x) = B (T x)) (k : ℕ) : ∀ x, T ((A ^ k) x) = (B ^ k) (T x) := by
  induction k with
  | zero => intro x; simp
  | succ k ih => intro x; rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]

theorem aeval_intertwine_alt (T : U₁ →ₗ[ℂ] U₂) (A : Module.End ℂ U₁) (B : Module.End ℂ U₂)
    (h : ∀ x, T (A x) = B (T x)) (p : ℂ[X]) (x : U₁) : T (aeval A p x) = aeval B p (T x) := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, rootCone_add_mem T A B h]

theorem aeval_eigenvector {B : Module.End ℂ U₂} {c : ℂ} {y : U₂} (hy : B y = c • y) (p : ℂ[X]) :
    aeval B p y = p.eval c • y := by
  have hp : ∀ k : ℕ, (B ^ k) y = c ^ k • y := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hy, smul_smul, pow_succ', mul_comm]
  rw [aeval_eq_sum_range, eval_eq_sum_range, LinearMap.sum_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, hp, smul_smul]

theorem lagrangeFactor_eval_ne_zero {C B : Module.End ℂ U₂} (h : Commute C B) (p : ℂ[X]) : Commute C (aeval B p) := by
  rw [aeval_eq_sum_range]
  exact Commute.sum_right _ _ _ fun i _ => (h.pow_right i).smul_right _

theorem prodShift_eq_aeval (A : Module.End ℂ U₂) (θ : Fin n → ℝ) :
    prodShift A θ = aeval A (∏ t, (X - C ((θ t : ℝ) : ℂ))) := by
  unfold prodShift
  rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
  congr 1
  refine congrArg List.ofFn (funext fun t => ?_)
  simp [Algebra.algebraMap_eq_smul_one]

def k2aQ (lam : Fin n → ℝ) (s : Fin n) : ℂ[X] := ∏ t ∈ univ.erase s, (X - C ((thV lam t : ℝ) : ℂ))

theorem aux_statement_18 (lam : Fin n → ℝ) (s : Fin n) (hanti : StrictAnti lam) :
    (k2aQ lam s).eval ((thV lam s : ℝ) : ℂ) ≠ 0 := by
  unfold k2aQ
  rw [eval_prod, Finset.prod_ne_zero_iff]
  intro t ht
  simp only [eval_sub, eval_X, eval_C]
  rw [sub_ne_zero, Ne, Complex.ofReal_inj]
  unfold thV
  intro h
  have : lam s = lam t := by linarith
  exact (Finset.ne_of_mem_erase ht) (hanti.injective this).symm

theorem shifted_aeval_lagrange_eq_zero (A : Module.End ℂ U₂) (lam : Fin n → ℝ) (s : Fin n) (h0 : prodShift A (thV lam) = 0)
    (y : U₂) : (A - ((thV lam s : ℝ) : ℂ) • (1 : Module.End ℂ U₂)) (aeval A (k2aQ lam s) y) = 0 := by
  have e : (A - ((thV lam s : ℝ) : ℂ) • (1 : Module.End ℂ U₂)) * aeval A (k2aQ lam s) = prodShift A (thV lam) := by
    rw [prodShift_eq_aeval, ← Finset.mul_prod_erase univ (fun t => X - C ((thV lam t : ℝ) : ℂ)) (mem_univ s),
      map_mul]
    simp [k2aQ, Algebra.algebraMap_eq_smul_one]
  rw [← Module.End.mul_apply, e, h0, LinearMap.zero_apply]

end Poly

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
