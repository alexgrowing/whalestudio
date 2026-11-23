import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur

open GlobalTheory.LeviCut

noncomputable section

namespace GlobalTheory.LeviCut.GridScalarProof

variable {V : Type} [AddCommGroup V] [Module ℚ V]

def vanSub (N : ℕ) (e : ℕ → ℕ → Module.End ℚ V) (lam : ℕ → ℤ) (s : Finset ℕ) :
    Submodule ℚ (Module.End ℚ V) where
  carrier := {U | ∀ (μ : ℕ → ℤ) (x : V), IsWt N e μ x → ∑ c ∈ s, μ c < ∑ c ∈ s, lam c → U x = 0}
  add_mem' := by
    intro U W hU hW μ x hx hlt
    simp [hU μ x hx hlt, hW μ x hx hlt]
  zero_mem' := by
    intro μ x _ _
    simp
  smul_mem' := by
    intro r U hU μ x hx hlt
    simp [hU μ x hx hlt]

theorem mem_vanSub {N : ℕ} {e : ℕ → ℕ → Module.End ℚ V} {lam : ℕ → ℤ} {s : Finset ℕ} {U : Module.End ℚ V} :
    U ∈ vanSub N e lam s ↔ ∀ (μ : ℕ → ℤ) (x : V), IsWt N e μ x → ∑ c ∈ s, μ c < ∑ c ∈ s, lam c → U x = 0 :=
  Iff.rfl

theorem isWt_shift {N : ℕ} {e : ℕ → ℕ → Module.End ℚ V} (he : GlRel N e) {c d : ℕ} (hc : c < N) (hd : d < N)
    {μ : ℕ → ℤ} {x : V} (hx : IsWt N e μ x) :
    IsWt N e (fun k => μ k + ((if k = c then 1 else 0) - (if k = d then 1 else 0))) (e c d x) := by
  intro k hk
  have h := congrArg (fun f : Module.End ℚ V => f x) (he k k c d hk hk hc hd)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h, hx k hk, map_smul]
  by_cases hkc : k = c <;> by_cases hkd : k = d
  · subst hkc; subst hkd; simp
  · subst hkc; simp [hkd, Ne.symm hkd]; module
  · subst hkd; simp [hkc]; module
  · simp [hkc, hkd, Ne.symm hkd]

theorem sum_shift (s : Finset ℕ) (μ : ℕ → ℤ) (c d : ℕ) :
    ∑ k ∈ s, (μ k + ((if k = c then 1 else 0) - (if k = d then 1 else 0))) =
      ∑ k ∈ s, μ k + ((if c ∈ s then 1 else 0) - (if d ∈ s then 1 else 0)) := by
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']

theorem adj_mem_vanSub {N : ℕ} {e : ℕ → ℕ → Module.End ℚ V} {lam : ℕ → ℤ} {s : Finset ℕ} (he : GlRel N e)
    {c d : ℕ} (hc : c < N) (hd : d < N) (hs : c ∈ s ↔ d ∈ s) {U : Module.End ℚ V}
    (hU : U ∈ vanSub N e lam s) : adj (e c d) U ∈ vanSub N e lam s := by
  rw [mem_vanSub] at hU ⊢
  intro μ x hx hlt
  have h2 : ∑ k ∈ s, (μ k + ((if k = c then 1 else 0) - (if k = d then 1 else 0))) < ∑ k ∈ s, lam k := by
    rw [sum_shift]
    by_cases h : c ∈ s
    · simp [h, hs.mp h, hlt]
    · simp [h, mt hs.mpr h, hlt]
  simp only [adj, LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, Module.End.mul_apply]
  rw [hU μ x hx hlt, map_zero, hU _ _ (isWt_shift he hc hd hx) h2, sub_zero]

theorem pow_mem_of {M : Type} [AddCommGroup M] [Module ℚ M] {S : Submodule ℚ M} {P : Module.End ℚ M}
    (hP : ∀ U ∈ S, P U ∈ S) (k : ℕ) : ∀ U ∈ S, (P ^ k) U ∈ S := by
  induction k with
  | zero => intro U hU; simpa using hU
  | succ k ih => intro U hU; rw [pow_succ, Module.End.mul_apply]; exact ih _ (hP U hU)

theorem proj_mem {M : Type} [AddCommGroup M] [Module ℚ M] {S : Submodule ℚ M} {P Q : Module.End ℚ M}
    (hP : ∀ U ∈ S, P U ∈ S) (hQ : ∀ U ∈ S, Q U ∈ S) (K j : ℕ) : ∀ U ∈ S, proj K j P Q U ∈ S := by
  intro U hU
  simp only [proj, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (pow_mem_of hQ k _ (pow_mem_of hP k U hU))

theorem listProd_mem {M : Type} [AddCommGroup M] [Module ℚ M] {S : Submodule ℚ M} (L : List (Module.End ℚ M))
    (hL : ∀ f ∈ L, ∀ U ∈ S, f U ∈ S) : ∀ U ∈ S, L.prod U ∈ S := by
  induction L with
  | nil => intro U hU; simpa using hU
  | cons f L ih =>
    intro U hU
    rw [List.prod_cons, Module.End.mul_apply]
    exact hL f (by simp) _ (ih (fun g hg => hL g (by simp [hg])) U hU)

theorem rootP_mem {N : ℕ} {e : ℕ → ℕ → Module.End ℚ V} {lam : ℕ → ℤ} {s : Finset ℕ} (he : GlRel N e)
    {i j : ℕ} (hi : i < N) (hj : j < N) (hs : i ∈ s ↔ j ∈ s) (K : ℕ) :
    ∀ U ∈ vanSub N e lam s, rootP (fun c d => adj (e c d)) K i j U ∈ vanSub N e lam s :=
  proj_mem (fun U hU => adj_mem_vanSub he hi hj hs hU) (fun U hU => adj_mem_vanSub he hj hi hs.symm hU) _ _

theorem rowP_mem {N : ℕ} {e : ℕ → ℕ → Module.End ℚ V} {lam : ℕ → ℤ} {t : Finset ℕ} (he : GlRel N e)
    {i s n : ℕ} (hi : i < N) (hsn : s + n ≤ N) (hS : ∀ j, s ≤ j → j < s + n → (i ∈ t ↔ j ∈ t)) (K : ℕ) :
    ∀ U ∈ vanSub N e lam t, rowP (fun c d => adj (e c d)) K i s n U ∈ vanSub N e lam t := by
  unfold rowP
  apply listProd_mem
  intro f hf
  rw [List.mem_map] at hf
  obtain ⟨j, hj, rfl⟩ := hf
  rw [List.mem_range'_1] at hj
  exact rootP_mem he hi (by omega) (hS j hj.1 hj.2) K

theorem isWt_pow {N : ℕ} {e : ℕ → ℕ → Module.End ℚ V} (he : GlRel N e) {c d : ℕ} (hc : c < N) (hd : d < N)
    {μ : ℕ → ℤ} {x : V} (hx : IsWt N e μ x) (k : ℕ) :
    IsWt N e (fun m => μ m + (k : ℤ) * ((if m = c then 1 else 0) - (if m = d then 1 else 0))) ((e c d ^ k) x) := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    have h := isWt_shift he hc hd ih
    have hf : (fun m => μ m + ((k + 1 : ℕ) : ℤ) * ((if m = c then 1 else 0) - (if m = d then 1 else 0))) =
        (fun m => (μ m + (k : ℤ) * ((if m = c then 1 else 0) - (if m = d then 1 else 0))) +
          ((if m = c then 1 else 0) - (if m = d then 1 else 0))) := by
      funext m; push_cast; ring
    rw [hf]; exact h

theorem kill_pow {N : ℕ} {e : ℕ → ℕ → Module.End ℚ V} {lam : ℕ → ℤ} {s : Finset ℕ} (he : GlRel N e)
    {i j : ℕ} (hi : i < N) (hj : j < N) (his : i ∈ s) (hjs : j ∉ s) {v : V} (hv : IsWt N e lam v)
    {U : Module.End ℚ V} (hU : U ∈ vanSub N e lam s) (k : ℕ) (hk : 0 < k) : U ((e j i ^ k) v) = 0 := by
  refine hU _ _ (isWt_pow he hj hi hv k) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [his, hjs, if_true, if_false]
  have : (0 : ℤ) < k := by exact_mod_cast hk
  linarith

theorem step (hS : StepScalar) {N K : ℕ} {e : ℕ → ℕ → Module.End ℚ V} {lam : ℕ → ℤ} {v : V} {φ : V →ₗ[ℚ] ℚ}
    (he : GlRel N e) {i j : ℕ} (hij : i < j) (hj : j < N) (hv : IsWt N e lam v) (hE : e i j v = 0)
    (hφ : ∀ x, φ (e j i x) = 0) (hl1 : lam j ≤ lam i) (hl2 : lam i ≤ lam j + K) {U : Module.End ℚ V}
    (hU : ∀ k : ℕ, 0 < k → U ((e j i ^ k) v) = 0) :
    φ (rootP (fun c d => adj (e c d)) K i j U v) * (((lam i - lam j + (j : ℤ) - (i : ℤ) : ℤ)) : ℚ) = φ (U v) := by
  have hi : i < N := by omega
  have h1 : e i j * e j i - e j i * e i j = e i i - e j j := by
    have := he i j j i hi hj hj hi
    rw [if_pos rfl, if_pos rfl] at this
    exact this
  have h2 : (e i i - e j j) * e j i - e j i * (e i i - e j j) = -(e j i + e j i) := by
    have a1 := he i i j i hi hi hj hi
    have a2 := he j j j i hj hj hj hi
    rw [if_neg hij.ne, if_pos rfl] at a1
    rw [if_pos rfl, if_neg hij.ne] at a2
    calc (e i i - e j j) * e j i - e j i * (e i i - e j j)
        = (e i i * e j i - e j i * e i i) - (e j j * e j i - e j i * e j j) := by noncomm_ring
      _ = -(e j i + e j i) := by rw [a1, a2]; abel
  have hn : (((lam i - lam j).toNat : ℕ) : ℤ) = lam i - lam j := Int.toNat_of_nonneg (by omega)
  have hnq : (((lam i - lam j).toNat : ℕ) : ℚ) = ((lam i : ℚ) - (lam j : ℚ)) := by
    have : (((lam i - lam j).toNat : ℕ) : ℚ) = ((((lam i - lam j).toNat : ℕ) : ℤ) : ℚ) := by norm_cast
    rw [this, hn]; push_cast; ring
  have hH : (e i i - e j j) v = (((lam i - lam j).toNat : ℕ) : ℚ) • v := by
    rw [LinearMap.sub_apply, hv i hi, hv j hj, ← sub_smul, hnq]
  have hK : (lam i - lam j).toNat ≤ K := by omega
  have key := hS V (e i j) (e j i) (e i i - e j j) U v φ (lam i - lam j).toNat K (j - i - 1) h1 h2 hE hH hK hφ hU
  have hc : (((lam i - lam j).toNat : ℕ) : ℚ) + ((j - i - 1 : ℕ) : ℚ) + 1 =
      (((lam i - lam j + (j : ℤ) - (i : ℤ) : ℤ)) : ℚ) := by
    have : ((((lam i - lam j).toNat : ℕ) : ℤ) + ((j - i - 1 : ℕ) : ℤ) + 1 : ℤ) = lam i - lam j + (j : ℤ) - (i : ℤ) := by
      omega
    exact_mod_cast this
  rw [← hc]
  exact key

theorem van_Ico_of_range {a b : ℕ} {e : ℕ → ℕ → Module.End ℚ V} {lam : ℕ → ℤ} (hD : Dom (a + b) e lam)
    {T : Module.End ℚ V} (hT : T ∈ vanSub (a + b) e lam (Finset.range a)) {i : ℕ} (hi : i ≤ a) :
    T ∈ vanSub (a + b) e lam (Finset.Ico i a) := by
  intro μ x hx hlt
  by_cases hx0 : x = 0
  · simp [hx0]
  obtain ⟨h1, -⟩ := hD μ x hx hx0
  have hi' := h1 i (by omega)
  apply hT μ x hx
  rw [← Finset.sum_range_add_sum_Ico _ hi, ← Finset.sum_range_add_sum_Ico _ hi]
  linarith

theorem van_union {a b : ℕ} {e : ℕ → ℕ → Module.End ℚ V} {lam : ℕ → ℤ} (hD : Dom (a + b) e lam)
    {i s : ℕ} (hs1 : a ≤ s) (hs2 : s ≤ a + b) {U : Module.End ℚ V} (hU : U ∈ vanSub (a + b) e lam (Finset.Ico i a)) :
    U ∈ vanSub (a + b) e lam (Finset.Ico i a ∪ Finset.Ico s (a + b)) := by
  intro μ x hx hlt
  by_cases hx0 : x = 0
  · simp [hx0]
  obtain ⟨h1, h2⟩ := hD μ x hx hx0
  have hs := h1 s hs2
  have hdisj : Disjoint (Finset.Ico i a) (Finset.Ico s (a + b)) := by
    rw [Finset.disjoint_left]; intro y hy1 hy2; simp only [Finset.mem_Ico] at hy1 hy2; omega
  rw [Finset.sum_union hdisj, Finset.sum_union hdisj] at hlt
  rw [← Finset.sum_range_add_sum_Ico _ hs2, ← Finset.sum_range_add_sum_Ico _ hs2] at h2
  apply hU μ x hx
  linarith

theorem row_scalar (hS : StepScalar) {a b K : ℕ} {e : ℕ → ℕ → Module.End ℚ V} {lam : ℕ → ℤ} {v : V}
    {φ : V →ₗ[ℚ] ℚ} (he : GlRel (a + b) e) (hD : Dom (a + b) e lam) (hv : IsWt (a + b) e lam v)
    (hij : ∀ i j : ℕ, i < j → j < a + b → e i j v = 0 ∧ (∀ x, φ (e j i x) = 0) ∧ lam j ≤ lam i ∧ lam i ≤ lam j + K)
    {i : ℕ} (hia : i < a) {U : Module.End ℚ V} (hU : U ∈ vanSub (a + b) e lam (Finset.Ico i a)) :
    ∀ n s, s + n = a + b → a ≤ s →
      φ (rowP (fun c d => adj (e c d)) K i s n U v) *
        ∏ j ∈ Finset.Ico s (a + b), (((lam i - lam j + (j : ℤ) - (i : ℤ) : ℤ)) : ℚ) = φ (U v) := by
  intro n
  induction n with
  | zero =>
    intro s hs _
    have : s = a + b := by omega
    subst this
    simp [rowP]
  | succ n ih =>
    intro s hs has
    have hsN : s < a + b := by omega
    have hWmem : rowP (fun c d => adj (e c d)) K i (s + 1) n U ∈
        vanSub (a + b) e lam (Finset.Ico i a ∪ Finset.Ico (s + 1) (a + b)) := by
      refine rowP_mem he (by omega) (by omega) ?_ K U (van_union hD (by omega) (by omega) hU)
      intro j h1 h2
      simp only [Finset.mem_union, Finset.mem_Ico]
      omega
    have hrow : rowP (fun c d => adj (e c d)) K i s (n + 1) U =
        rootP (fun c d => adj (e c d)) K i s (rowP (fun c d => adj (e c d)) K i (s + 1) n U) := by
      simp only [rowP, List.range'_succ, List.map_cons, List.prod_cons, Module.End.mul_apply]
    obtain ⟨hE, hφ, hl1, hl2⟩ := hij i s (by omega) hsN
    have hst := step hS he (by omega : i < s) hsN hv hE hφ hl1 hl2
      (kill_pow he (by omega) hsN (by simp only [Finset.mem_union, Finset.mem_Ico]; omega)
        (by simp only [Finset.mem_union, Finset.mem_Ico]; omega) hv hWmem)
    rw [hrow, Finset.prod_eq_prod_Ico_succ_bot hsN, ← mul_assoc, hst]
    exact ih (s + 1) (by omega) (by omega)

theorem gridP_succ {M : Type} [AddCommGroup M] [Module ℚ M] (D : ℕ → ℕ → Module.End ℚ M) (K a b t : ℕ) :
    gridP D K a b (t + 1) = rowP D K t a b * gridP D K a b t := by
  simp only [gridP, List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
    List.map_cons, List.prod_cons]

theorem grid_van {a b K : ℕ} {e : ℕ → ℕ → Module.End ℚ V} {lam : ℕ → ℤ} (he : GlRel (a + b) e)
    (hD : Dom (a + b) e lam) {T : Module.End ℚ V} (hT : T ∈ vanSub (a + b) e lam (Finset.range a)) :
    ∀ t i, t ≤ i → i ≤ a → gridP (fun c d => adj (e c d)) K a b t T ∈ vanSub (a + b) e lam (Finset.Ico i a) := by
  intro t
  induction t with
  | zero => intro i _ hi; simpa [gridP] using van_Ico_of_range hD hT hi
  | succ t ih =>
    intro i hti hi
    rw [gridP_succ, Module.End.mul_apply]
    refine rowP_mem he (by omega) (by omega) ?_ K _ (ih i (by omega) hi)
    intro j h1 h2
    simp only [Finset.mem_Ico]
    omega

theorem grid_scalar (hS : StepScalar) {a b K : ℕ} {e : ℕ → ℕ → Module.End ℚ V} {lam : ℕ → ℤ} {v : V}
    {φ : V →ₗ[ℚ] ℚ} (he : GlRel (a + b) e) (hD : Dom (a + b) e lam) (hv : IsWt (a + b) e lam v)
    (hij : ∀ i j : ℕ, i < j → j < a + b → e i j v = 0 ∧ (∀ x, φ (e j i x) = 0) ∧ lam j ≤ lam i ∧ lam i ≤ lam j + K)
    {T : Module.End ℚ V} (hT : T ∈ vanSub (a + b) e lam (Finset.range a)) :
    ∀ t, t ≤ a → φ (gridP (fun c d => adj (e c d)) K a b t T v) *
      ∏ i ∈ Finset.range t, ∏ j ∈ Finset.Ico a (a + b), (((lam i - lam j + (j : ℤ) - (i : ℤ) : ℤ)) : ℚ) = φ (T v) := by
  intro t
  induction t with
  | zero => intro _; simp [gridP]
  | succ t ih =>
    intro ht
    rw [gridP_succ, Module.End.mul_apply, Finset.prod_range_succ, mul_comm (Finset.prod _ _) _, ← mul_assoc,
      row_scalar hS he hD hv hij (by omega : t < a) (grid_van he hD hT t t le_rfl (by omega)) b a (by omega) le_rfl]
    exact ih (by omega)

end GlobalTheory.LeviCut.GridScalarProof

namespace GlobalTheory.LeviCut

open GridScalarProof in

theorem gridScalar_of_stepScalar : StepScalar → GridScalar := by
  intro hS V _ _ a b K e lam v φ T he hD hv hij hT
  have hT' : T ∈ vanSub (a + b) e lam (Finset.range a) := hT
  have key := grid_scalar hS he hD hv hij hT' a le_rfl
  rw [Int.cast_prod]
  simp_rw [Int.cast_prod]
  exact key

end GlobalTheory.LeviCut
