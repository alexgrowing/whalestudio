import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetIntegralNormRmulLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousIntegralInvMulOfLocallyIntegrable
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

noncomputable section

namespace GlobalTheory.CapTrace

variable {A : Type} [Ring A] [Algebra ℂ A]

def dprod (L : List (ℂ × A)) : ℂ := (L.map Prod.fst).prod

def sub1 (L : List (ℂ × A)) : A := List.rec 0 (fun p L s => dprod L • p.2 + p.1 • s) L

theorem sub1_nil : sub1 ([] : List (ℂ × A)) = 0 := rfl

theorem sub1_cons (p : ℂ × A) (L : List (ℂ × A)) : sub1 (p :: L) = dprod L • p.2 + p.1 • sub1 L := rfl

theorem prod_affine (L : List (ℂ × A)) : ∃ c : ℕ → A, (∀ k, L.length < k → c k = 0) ∧
    (∀ u : ℂ, (L.map fun p => (u * p.1) • (1 : A) + p.2).prod =
      ∑ k ∈ Finset.range (L.length + 1), u ^ k • c k) ∧
    c L.length = dprod L • (1 : A) ∧ (∀ j, j + 1 = L.length → c j = sub1 L) := by
  induction L with
  | nil => exact ⟨fun k => if k = 0 then 1 else 0, fun k hk => by simp at hk; simp [Nat.pos_iff_ne_zero.1 hk],
      fun u => by simp, by simp [dprod], fun j hj => by simp at hj⟩
  | cons p L ih =>
    obtain ⟨c, hc0, hcu, hctop, hcsub⟩ := ih
    refine ⟨fun k => (if k = 0 then 0 else p.1 • c (k - 1)) + p.2 * c k, ?_, ?_, ?_, ?_⟩
    · intro k hk
      simp only [List.length_cons] at hk
      have h1 : k ≠ 0 := by omega
      simp only [h1, if_false, hc0 k (by omega), hc0 (k - 1) (by omega), smul_zero, mul_zero, add_zero]
    · intro u
      have hS1 : ∑ k ∈ Finset.range (L.length + 1 + 1), u ^ k • (if k = 0 then (0:A) else p.1 • c (k - 1)) =
          ∑ k ∈ Finset.range (L.length + 1), (u * p.1) • (u ^ k • c k) := by
        rw [Finset.sum_range_succ']
        simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, if_true, smul_zero, add_zero]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [smul_smul, smul_smul, pow_succ]; ring_nf
      have hS2 : ∑ k ∈ Finset.range (L.length + 1 + 1), u ^ k • (p.2 * c k) =
          ∑ k ∈ Finset.range (L.length + 1), p.2 * (u ^ k • c k) := by
        rw [Finset.sum_range_succ, hc0 (L.length + 1) (by omega)]
        simp [mul_smul_comm]
      simp only [List.map_cons, List.prod_cons, hcu, List.length_cons, smul_add, Finset.sum_add_distrib, hS1, hS2,
        add_mul, Finset.mul_sum, smul_mul_assoc, one_mul]
    · simp only [List.length_cons, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, hctop,
        hc0 (L.length + 1) (by omega), mul_zero, add_zero, dprod, List.map_cons, List.prod_cons, smul_smul]
    · intro j hj
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hj
      subst hj
      beta_reduce
      rw [hctop, sub1_cons]
      rcases Nat.eq_zero_or_pos L.length with h | h
      · rw [if_pos h]
        have : L = [] := List.length_eq_zero_iff.1 h
        subst this
        simp [sub1_nil, dprod]
      · rw [if_neg (by omega), hcsub _ (by omega), mul_smul_comm, mul_one, add_comm]

end GlobalTheory.CapTrace

namespace GlobalTheory.CapTrace

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem coeff_mem (S : Submodule ℂ A) (n : ℕ) (c : ℕ → A)
    (h : ∀ u : ℂ, ∑ k ∈ Finset.range (n + 1), u ^ k • c k ∈ S) (m : ℕ) (hm : m ≤ n) : c m ∈ S := by
  let v : Fin (n + 1) → ℂ := fun j => ((j : ℕ) : ℂ)
  have hv : Function.Injective v := fun i j hij => Fin.ext (by simpa [v] using hij)
  have hdet : IsUnit (Matrix.vandermonde v).det :=
    isUnit_iff_ne_zero.2 (Matrix.det_vandermonde_ne_zero_iff.2 hv)
  have hW : (Matrix.vandermonde v)⁻¹ * Matrix.vandermonde v = 1 := Matrix.nonsing_inv_mul _ hdet
  set W := (Matrix.vandermonde v)⁻¹
  let m' : Fin (n + 1) := ⟨m, by omega⟩
  have key : c m = ∑ j, W m' j • ∑ k ∈ Finset.range (n + 1), v j ^ k • c k := by
    calc c m = ∑ k : Fin (n + 1), (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) m' k • c k := by
          rw [Finset.sum_eq_single m']
          · simp [m']
          · intro k _ hk; rw [Matrix.one_apply_ne (Ne.symm hk), zero_smul]
          · simp
      _ = ∑ k : Fin (n + 1), (W * Matrix.vandermonde v) m' k • c k := by rw [hW]
      _ = ∑ j, W m' j • ∑ k : Fin (n + 1), v j ^ (k : ℕ) • c k := by
          simp only [Matrix.mul_apply, Matrix.vandermonde_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
          exact Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_range (fun k => v j ^ k • c k)]
  rw [key]
  exact S.sum_mem fun j _ => S.smul_mem _ (h _)

theorem sub1_ones (L : List (ℂ × A)) (h : ∀ p ∈ L, p.1 = 1) : sub1 L = (L.map Prod.snd).sum ∧ dprod L = 1 := by
  induction L with
  | nil => simp [sub1_nil, dprod]
  | cons p L ih =>
    obtain ⟨h1, h2⟩ := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
    have hp := h p List.mem_cons_self
    refine ⟨?_, ?_⟩
    · rw [sub1_cons, h1, h2, hp]; simp
    · simp only [dprod, List.map_cons, List.prod_cons, hp, one_mul]; exact h2

theorem dprod_eq_zero (L : List (ℂ × A)) (p : ℂ × A) (hp : p ∈ L) (h : p.1 = 0) : dprod L = 0 :=
  List.prod_eq_zero (List.mem_map.2 ⟨p, hp, h⟩)

theorem sub1_ofFn_eq_zero : ∀ (n : ℕ) (d : Fin n → ℂ) (B : Fin n → A) (k₀ k₁ : Fin n), k₀ ≠ k₁ → d k₀ = 0 →
    d k₁ = 0 → sub1 (List.ofFn fun k => (d k, B k)) = 0 := by
  intro n
  induction n with
  | zero => intro d B k₀; exact k₀.elim0
  | succ n ih =>
    intro d B k₀ k₁ hne h₀ h₁
    rw [List.ofFn_succ, sub1_cons]
    have hmem : ∀ j : Fin n, d j.succ = 0 → dprod (List.ofFn fun k : Fin n => (d k.succ, B k.succ)) = 0 :=
      fun j hj => dprod_eq_zero _ (d j.succ, B j.succ) (List.mem_ofFn.2 ⟨j, rfl⟩) hj
    induction k₀ using Fin.cases with
    | zero =>
      induction k₁ using Fin.cases with
      | zero => exact absurd rfl hne
      | succ j₁ => simp [h₀, hmem j₁ h₁]
    | succ j₀ =>
      induction k₁ using Fin.cases with
      | zero => simp [h₁, hmem j₀ h₀]
      | succ j₁ =>
        rw [ih (fun k => d k.succ) (fun k => B k.succ) j₀ j₁ (fun e => hne (by rw [e])) h₀ h₁, hmem j₀ h₀]
        simp

end GlobalTheory.CapTrace

namespace GlobalTheory.CapTrace

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem trace_mem_of_qdet_mem {n : ℕ} (X : Fin n → Fin n → A) (S : Subalgebra ℂ A)
    (h : ∀ u : ℂ, Formalism.REAL.qdet X u ∈ S) : ∑ i, X i i ∈ S := by
  classical
  let d : Equiv.Perm (Fin n) → Fin n → ℂ := fun σ k => if σ k = k then 1 else 0
  let B : Equiv.Perm (Fin n) → Fin n → A := fun σ k =>
    (if σ k = k then algebraMap ℂ A (-((k : ℕ) : ℂ)) else 0) + X (σ k) k
  let L : Equiv.Perm (Fin n) → List (ℂ × A) := fun σ => List.ofFn fun k => (d σ k, B σ k)
  have hlen : ∀ σ, (L σ).length = n := fun σ => List.length_ofFn
  choose c hc0 hcu hctop hcsub using fun σ => prod_affine (L σ)
  have hfac : ∀ σ (u : ℂ), (List.ofFn fun k : Fin n => Formalism.REAL.Tm X (u - ((k : ℕ) : ℂ)) (id (σ k)) (id k)).prod =
      ((L σ).map fun p => (u * p.1) • (1 : A) + p.2).prod := by
    intro σ u
    simp only [L, List.map_ofFn]
    congr 1
    refine List.ofFn_inj.2 (funext fun k => ?_)
    simp only [Function.comp_apply, Formalism.REAL.Tm, id, d, B]
    split_ifs
    · rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, mul_one, sub_eq_add_neg, add_smul]; abel
    · simp
  let C : ℕ → A := fun k => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : A) * c σ k
  have hC : ∀ u : ℂ, Formalism.REAL.qdet X u = ∑ k ∈ Finset.range (n + 1), u ^ k • C k := by
    intro u
    simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, hfac, hcu, hlen, C, Finset.mul_sum, Finset.smul_sum, mul_smul_comm]
    exact Finset.sum_comm
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  have hmem : C (n - 1) ∈ S := coeff_mem (Subalgebra.toSubmodule S) n C (fun u => by
    rw [← hC]; exact h u) (n - 1) (by omega)
  have hsub : ∀ σ, c σ (n - 1) = sub1 (L σ) := fun σ => hcsub σ _ (by rw [hlen]; omega)
  have hCeq : C (n - 1) = ∑ k : Fin n, B 1 k := by
    simp only [C, hsub]
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
    · rw [(sub1_ones (L 1) ?_).1]
      · simp [L, List.map_ofFn, List.sum_ofFn]
      · intro p hp
        obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hp
        simp [d]
    · intro σ _ hσ
      obtain ⟨k₀, hk₀⟩ : ∃ k, σ k ≠ k := by
        by_contra hc; exact hσ (Equiv.ext fun k => not_not.1 fun hk => hc ⟨k, hk⟩)
      have hk₁ : σ (σ k₀) ≠ σ k₀ := fun e => hk₀ (σ.injective e)
      rw [sub1_ofFn_eq_zero n (d σ) (B σ) k₀ (σ k₀) (Ne.symm hk₀) (by simp [d, hk₀]) (by simp [d, hk₁]), mul_zero]
    · simp
  have hB : ∀ k : Fin n, B 1 k = algebraMap ℂ A (-((k : ℕ) : ℂ)) + X k k := fun k => by simp [B]
  simp only [hCeq, hB, Finset.sum_add_distrib] at hmem
  have hs : ∑ k : Fin n, algebraMap ℂ A (-((k : ℕ) : ℂ)) ∈ S := S.sum_mem fun k _ => S.algebraMap_mem _
  simpa using S.sub_mem hmem hs

end GlobalTheory.CapTrace

namespace GlobalTheory.CuspRep

theorem Eop_add_Eop_conj {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (τ : E →+* ℂ)
    (i : Fin a) : Eop τ i i + Eop (ComplexEmbedding.conjugate τ) i i = lieS E a i i (atEmb τ 1) := by
  have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by
    rw [atEmb_eq]; simp
  simp only [Eop, atEmb_conj, map_one, Complex.conj_I, e, map_neg, smul_neg, sub_neg_eq_add]
  rw [← smul_add]
  module

end GlobalTheory.CuspRep
