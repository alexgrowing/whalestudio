import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroCommonZeroOfIsHomogeneousStatement

open IsLocalRing

namespace GlobalTheory
namespace TsenCount

open Polynomial

variable {σ k : Type} [CommRing k]

def CoeffHom (e : ℕ) (p : (MvPolynomial σ k)[X]) : Prop := ∀ j, (p.coeff j).IsHomogeneous e

theorem CoeffHom.mul {a b : ℕ} {p q : (MvPolynomial σ k)[X]} (hp : CoeffHom a p)
    (hq : CoeffHom b q) : CoeffHom (a + b) (p * q) := fun j => by
  rw [coeff_mul]
  exact MvPolynomial.IsHomogeneous.sum _ _ _ fun c _ => (hp _).mul (hq _)

theorem coeffHom_map (g : k[X]) :
    CoeffHom 0 (g.map (MvPolynomial.C : k →+* MvPolynomial σ k)) := fun j => by
  rw [coeff_map]
  exact MvPolynomial.isHomogeneous_C _ _

theorem coeffHom_one : CoeffHom 0 (1 : (MvPolynomial σ k)[X]) := by
  simpa using coeffHom_map (σ := σ) (1 : k[X])

theorem CoeffHom.pow {p : (MvPolynomial σ k)[X]} (hp : CoeffHom 1 p) (m : ℕ) :
    CoeffHom m (p ^ m) := by
  induction m with
  | zero => simpa using coeffHom_one
  | succ m ih => rw [pow_succ]; exact ih.mul hp

theorem CoeffHom.prod {ι : Type} (s : Finset ι) (e : ι → ℕ) (p : ι → (MvPolynomial σ k)[X])
    (h : ∀ i, CoeffHom (e i) (p i)) : CoeffHom (∑ i ∈ s, e i) (∏ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using coeffHom_one
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha]; exact (h a).mul ih

theorem CoeffHom.sum {ι : Type} (s : Finset ι) (e : ℕ) (p : ι → (MvPolynomial σ k)[X])
    (h : ∀ i ∈ s, CoeffHom e (p i)) : CoeffHom e (∑ i ∈ s, p i) := fun j => by
  rw [finsetSum_coeff]
  exact MvPolynomial.IsHomogeneous.sum _ _ _ fun i hi => h i hi j

theorem sum_eq_of_mem_support {n d : ℕ} {R : Type} [CommRing R] {f : MvPolynomial (Fin n) R}
    (hf : f.IsHomogeneous d) {s : Fin n →₀ ℕ} (hs : s ∈ f.support) : ∑ i, s i = d := by
  have h := hf (MvPolynomial.mem_support_iff.1 hs)
  rw [← h, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp

theorem coeffHom_eval₂ {n d : ℕ} {f : MvPolynomial (Fin n) k[X]} (hf : f.IsHomogeneous d)
    (y : Fin n → (MvPolynomial σ k)[X]) (hy : ∀ i, CoeffHom 1 (y i)) :
    CoeffHom d (MvPolynomial.eval₂ (mapRingHom (MvPolynomial.C : k →+* MvPolynomial σ k)) y f) := by
  rw [MvPolynomial.eval₂_eq']
  refine CoeffHom.sum _ _ _ fun s hs => ?_
  have h := (coeffHom_map (σ := σ) (MvPolynomial.coeff s f)).mul
    (CoeffHom.prod Finset.univ (fun i => s i) (fun i => y i ^ s i) fun i => (hy i).pow _)
  rwa [zero_add, sum_eq_of_mem_support hf hs] at h

theorem natDegree_eval_le {n d N D : ℕ} {f : MvPolynomial (Fin n) k[X]} (hf : f.IsHomogeneous d)
    (hD : ∀ s ∈ f.support, (MvPolynomial.coeff s f).natDegree ≤ D)
    (x : Fin n → k[X]) (hx : ∀ i, (x i).natDegree ≤ N) :
    (MvPolynomial.eval x f).natDegree ≤ D + d * N := by
  rw [MvPolynomial.eval_eq']
  refine natDegree_sum_le_of_forall_le _ _ fun s hs => natDegree_mul_le.trans ?_
  refine add_le_add (hD s hs) ((natDegree_prod_le _ _).trans ?_)
  rw [← sum_eq_of_mem_support hf hs, Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => natDegree_pow_le.trans (Nat.mul_le_mul_left _ (hx i))

end TsenCount

open Polynomial TsenCount in

theorem exists_nonzero_zero_polynomial_of_isAlgClosed (k : Type) [Field k] [IsAlgClosed k] (n d : ℕ)
    (f : MvPolynomial (Fin n) (Polynomial k)) (hf : f.IsHomogeneous d) (hd : 0 < d) (hn : d < n) :
    ∃ x : Fin n → Polynomial k, x ≠ 0 ∧ MvPolynomial.eval x f = 0 := by
  classical
  obtain ⟨D, hD⟩ : ∃ D, ∀ s ∈ f.support, (MvPolynomial.coeff s f).natDegree ≤ D :=
    ⟨f.support.sup fun s => (MvPolynomial.coeff s f).natDegree, fun s hs =>
      Finset.le_sup (f := fun s => (MvPolynomial.coeff s f).natDegree) hs⟩
  let y : Fin n → (MvPolynomial (Fin (n * (D + 1))) k)[X] := fun i =>
    ∑ m : Fin (D + 1), monomial (m : ℕ) (MvPolynomial.X (finProdFinEquiv (i, m)))
  have hy : ∀ i, CoeffHom 1 (y i) := fun i => CoeffHom.sum _ _ _ fun m _ j => by
    rw [coeff_monomial]
    split_ifs
    · exact MvPolynomial.isHomogeneous_X _ _
    · exact MvPolynomial.isHomogeneous_zero _ _ _
  have hP := coeffHom_eval₂ hf y hy
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.T.exists_ne_zero_common_zero_of_isHomogeneous' k (n * (D + 1)) (D + d * D + 1)
    (fun j => (MvPolynomial.eval₂ (mapRingHom MvPolynomial.C) y f).coeff j)
    (fun j => ⟨d, hd, hP j⟩) (by nlinarith)
  let x : Fin n → k[X] := fun i => (y i).map (MvPolynomial.eval c)
  have hx : ∀ i, x i = ∑ m : Fin (D + 1), monomial (m : ℕ) (c (finProdFinEquiv (i, m))) := fun i => by
    simp [x, y, Polynomial.map_sum]
  have hdeg : ∀ i, (x i).natDegree ≤ D := fun i => by
    rw [hx]
    exact natDegree_sum_le_of_forall_le _ _ fun m _ =>
      (natDegree_monomial_le _).trans (Nat.lt_succ_iff.1 m.2)
  have hev : MvPolynomial.eval x f =
      (MvPolynomial.eval₂ (mapRingHom MvPolynomial.C) y f).map (MvPolynomial.eval c) := by
    rw [← coe_mapRingHom, MvPolynomial.eval₂_comp_left, mapRingHom_comp]
    have : (MvPolynomial.eval c).comp (MvPolynomial.C : k →+* MvPolynomial (Fin (n * (D + 1))) k)
        = RingHom.id k := by ext; simp
    rw [this, mapRingHom_id]
    rfl
  refine ⟨x, fun h0 => hc0 ?_, ?_⟩
  · funext a
    obtain ⟨⟨i, m⟩, rfl⟩ := finProdFinEquiv.surjective a
    have h1 : (x i).coeff m = 0 := by rw [h0]; simp
    rw [hx, finsetSum_coeff, Finset.sum_eq_single m] at h1
    · simpa using h1
    · intro b _ hb
      rw [coeff_monomial, if_neg fun h => hb (Fin.ext h)]
    · simp
  · ext j
    rw [coeff_zero]
    by_cases hj : j < D + d * D + 1
    · rw [hev, coeff_map]
      exact hc ⟨j, hj⟩
    · exact coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (natDegree_eval_le hf hD x hdeg) (by omega))

end GlobalTheory
