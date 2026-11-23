import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubWeilOfInjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair

theorem prod_pow_of_mul_eq_zero {A κ : Type} [CommRing A] [Fintype κ] [DecidableEq κ] (x : κ → A)
    (hx : ∀ i j, x i * x j = 0) (k : κ → ℕ) :
    ∏ i, x i ^ k i = ∏ i, (0 : A) ^ k i + ∑ i, if k = Pi.single i 1 then x i else 0 := by
  by_cases h0 : k = 0
  · subst h0
    rw [Finset.sum_eq_zero fun i _ => if_neg fun h => by simpa using congrFun h i]
    simp
  obtain ⟨i, hi⟩ := Function.ne_iff.1 h0
  have hi : k i ≠ 0 := hi
  rw [Finset.prod_eq_zero (f := fun i => (0 : A) ^ k i) (Finset.mem_univ i) (zero_pow hi), zero_add,
    Finset.sum_eq_single i (fun j _ hj => if_neg fun h => hi (by rw [h]; simp [hj.symm])) (by simp)]
  split_ifs with h
  · subst h
    rw [Finset.prod_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
    simp
  · by_cases h1 : k i = 1
    · obtain ⟨j, hj⟩ := Function.ne_iff.1 h
      have hji : j ≠ i := by rintro rfl; simp [h1] at hj
      have hj0 : k j ≠ 0 := by simpa [hji] using hj
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
        ← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨hji, Finset.mem_univ j⟩), h1, pow_one]
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hj0
      rw [hm, pow_succ', mul_assoc (x j), ← mul_assoc (x i), hx, zero_mul]
    · refine Finset.prod_eq_zero (Finset.mem_univ i) (pow_eq_zero_of_le (m := 2) (by omega) ?_)
      rw [pow_two, hx]

theorem evalPoints_first_order_of_sq_eq_zero {R : Type} [CommRing R] {d : ℕ} (ph : PS R 3 d) {A : Type} [CommRing A] [Algebra R A]
    (e : A) (he : e ^ 2 = 0) (u : Fin d → R) (b b' : Fin d → A) (hb : ∀ j, IsNilpotent (b j))
    (hb' : ∀ j, IsNilpotent (b' j)) :
    evP ![fun j => u j • e, b, b'] ph = evP ![0, b, b'] ph + e * evP ![b, b'] (c2 ph u) := by
  have hx : ∀ i j, (u i • e) * (u j • e) = 0 := fun i j => by
    rw [smul_mul_smul_comm, ← pow_two, he, smul_zero]
  obtain ⟨N₁, -, h₁⟩ := evBasic_exists_pow b hb
  obtain ⟨N₂, -, h₂⟩ := evBasic_exists_pow b' hb'
  obtain ⟨N, hN, h₁, h₂⟩ : ∃ N, 2 ≤ N ∧ (∀ j, b j ^ N = 0) ∧ ∀ j, b' j ^ N = 0 :=
    ⟨N₁ + N₂ + 2, by omega, fun j => pow_eq_zero_of_le (by omega) (h₁ j),
      fun j => pow_eq_zero_of_le (by omega) (h₂ j)⟩
  have h3 : ∀ x : Fin d → A, (∀ j, x j ^ N = 0) →
      ∀ q : Fin 3 × Fin d, (![x, b, b'] : Fin 3 → Fin d → A) q.1 q.2 ^ N = 0 := by
    rintro x hx ⟨i, j⟩
    fin_cases i
    exacts [hx j, h₁ j, h₂ j]
  have h2 : ∀ q : Fin 2 × Fin d, (![b, b'] : Fin 2 → Fin d → A) q.1 q.2 ^ N = 0 := by
    rintro ⟨i, j⟩
    fin_cases i
    exacts [h₁ j, h₂ j]
  have hp : ∀ (x : Fin d → A) (n : Fin 3 × Fin d → ℕ),
      ∏ q : Fin 3 × Fin d, (![x, b, b'] : Fin 3 → Fin d → A) q.1 q.2 ^ n q = (∏ j, x j ^ n (0, j)) *
        ∏ q : Fin 2 × Fin d, (![b, b'] : Fin 2 → Fin d → A) q.1 q.2 ^ n (q.1.succ, q.2) := by
    intro x n
    rw [Fintype.prod_prod_type, Fin.prod_univ_succ, Fintype.prod_prod_type]
    rfl
  unfold evP
  rw [evBasic_nEval_eq_tEval _ _ N (h3 _ fun j => pow_eq_zero_of_le hN (by rw [pow_two, hx])),
    evBasic_nEval_eq_tEval _ _ N (h3 0 fun j => zero_pow (by omega)),
    evBasic_nEval_eq_tEval _ _ N h2, evBasic_tEval_eq_sum, evBasic_tEval_eq_sum, evBasic_tEval_eq_sum]
  simp only [hp, prod_pow_of_mul_eq_zero _ hx, add_mul, mul_add, Finset.sum_add_distrib, Pi.zero_apply,
    add_right_inj]
  have hc : ∀ mu, MvPowerSeries.coeff mu (c2 ph u) = ∑ i, u i * MvPowerSeries.coeff
    (mu.mapDomain (fun q : Fin 2 × Fin d => (q.1.succ, q.2)) + Finsupp.single ((0 : Fin 3), i) 1) ph :=
    fun _ => rfl
  simp only [hc, map_sum, Finset.sum_mul, Finset.mul_sum, ite_mul, mul_ite, zero_mul, mul_zero]
  rw [Finset.sum_comm, Finset.sum_comm (t := Finset.univ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_filter]
  have hinj : Function.Injective (fun q : Fin 2 × Fin d => ((q.1.succ, q.2) : Fin 3 × Fin d)) :=
    fun q q' h => by
      simp only [Prod.mk.injEq, Fin.succ_inj] at h
      exact Prod.ext h.1 h.2
  refine Finset.sum_nbij' (fun n q => n (q.1.succ, q.2))
    (fun m q => (Fin.cons (Pi.single i 1) (fun a j => m (a, j)) : Fin 3 → Fin d → ℕ) q.1 q.2) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_filter, Fintype.mem_piFinset] at hn ⊢
    exact fun q => hn.1 _
  · intro m hm
    simp only [Finset.mem_filter, Fintype.mem_piFinset] at hm ⊢
    refine ⟨?_, rfl⟩
    rintro ⟨a, j⟩
    refine Fin.cases ?_ (fun a => hm (a, j)) a
    simp only [Fin.cons_zero, Finset.mem_range, Pi.single_apply]
    split_ifs <;> omega
  · intro n hn
    funext ⟨a, j⟩
    exact Fin.cases (congrFun (Finset.mem_filter.1 hn).2 j).symm (fun _ => rfl) a
  · intro m _
    rfl
  · intro n hn
    have hn0 : ∀ j, n (0, j) = (Pi.single i 1 : Fin d → ℕ) j := congrFun (Finset.mem_filter.1 hn).2
    have : (Finsupp.equivFunOnFinite.symm fun q : Fin 2 × Fin d => n (q.1.succ, q.2)).mapDomain
        (fun q : Fin 2 × Fin d => ((q.1.succ, q.2) : Fin 3 × Fin d)) + Finsupp.single ((0 : Fin 3), i) 1 =
        Finsupp.equivFunOnFinite.symm n := by
      ext ⟨a, j⟩
      refine Fin.cases ?_ (fun a => ?_) a
      · rw [Finsupp.add_apply, Finsupp.mapDomain_notin_range _ _
          (by rintro ⟨q, hq⟩; exact Fin.succ_ne_zero _ (congrArg Prod.fst hq))]
        simp [hn0, Finsupp.single_apply, Pi.single_apply, eq_comm]
      · rw [Finsupp.add_apply, Finsupp.mapDomain_apply hinj _ (a, j),
          Finsupp.single_eq_of_ne (fun h => Fin.succ_ne_zero _ (congrArg Prod.fst h))]
        simp
    rw [this, map_mul, Algebra.smul_def]
    ring

theorem evalPoints_first_order_of_eq_one : ∀ (R : Type) [CommRing R] (d : ℕ) (ph : PS R 3 d), ev (n := 2) ![0, pt R d 0, pt R d 1] ph = 1 → ∀ (A : Type) [CommRing A] [Algebra R A] (e : A), e ^ 2 = 0 → ∀ (u : Fin d → R) (b b' : Fin d → A), (∀ j, IsNilpotent (b j)) → (∀ j, IsNilpotent (b' j)) → evP ![fun j => u j • e, b, b'] ph = 1 + e * evP ![b, b'] (c2 ph u) := by
  intro R _ d ph hph A _ _ e he u b b' hb hb'
  rw [evalPoints_first_order_of_sq_eq_zero ph e he u b b' hb hb']
  congr 1
  have hn : ∀ q : Fin 2 × Fin d, IsNilpotent ((![b, b'] : Fin 2 → Fin d → A) q.1 q.2) := by
    rintro ⟨i, j⟩
    fin_cases i
    exacts [hb j, hb' j]
  have h := congrArg (fun f => nEval f fun q : Fin 2 × Fin d => (![b, b'] : Fin 2 → Fin d → A) q.1 q.2) hph
  beta_reduce at h
  rw [nEval_one hn, ev, ChartCompare.nEval_subst _ _ _ _ hn] at h
  · rw [← h, evP]
    congr 1
    funext ⟨i, j⟩
    fin_cases i
    · exact (ChartCompare.nEval_zero _ hn).symm
    · exact (ChartCompare.nEval_X _ hn (0, j)).symm
    · exact (ChartCompare.nEval_X _ hn (1, j)).symm
  · rintro ⟨i, j⟩
    fin_cases i <;> simp [pt]

end GlobalTheory.AlphaPair
