import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableComb
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthonormalTransitionDetMulConjEqOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RatOfImEqZero
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.FourCopies

theorem exists_orthogonal_family {K V : Type} [Field K] [AddCommGroup V] [Module K V] (h : V → V →ₗ[K] K)
    (hsym : ∀ x y, h y x = 0 → h x y = 0) (hdef : ∀ x, h x x = 0 → x = 0) (s : Finset V) :
    ∃ (n : ℕ) (v : Fin n → V), (∀ i, v i ≠ 0) ∧ (∀ i j, i ≠ j → h (v j) (v i) = 0) ∧
      ∀ x ∈ s, x ∈ Submodule.span K (Set.range v) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, by simp⟩
  | insert x s _ ih =>
    obtain ⟨n, v, h0, ho, hs⟩ := ih
    set p : V := ∑ i, (h (v i) x / h (v i) (v i)) • v i with hp
    have hpm : p ∈ Submodule.span K (Set.range v) :=
      sum_mem fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hx : ∀ j, h (v j) (x - p) = 0 := by
      intro j
      have hj : h (v j) (v j) ≠ 0 := fun e => h0 j (hdef _ e)
      rw [map_sub, hp, map_sum, Finset.sum_eq_single j]
      · rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hj, sub_self]
      · intro i _ hij
        rw [map_smul, ho i j hij, smul_zero]
      · simp
    by_cases hz : x - p = 0
    · refine ⟨n, v, h0, ho, fun y hy => ?_⟩
      rcases Finset.mem_insert.1 hy with rfl | hy
      · rw [sub_eq_zero.1 hz]; exact hpm
      · exact hs y hy
    · have hle : Submodule.span K (Set.range v) ≤
          Submodule.span K (Set.range (Fin.cons (x - p) v : Fin (n + 1) → V)) :=
        Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨i.succ, by simp⟩)
      refine ⟨n + 1, Fin.cons (x - p) v, fun i => ?_, fun i j hij => ?_, fun y hy => ?_⟩
      · refine Fin.cases ?_ (fun i => ?_) i
        · simpa using hz
        · simpa using h0 i
      · revert hij
        refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> intro hij
        · exact absurd rfl hij
        · exact hx j
        · exact hsym _ _ (hx i)
        · exact ho i j (fun e => hij (by rw [e]))
      · rcases Finset.mem_insert.1 hy with rfl | hy
        · have := add_mem (Submodule.subset_span (Set.mem_range_self 0)) (hle hpm)
          rwa [Fin.cons_zero, sub_add_cancel] at this
        · exact hle (hs y hy)

theorem exists_similitude (a : ℚ) (ha : 0 < a) :
    ∃ A : Fin 4 → Fin 4 → ℚ, (∀ j j', a * ∑ k, A j k * A j' k = if j = j' then 1 else 0) ∧
      ∀ k k', a * ∑ j, A j k * A j k' = if k = k' then 1 else 0 := by
  obtain ⟨p, q, r, s, h⟩ := Nat.sum_four_squares (a.num.natAbs * a.den)
  have hn : (0 : ℚ) < a.num := by exact_mod_cast Rat.num_pos.2 ha
  have h1 : ((a.num.natAbs : ℕ) : ℚ) = a.num := by
    rw [Nat.cast_natAbs, abs_of_pos (Rat.num_pos.2 ha)]
  have h2 : (p : ℚ) ^ 2 + q ^ 2 + r ^ 2 + s ^ 2 = a.num * a.den := by
    rw [← h1]; exact_mod_cast h
  have h3 : a * a.den = a.num := Rat.mul_den_eq_num a
  obtain ⟨p, q, r, s, h⟩ : ∃ p q r s : ℚ, a * (p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2) = 1 := by
    refine ⟨p / a.num, q / a.num, r / a.num, s / a.num, ?_⟩
    simp only [div_pow, ← add_div, h2]
    field_simp
    linear_combination h3
  refine ⟨![![p, q, r, s], ![-q, p, -s, r], ![-r, s, p, -q], ![-s, -r, q, p]], fun j j' => ?_, fun j j' => ?_⟩ <;>
    fin_cases j <;> fin_cases j' <;> simp [Fin.sum_univ_four] <;>
    first | linear_combination h | (right; ring)

variable (D : D7)

theorem exists_rat_of_real (x : D.host.K) (hx : (D.host.φ₀ (x : D.host.E)).im = 0) : ∃ a : ℚ, x = (a : D.host.K) :=
  by apply _root_.GlobalTheory.RationalOfReal.rat_of_real <;> assumption

theorem exists_rat_pos {N N' : ℕ} (x : Matrix (Fin N') (Fin N) D.host.E) (hx : x ≠ 0) :
    ∃ a : ℚ, 0 < a ∧ hYY D x x = (a : D.host.K) := by
  have hc : ∀ (φ : D.host.E →+* ℂ) (z : D.host.E), φ (D.host.conj z) = starRingEnd ℂ (φ z) :=
    fun φ z => D.host.conjE_apply φ z
  have h : D.host.φ₀ ((hYY D x x : D.host.K) : D.host.E) =
      ((∑ τ, ∑ i, ∑ j, Complex.normSq (embT D τ (x i j)) : ℝ) : ℂ) := by
    unfold hYY
    rw [← (GlobalTheory.InducedType.induced_type D).1.2]
    simp only [map_sum, map_mul, hc, Complex.mul_conj]
    push_cast
    rfl
  obtain ⟨a, ha⟩ := exists_rat_of_real D (hYY D x x) (by rw [h, Complex.ofReal_im])
  refine ⟨a, ?_, ha⟩
  obtain ⟨i, j, hij⟩ : ∃ i j, x i j ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hx (Matrix.ext hh)
  have hpos : 0 < ∑ τ, ∑ i, ∑ j, Complex.normSq (embT D τ (x i j)) := by
    have nn := fun τ i j => Complex.normSq_nonneg (embT D τ (x i j))
    refine Finset.sum_pos' (fun τ _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => nn τ i j)
      ⟨D.eTau.symm 1, Finset.mem_univ _, ?_⟩
    refine Finset.sum_pos' (fun i _ => Finset.sum_nonneg fun j _ => nn _ i j) ⟨i, Finset.mem_univ _, ?_⟩
    refine Finset.sum_pos' (fun j _ => nn _ i j) ⟨j, Finset.mem_univ _, ?_⟩
    exact Complex.normSq_pos.2 ((map_ne_zero _).2 hij)
  rw [ha] at h
  have h' : ((a : ℝ) : ℂ) = ((∑ τ, ∑ i, ∑ j, Complex.normSq (embT D τ (x i j)) : ℝ) : ℂ) := by
    rw [← h]; simp
  rw [← Complex.ofReal_injective h'] at hpos
  exact_mod_cast hpos

def cols (N : ℕ) : Fin (N + 3 * N) ≃ Fin 4 × Fin N :=
  (finCongr (by ring)).trans finProdFinEquiv.symm

def blocks {N N' : ℕ} (c : Fin 4 → ℚ) :
    Matrix (Fin N') (Fin N) D.host.E →ₗ[D.host.K] Matrix (Fin N') (Fin (N + 3 * N)) D.host.E where
  toFun v := fun i j => (c (cols N j).1 : D.host.E) * v i (cols N j).2
  map_add' v w := by
    funext i j
    exact mul_add _ _ _
  map_smul' a v := by
    funext i j
    exact mul_smul_comm a _ (v i (cols N j).2)

theorem blocks_apply {N N' : ℕ} (c : Fin 4 → ℚ) (v : Matrix (Fin N') (Fin N) D.host.E) (i j) :
    blocks D c v i j = (c (cols N j).1 : D.host.E) * v i (cols N j).2 := rfl

theorem hYY_blocks {N N' : ℕ} (c c' : Fin 4 → ℚ) (v w : Matrix (Fin N') (Fin N) D.host.E) :
    hYY D (blocks D c v) (blocks D c' w) = ((∑ k, c k * c' k : ℚ) : D.host.K) * hYY D v w := by
  unfold hYY
  rw [← smul_eq_mul ((∑ k, c k * c' k : ℚ) : D.host.K), ← map_smul, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← (cols N).symm.sum_comp, Fintype.sum_prod_type, Algebra.smul_def, map_ratCast]
  simp only [blocks_apply, Equiv.apply_symm_apply, map_mul, map_ratCast]
  push_cast
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

theorem exists_onB_four : ∀ (D : D7) (N N' : ℕ), ∃ (m r : ℕ) (b : Fin r → Matrix (Fin N') (Fin (N + m)) D.host.E), OnB D b := by
  intro D N N'
  obtain ⟨s, hs⟩ : (⊤ : Submodule D.host.K (Matrix (Fin N') (Fin N) D.host.E)).FG := Module.Finite.fg_top
  obtain ⟨n, v, h0, ho, hsp⟩ := exists_orthogonal_family (hYYLeft D (N := N) (N' := N'))
    (fun x y e => by
      have h1 := hYY_herm D (GlobalTheory.InducedType.induced_type D).1.2 x y
      change hYY D x y = 0 at e
      change hYY D y x = 0
      rw [e] at h1
      simpa using h1)
    (fun x e => by
      by_contra hx
      obtain ⟨a, ha, h1⟩ := exists_rat_pos D x hx
      change hYY D x x = 0 at e
      rw [e] at h1
      exact ha.ne' (by exact_mod_cast h1.symm)) s
  have htop : ∀ x, x ∈ Submodule.span D.host.K (Set.range v) := fun x =>
    (Submodule.span_le.2 (fun y hy => hsp y hy) : Submodule.span D.host.K (s : Set _) ≤ _) (by rw [hs]; trivial)
  choose a ha hav using fun i => exists_rat_pos D (v i) (h0 i)
  choose A hA hA' using fun i => exists_similitude (a i) (ha i)
  let e : Fin (n * 4) ≃ Fin n × Fin 4 := finProdFinEquiv.symm
  refine ⟨3 * N, n * 4, fun l => blocks D (A (e l).1 (e l).2) (v (e l).1), fun l l' => ?_, ?_⟩
  · rw [hYY_blocks]
    by_cases hi : (e l).1 = (e l').1
    · rw [← hi, hav, ← Rat.cast_mul, mul_comm, hA]
      have : (e l).2 = (e l').2 ↔ l = l' := ⟨fun h => e.injective (Prod.ext hi h), fun h => by rw [h]⟩
      simp only [this]
      split_ifs <;> simp
    · have : l ≠ l' := fun h => hi (by rw [h])
      rw [if_neg this, show hYY D (v (e l).1) (v (e l').1) = 0 from ho _ _ hi, mul_zero]
  · set W := Submodule.span D.host.K (Set.range fun l => blocks D (A (e l).1 (e l).2) (v (e l).1)) with hW
    have hb : ∀ i j, blocks D (A i j) (v i) ∈ W := fun i j =>
      Submodule.subset_span ⟨e.symm (i, j), by simp only [Equiv.apply_symm_apply]⟩
    have h1 : ∀ (k : Fin 4) i, blocks D (fun k' => if k = k' then 1 else 0) (v i) ∈ W := by
      intro k i
      have : blocks D (fun k' => if k = k' then 1 else 0) (v i) =
          ∑ j, ((a i * A i j k : ℚ) : D.host.K) • blocks D (A i j) (v i) := by
        funext s t
        simp only [Matrix.sum_apply, Matrix.smul_apply, blocks_apply, Algebra.smul_def, map_ratCast]
        rw [← hA' i]
        push_cast
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [this]
      exact sum_mem fun j _ => W.smul_mem _ (hb i j)
    have h2 : ∀ (k : Fin 4) x, blocks D (fun k' => if k = k' then 1 else 0) x ∈ W := by
      intro k x
      have : Submodule.span D.host.K (Set.range v) ≤ W.comap (blocks D fun k' => if k = k' then 1 else 0) :=
        Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact h1 k i)
      exact this (htop x)
    rw [eq_top_iff]
    intro x _
    have : x = ∑ k : Fin 4, blocks D (fun k' => if k = k' then 1 else 0)
        (Matrix.of fun i j => x i ((cols N).symm (k, j))) := by
      funext s t
      simp only [Matrix.sum_apply, blocks_apply, Matrix.of_apply]
      rw [Finset.sum_eq_single (cols N t).1]
      · simp
      · intro k _ hk
        simp [hk]
      · simp
    rw [this]
    exact sum_mem fun k _ => h2 k _

end GlobalTheory.FourCopies
