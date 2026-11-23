import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum

theorem exists_detIdeal_abstract {R K V ι : Type} [CommRing R] [CommRing K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    (B : V → V →ₗ[K] K) (hB : ∀ (s : ℕ) (y x : V), B ((s : K) • y) x = (s : K) * B y x)
    (Y : Set V) (b₀ : ι → V)
    (hY : ∀ x ∈ Y, ∀ y ∈ Y, B y x ∈ (algebraMap R K).range)
    (h0 : ∀ i, ∃ s : ℕ, 0 < s ∧ (s : K) • b₀ i ∈ Y) :
    ∃ I : Submodule R K, (∃ n : ℕ, 0 < n ∧ ∀ x ∈ I, (n : K) * x ∈ (algebraMap R K).range) ∧
      ∀ (p : ℕ) (b : ι → V), (∀ i, ∃ s : ℕ, Nat.Coprime s p ∧ (s : K) • b i ∈ Y) →
        (∀ y ∈ Y, ∃ s : ℕ, Nat.Coprime s p ∧ ∃ c : ι → R,
          (s : K) • y = ∑ i, algebraMap R K (c i) • b i) →
        (∃ s : ℕ, Nat.Coprime s p ∧ (s : K) * (Matrix.of fun i j => B (b₀ i) (b j)).det ∈ I) ∧
        ∀ x ∈ I, ∃ (s : ℕ) (c : R), Nat.Coprime s p ∧
          (s : K) * x = algebraMap R K c * (Matrix.of fun i j => B (b₀ i) (b j)).det := by
  have hcol : ∀ (s : ι → ℕ) (y : ι → V),
      (Matrix.of fun i j => B (b₀ i) ((s j : K) • y j)).det =
        ((∏ j, s j : ℕ) : K) * (Matrix.of fun i j => B (b₀ i) (y j)).det := by
    intro s y
    rw [Nat.cast_prod, ← Matrix.det_mul_row]
    congr 1
    ext i j
    simp
  refine ⟨Submodule.span R {d | ∃ y : ι → V, (∀ j, y j ∈ Y) ∧
    d = (Matrix.of fun i j => B (b₀ i) (y j)).det}, ?_, ?_⟩
  · choose s hs hsY using h0
    refine ⟨∏ i, s i, Finset.prod_pos fun i _ => hs i, ?_⟩
    intro x hx
    induction hx using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨y, hy, rfl⟩ := hd
      choose c hc using fun i j => hY (y j) (hy j) _ (hsY i)
      refine ⟨(Matrix.of c).det, ?_⟩
      rw [RingHom.map_det, Nat.cast_prod, ← Matrix.det_mul_column]
      congr 1
      ext i j
      simp [hc, hB]
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul a x _ hx =>
      rw [Algebra.smul_def, mul_left_comm]
      exact mul_mem ⟨a, rfl⟩ hx
  · intro p b h1 h2
    constructor
    · choose s hs hsY using h1
      refine ⟨∏ i, s i, Nat.Coprime.prod_left fun i _ => hs i, ?_⟩
      rw [← hcol]
      exact Submodule.subset_span ⟨_, hsY, rfl⟩
    · intro x hx
      induction hx using Submodule.span_induction with
      | mem d hd =>
        obtain ⟨y, hy, rfl⟩ := hd
        choose s hs c hc using fun j => h2 (y j) (hy j)
        refine ⟨∏ i, s i, (Matrix.of c).det, Nat.Coprime.prod_left fun i _ => hs i, ?_⟩
        rw [← hcol, RingHom.map_det, mul_comm, ← Matrix.det_transpose (RingHom.mapMatrix _ _),
          ← Matrix.det_mul]
        congr 1
        ext i j
        simp [hc, Matrix.mul_apply, mul_comm]
      | zero => exact ⟨1, 0, by simp, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨s, c, hs, hc⟩ := hx
        obtain ⟨t, d, ht, hd⟩ := hy
        refine ⟨s * t, t * c + s * d, Nat.Coprime.mul_left hs ht, ?_⟩
        simp only [Nat.cast_mul, map_add, map_mul, map_natCast]
        linear_combination (t : K) * hc + (s : K) * hd
      | smul a x _ hx =>
        obtain ⟨s, c, hs, hc⟩ := hx
        refine ⟨s, a * c, hs, ?_⟩
        rw [Algebra.smul_def, map_mul]
        linear_combination (algebraMap R K a) * hc

noncomputable def detIdealForm (D : D7) {N N' : ℕ} (y : Matrix (Fin N') (Fin N) D.host.E) :
    Matrix (Fin N') (Fin N) D.host.E →ₗ[D.host.K] D.host.K where
  toFun x := hYY D x y
  map_add' x x' := by
    simp only [hYY, Matrix.add_apply, add_mul, Finset.sum_add_distrib, map_add]
  map_smul' c x := by
    simp only [hYY, Matrix.smul_apply, smul_mul_assoc, ← Finset.smul_sum, map_smul, RingHom.id_apply]

theorem exists_detIdeal : ∀ (D : D7) (N N' r : ℕ) (Y : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E)) (b₀ : Fin r → Matrix (Fin N') (Fin N) D.host.E), (∀ x ∈ Y, ∀ y ∈ Y, hYY D x y ∈ (algebraMap (𝓞 D.host.K) D.host.K).range) → (∀ i, ∃ s : ℕ, 0 < s ∧ (s : D.host.E) • b₀ i ∈ Y) → ∃ I : Submodule (𝓞 D.host.K) D.host.K, (∃ n : ℕ, 0 < n ∧ ∀ x ∈ I, (n : D.host.K) * x ∈ (algebraMap (𝓞 D.host.K) D.host.K).range) ∧ ∀ (p : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), LocBasis D p Y b → (∃ s : ℕ, Nat.Coprime s p ∧ (s : D.host.K) * (Matrix.of fun i j => hYY D (b j) (b₀ i)).det ∈ I) ∧ ∀ x ∈ I, ∃ (s : ℕ) (c : 𝓞 D.host.K), Nat.Coprime s p ∧ (s : D.host.K) * x = (c : D.host.K) * (Matrix.of fun i j => hYY D (b j) (b₀ i)).det := by
  intro D N N' r Y b₀ hY h0
  have hsm : ∀ (s : ℕ) (y : Matrix (Fin N') (Fin N) D.host.E),
      (s : D.host.K) • y = (s : D.host.E) • y := by
    intro s y
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  obtain ⟨I, hI1, hI2⟩ := exists_detIdeal_abstract (R := 𝓞 D.host.K) (K := D.host.K)
    (detIdealForm D) (by
      intro s y x
      change hYY D x _ = _ * hYY D x y
      rw [hsm, ← smul_eq_mul, hYY, hYY, ← map_smul, Nat.cast_smul_eq_nsmul D.host.K, nsmul_eq_mul]
      congr 1
      simp only [Matrix.smul_apply, smul_eq_mul, map_mul, map_natCast, Finset.mul_sum, mul_left_comm])
    (Y : Set (Matrix (Fin N') (Fin N) D.host.E)) b₀ hY (by simpa only [hsm, SetLike.mem_coe] using h0)
  refine ⟨I, hI1, fun p b hb => hI2 p b ?_ ?_⟩
  · simpa only [hsm, SetLike.mem_coe] using hb.2.1
  · intro y hy
    obtain ⟨s, hs, c, hc⟩ := hb.2.2 y hy
    exact ⟨s, hs, c, by rw [hsm, hc]; rfl⟩

end GlobalTheory.NormSum
