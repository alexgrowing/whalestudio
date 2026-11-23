import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum

noncomputable def hYYLeft (D : D7) {N N' : ℕ} (y : Matrix (Fin N') (Fin N) D.host.E) :
    Matrix (Fin N') (Fin N) D.host.E →ₗ[D.host.K] D.host.K where
  toFun x := hYY D x y
  map_add' x x' := by
    simp only [hYY, Matrix.add_apply, add_mul, Finset.sum_add_distrib, map_add]
  map_smul' c x := by
    simp only [hYY, Matrix.smul_apply, smul_mul_assoc, RingHom.id_apply]
    rw [← map_smul, Finset.smul_sum]
    simp only [Finset.smul_sum]

theorem hYY_herm (D : D7) (h : TraceMapNormalisation D) {N N' : ℕ} (x y : Matrix (Fin N') (Fin N) D.host.E) :
    D.host.φ₀ ((hYY D y x : D.host.K) : D.host.E) =
      starRingEnd ℂ (D.host.φ₀ ((hYY D x y : D.host.K) : D.host.E)) := by
  have hc : ∀ (φ : D.host.E →+* ℂ) (z : D.host.E), φ (D.host.conj z) = starRingEnd ℂ (φ z) :=
    fun φ z => D.host.conjE_apply φ z
  unfold hYY
  rw [← h, ← h]
  simp only [map_sum, map_mul, hc, Complex.conj_conj]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem onB_expand (D : D7) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (hb : OnB D b)
    (x : Matrix (Fin N') (Fin N) D.host.E) : x = ∑ i, hYY D x (b i) • b i := by
  have hx : x ∈ Submodule.span D.host.K (Set.range b) := by rw [hb.2]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.K).1 hx
  have h1 : ∀ k, hYY D x (b k) = c k := by
    intro k
    change hYYLeft D (b k) x = c k
    rw [← hc, map_sum]
    have h2 : ∀ i, hYYLeft D (b k) (c i • b i) = if i = k then c i else 0 := by
      intro i
      rw [map_smul]
      change c i • hYY D (b i) (b k) = _
      rw [hb.1 i k]
      split_ifs <;> simp
    simp only [h2]
    simp
  simp only [h1]
  exact hc.symm

theorem onB_parseval (D : D7) (h : TraceMapNormalisation D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (hb : OnB D b) (x y : Matrix (Fin N') (Fin N) D.host.E) :
    D.host.φ₀ ((hYY D x y : D.host.K) : D.host.E) =
      ∑ i, D.host.φ₀ ((hYY D x (b i) : D.host.K) : D.host.E) *
        starRingEnd ℂ (D.host.φ₀ ((hYY D y (b i) : D.host.K) : D.host.E)) := by
  have h1 : hYY D x y = ∑ i, hYY D x (b i) * hYY D (b i) y := by
    change hYYLeft D y x = _
    conv_lhs => rw [onB_expand D b hb x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    rfl
  have h2 := congrArg (D.host.φ₀.comp (algebraMap D.host.K D.host.E)) h1
  rw [map_sum] at h2
  refine h2.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [map_mul, ← hYY_herm D h y (b i)]
  rfl

theorem det_onB_mul_conj : ∀ (D : D7), admG1 D → ∀ (N N' r : ℕ) (b₀ b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b₀ → OnB D b → (((Matrix.of fun i j => hYY D (b j) (b₀ i)).det : D.host.K) : D.host.E) * D.host.conj (((Matrix.of fun i j => hYY D (b j) (b₀ i)).det : D.host.K) : D.host.E) = 1 := by
  intro D hD N N' r b₀ b hb₀ hb
  have hc : ∀ (φ : D.host.E →+* ℂ) (z : D.host.E), φ (D.host.conj z) = starRingEnd ℂ (φ z) :=
    fun φ z => D.host.conjE_apply φ z
  set M : Matrix (Fin r) (Fin r) D.host.K := Matrix.of fun i j => hYY D (b j) (b₀ i) with hM
  let ψ : D.host.K →+* ℂ := D.host.φ₀.comp (algebraMap D.host.K D.host.E)
  have hA : (ψ.mapMatrix M).transpose * (starRingEnd ℂ).mapMatrix (ψ.mapMatrix M) = 1 := by
    ext j k
    rw [Matrix.mul_apply]
    have h1 := onB_parseval D hD.2 b₀ hb₀ (b j) (b k)
    rw [hb.1 j k] at h1
    refine Eq.trans h1.symm ?_
    rw [Matrix.one_apply]
    split_ifs
    · exact map_one ψ
    · exact map_zero ψ
  have hdet := congrArg Matrix.det hA
  rw [Matrix.det_mul, Matrix.det_transpose, ← RingHom.map_det (starRingEnd ℂ), ← RingHom.map_det ψ, Matrix.det_one] at hdet
  apply D.host.φ₀.injective
  rw [map_mul, hc, map_one]
  exact hdet

end GlobalTheory.NormSum
