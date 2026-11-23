import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeExtensionAlongFieldEmbeddingDuals
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum.TraceInt

theorem pair_integral {E : Type} [Field E] [NumberField E] [StarRing E] {N N' : ℕ}
    {L : Submodule (𝓞 E) (Fin N → E)} {L' : Submodule (𝓞 E) (Fin N' → E)}
    (hL : IsSDLat E N L) (hL' : IsSDLat E N' L') {A B : Matrix (Fin N') (Fin N) E}
    (hA : ∀ x ∈ L, A.mulVec x ∈ L') (hB : ∀ x ∈ L, B.mulVec x ∈ L') :
    IsIntegral ℤ (∑ i, ∑ j, A i j * star (B i j)) := by
  obtain ⟨hLfg, hLspan, hLdual⟩ := hL
  obtain ⟨-, -, hL'dual⟩ := hL'
  obtain ⟨m, x, φ, hx, hφ, hxφ⟩ := GlobalTheory.TauLat.exists_dual_family L ⟨hLfg, hLspan⟩

  set ψ : Fin m → Fin N → E := fun k b => star (φ k b) with hψdef
  have hψ : ∀ k, ψ k ∈ L := by
    intro k
    rw [hLdual]
    intro y hy
    rw [GlobalTheory.TauLat.mem_range_iff]
    have h1 : ∑ i, star (y i) * ψ k i = starRingEnd E (φ k ⬝ᵥ y) := by
      rw [starRingEnd_apply, dotProduct, star_sum]
      simp [hψdef, star_mul', mul_comm]
    unfold stdH
    rw [h1]
    exact GlobalTheory.TauLat.integral_map _ (hφ k y hy)

  have key : ∀ i, ∑ j, A i j * star (B i j) = ∑ k, (A.mulVec (x k)) i * star ((B.mulVec (ψ k)) i) := by
    intro i
    have e1 : ∑ j, A i j * star (B i j) =
        ∑ a, ∑ b, A i a * star (B i b) * ∑ k, x k a * φ k b := by
      refine Finset.sum_congr rfl fun a _ => ?_
      simp [hxφ, mul_ite]
    rw [e1]
    simp only [Matrix.mulVec, dotProduct, hψdef, star_sum, star_mul', star_star, Finset.mul_sum,
      Finset.sum_mul]
    conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [Finset.sum_congr rfl fun i _ => key i, Finset.sum_comm]
  refine IsIntegral.sum _ fun k _ => ?_

  have hint : IsIntegral ℤ (∑ i, star ((A.mulVec (x k)) i) * (B.mulVec (ψ k)) i) := by
    rw [← GlobalTheory.TauLat.mem_range_iff]
    exact (hL'dual _).1 (hB _ (hψ k)) _ (hA _ (hx k))
  have h2 : ∑ i, (A.mulVec (x k)) i * star ((B.mulVec (ψ k)) i) =
      starRingEnd E (∑ i, star ((A.mulVec (x k)) i) * (B.mulVec (ψ k)) i) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, starRingEnd_apply, starRingEnd_apply, star_star, mul_comm]
  rw [h2]
  exact GlobalTheory.TauLat.integral_map _ hint

theorem mulVec_mem_of_homL (D : D7) {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {A : Matrix (Fin N') (Fin N) D.host.E}
    (hA : A ∈ homL D L L') : ∀ x ∈ L, A.mulVec x ∈ L' := by
  unfold homL at hA
  induction hA using Submodule.span_induction with
  | mem B hB => exact hB
  | zero => intro x _; simp
  | add B C _ _ hB hC =>
    intro x hx
    rw [Matrix.add_mulVec]
    exact L'.add_mem (hB x hx) (hC x hx)
  | smul c B _ hB =>
    intro x hx
    rw [Matrix.smul_mulVec]
    exact L'.smul_mem c (hB x hx)

theorem hYY_add_left (D : D7) {N N' : ℕ} (x x' y : Matrix (Fin N') (Fin N) D.host.E) :
    hYY D (x + x') y = hYY D x y + hYY D x' y := by
  unfold hYY
  simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib, map_add]

theorem hYY_add_right (D : D7) {N N' : ℕ} (x y y' : Matrix (Fin N') (Fin N) D.host.E) :
    hYY D x (y + y') = hYY D x y + hYY D x y' := by
  unfold hYY
  simp only [Matrix.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem hYY_gen (D : D7) {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (hL : SD D L) (hL' : SD D L')
    {a a' : D.host.E} (ha : a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E))
    (ha' : a' ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E))
    {A B : Matrix (Fin N') (Fin N) D.host.E} (hA : A ∈ homL D L L') (hB : B ∈ homL D L L') :
    hYY D (a • A) (a' • B) ∈ (algebraMap (𝓞 D.host.K) D.host.K).range := by
  have hs : IsIntegral ℤ (∑ i, ∑ j, A i j * D.host.conj (B i j)) := by
    let _ := D.host.cmStar
    have h := pair_integral (E := D.host.E) hL hL' (mulVec_mem_of_homL D hA) (mulVec_mem_of_homL D hB)
    simpa only [bridge_star_holds _ D.host] using h
  have hsum : ∑ i, ∑ j, (a • A) i j * D.host.conj ((a' • B) i j) =
      a * (∑ i, ∑ j, A i j * D.host.conj (B i j)) * D.host.conj a' := by
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have has : a * (∑ i, ∑ j, A i j * D.host.conj (B i j)) ∈ D.host.AA0 := by
    have h1 : ∀ c : 𝓞 D.host.E, (c : D.host.E) * a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) := by
      intro c
      have h := (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).smul_mem c ha
      rwa [Algebra.smul_def] at h
    rw [mul_comm]
    exact h1 ⟨_, hs⟩
  unfold hYY
  rw [hsum]
  exact (factMMUnimodular _ D.host _).1 has a' ha'

private theorem exists_ringOfIntegers_eq_conj (D : D7) (c : 𝓞 D.host.E) :
    ∃ c' : 𝓞 D.host.E, (c' : D.host.E) = D.host.conj (c : D.host.E) :=
  ⟨⟨D.host.conj (c : D.host.E),
    GlobalTheory.TauLat.integral_map (D.host.conj : D.host.E →+* D.host.E) c.isIntegral_coe⟩, rfl⟩

private theorem conjO_conjO_unimodular_class_representatives (D : D7) (z : D.host.E) : D.host.conj (D.host.conj z) = z := by
  let _ := D.host.cmStar
  rw [← bridge_star_holds _ D.host z, ← bridge_star_holds _ D.host (star z), star_star]

private theorem hYY_smul_left_eq_conj_smul_right (D : D7) {N N' : ℕ} (c c' : 𝓞 D.host.E)
    (hc : (c' : D.host.E) = D.host.conj (c : D.host.E)) (x y : Matrix (Fin N') (Fin N) D.host.E) :
    hYY D (c • x) y = hYY D x (c' • y) := by
  unfold hYY
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_apply, Matrix.smul_apply, Algebra.smul_def, Algebra.smul_def, map_mul]
  change (c : D.host.E) * x i j * D.host.conj (y i j) =
    x i j * (D.host.conj (c' : D.host.E) * D.host.conj (y i j))
  rw [hc, conjO_conjO_unimodular_class_representatives]
  ring

private theorem hYY_smul_right_eq_conj_smul_left (D : D7) {N N' : ℕ} (c c' : 𝓞 D.host.E)
    (hc : (c' : D.host.E) = D.host.conj (c : D.host.E)) (x y : Matrix (Fin N') (Fin N) D.host.E) :
    hYY D x (c • y) = hYY D (c' • x) y := by
  have hc' : (c : D.host.E) = D.host.conj (c' : D.host.E) := by rw [hc, conjO_conjO_unimodular_class_representatives]
  exact (hYY_smul_left_eq_conj_smul_right D c' c hc' x y).symm

theorem hYY_integral : ∀ (D : D7) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D L → SD D L' →
    ∀ x ∈ YYl D L L', ∀ y ∈ YYl D L L', hYY D x y ∈ (algebraMap (𝓞 D.host.K) D.host.K).range := by
  intro D N N' L L' hL hL' x hx y hy
  have hsub : ∀ (c : 𝓞 D.host.E) (a : D.host.E),
      a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) →
      (c : D.host.E) * a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) := by
    intro c a ha
    have h := (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).smul_mem c ha
    rwa [Algebra.smul_def] at h

  have hgen : ∀ y ∈ YYl D L L', ∀ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E),
      ∀ A ∈ homL D L L', hYY D (a • A) y ∈ (algebraMap (𝓞 D.host.K) D.host.K).range := by
    intro y hy
    unfold YYl at hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a', ha', B, hB, rfl⟩ := hz
      intro a ha A hA
      exact hYY_gen D hL hL' ha ha' hA hB
    | zero =>
      intro a _ A _
      unfold hYY
      simp
    | add z w _ _ hz hw =>
      intro a ha A hA
      rw [hYY_add_right]
      exact Subring.add_mem _ (hz a ha A hA) (hw a ha A hA)
    | smul c z _ hz =>
      intro a ha A hA
      obtain ⟨c', hc'⟩ := exists_ringOfIntegers_eq_conj D c
      rw [hYY_smul_right_eq_conj_smul_left D c c' hc', ← smul_assoc, Algebra.smul_def]
      exact hz _ (hsub c' a ha) A hA
  unfold YYl at hx
  induction hx using Submodule.span_induction generalizing y with
  | mem z hz =>
    obtain ⟨a, ha, A, hA, rfl⟩ := hz
    exact hgen y hy a ha A hA
  | zero =>
    unfold hYY
    simp
  | add z w _ _ hz hw =>
    rw [hYY_add_left]
    exact Subring.add_mem _ (hz y hy) (hw y hy)
  | smul c z _ hz =>
    obtain ⟨c', hc'⟩ := exists_ringOfIntegers_eq_conj D c
    rw [hYY_smul_left_eq_conj_smul_right D c c' hc']
    exact hz _ ((YYl D L L').smul_mem c' hy)

end GlobalTheory.NormSum.TraceInt
