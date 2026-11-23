import Mathlib
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.IsStarRep

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL PositivityTheory.Rg.Cz
open scoped Classical

namespace GlobalTheory.CompanionTheory.FrameCasimir

theorem sum_embeddings {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : Type} [AddCommMonoid N]
    (f : (E →+* ℂ) → N) :
    ∑ τ, f τ = ∑ v : InfinitePlace E, (f v.embedding + f (ComplexEmbedding.conjugate v.embedding)) := by
  rw [← Finset.sum_fiberwise Finset.univ (fun τ : E →+* ℂ => InfinitePlace.mk τ) f]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hne : v.embedding ≠ ComplexEmbedding.conjugate v.embedding := by
    intro h
    have hc : v.IsComplex := IsTotallyComplex.isComplex v
    exact (InfinitePlace.isComplex_iff.1 hc) (ComplexEmbedding.isReal_iff.2 h.symm)
  have hf : (Finset.univ.filter fun τ : E →+* ℂ => InfinitePlace.mk τ = v) =
      {v.embedding, ComplexEmbedding.conjugate v.embedding} := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro rfl
      rcases InfinitePlace.embedding_mk_eq τ with h | h
      · exact Or.inl h.symm
      · right
        rw [h]
        exact (star_star τ).symm
    · rintro (rfl | rfl)
      · exact InfinitePlace.mk_embedding v
      · rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  rw [hf, Finset.sum_pair hne]

theorem atEmb_embedding {E : Type} [Field E] (v : InfinitePlace E) (z : ℂ) :
    atEmb v.embedding z = (Pi.single v z : Cinf E) := by
  unfold atEmb
  rw [if_pos (by rw [InfinitePlace.mk_embedding])]
  congr 1 <;> simp

theorem map_single_atEmb {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} {N : Type} [AddCommGroup N]
    [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N] (φ : Lie E a →ₗ[ℝ] N) (τ : E →+* ℂ) (i j : Fin a) (z : ℂ) :
    φ (toL (Matrix.single i j (atEmb τ z))) =
      z • cx τ φ i j + starRingEnd ℂ z • cx (ComplexEmbedding.conjugate τ) φ i j := by
  let L : Cinf E →ₗ[ℝ] N :=
    { toFun := fun x => φ (toL (Matrix.single i j x))
      map_add' := fun x y => by
        rw [Matrix.single_add]
        exact φ.map_add _ _
      map_smul' := fun r x => by
        rw [← Matrix.smul_single]
        exact φ.map_smul r _ }
  have hL : ∀ x, φ (toL (Matrix.single i j x)) = L x := fun _ => rfl
  have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by
    rw [atEmb_eq]; simp
  rw [hL, atEmb_eq, map_add, map_smul, map_smul]
  simp only [cx, hL, atEmb_conj, map_one, Complex.conj_I, e, map_neg]
  have h1 := Complex.add_conj z
  have h2 := Complex.sub_conj z
  push_cast at h1 h2
  match_scalars
  · simp only [Complex.coe_algebraMap]; linear_combination (-1 / 2 : ℂ) * h1
  · simp only [Complex.coe_algebraMap]; linear_combination (Complex.I / 2 : ℂ) * h2 + z.im * Complex.I_mul_I

theorem alg_sq {R : Type} [Ring R] [Algebra ℂ R] (u w : R) :
    (u + w) * (u + w) - (Complex.I • u - Complex.I • w) * (Complex.I • u - Complex.I • w) =
      (2 : ℂ) • (u * u) + (2 : ℂ) • (w * w) := by
  rw [← smul_sub, smul_mul_smul_comm, Complex.I_mul_I]
  simp only [mul_add, add_mul, sub_mul, mul_sub]
  module

theorem alg_sum {R : Type} [Ring R] [Algebra ℂ R] {a : ℕ} (P : Fin a → Fin a → R) (c d : ℂ)
    (h0 : c * c + d * d = 0) (h1 : 2 * (c * d) = 1) :
    ∑ i, ∑ j, (c • P i j + d • P j i) * (c • P i j + d • P j i) = ∑ i, ∑ j, P i j * P j i := by
  have e : ∀ i j, (c • P i j + d • P j i) * (c • P i j + d • P j i) =
      (c * c) • (P i j * P i j) + (c * d) • (P i j * P j i) + (c * d) • (P j i * P i j) + (d * d) • (P j i * P j i) := by
    intro i j
    simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm]
    module
  simp only [e, Finset.sum_add_distrib, ← Finset.smul_sum]
  rw [Finset.sum_comm (f := fun i j => P j i * P i j), Finset.sum_comm (f := fun i j => P j i * P j i)]
  generalize (∑ i, ∑ j, P i j * P i j) = S
  generalize (∑ i, ∑ j, P i j * P j i) = T
  calc (c * c) • S + (c * d) • T + (c * d) • T + (d * d) • S = (c * c + d * d) • S + (2 * (c * d)) • T := by module
    _ = T := by rw [h0, h1, zero_smul, one_smul, zero_add]

theorem iM_single {E : Type} [Field E] {a : ℕ} (v : InfinitePlace E) (i j : Fin a) (z : ℂ) :
    iM (Matrix.single i j (Pi.single v z : Cinf E)) = Matrix.single i j (Pi.single v (Complex.I * z) : Cinf E) := by
  unfold iM
  rw [Matrix.smul_single]
  congr 1
  funext w
  by_cases hw : w = v
  · subst hw
    simp
  · simp [Pi.single_eq_of_ne hw]

theorem fr_val {E : Type} [Field E] {a : ℕ} (v : InfinitePlace E) (i j : Fin a) :
    (fr (v, i, j) : Herm E a).1 = Matrix.single i j (Pi.single v ((1 + Complex.I) / 2) : Cinf E) +
      Matrix.single j i (Pi.single v (starRingEnd ℂ ((1 + Complex.I) / 2)) : Cinf E) := by
  change frU (v, i, j) + star (frU (v, i, j)) = _
  congr 1
  unfold frU
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single]
  congr 1
  funext w
  by_cases hw : w = v
  · subst hw
    simp only [Pi.star_apply, Pi.single_eq_same, Complex.star_def]
  · simp [Pi.single_eq_of_ne hw]

theorem frameCas : FrameCas := by
  intro E _ _ _ a M _ _ _ _ φ
  set c : ℂ := (1 + Complex.I) / 2 with hc
  have hc0 : c * c + starRingEnd ℂ c * starRingEnd ℂ c = 0 := by
    simp only [hc, map_div₀, map_add, map_one, Complex.conj_I, map_ofNat]
    ring_nf
    simp
  have hc1 : 2 * (c * starRingEnd ℂ c) = 1 := by
    simp only [hc, map_div₀, map_add, map_one, Complex.conj_I, map_ofNat]
    ring_nf
    simp
    norm_num
  let P : InfinitePlace E → Fin a → Fin a → Module.End ℂ M := fun v => cx v.embedding φ
  let Q : InfinitePlace E → Fin a → Fin a → Module.End ℂ M := fun v => cx (ComplexEmbedding.conjugate v.embedding) φ
  let u : InfinitePlace E → Fin a → Fin a → Module.End ℂ M := fun v i j => c • P v i j + starRingEnd ℂ c • P v j i
  let w : InfinitePlace E → Fin a → Fin a → Module.End ℂ M := fun v i j => starRingEnd ℂ c • Q v i j + c • Q v j i
  have hs : ∀ v i j z, φ (toL (Matrix.single i j (Pi.single v z : Cinf E))) = z • P v i j + starRingEnd ℂ z • Q v i j := by
    intro v i j z
    rw [← atEmb_embedding]
    exact map_single_atEmb φ v.embedding i j z
  have hadd : ∀ A B : Matrix (Fin a) (Fin a) (Cinf E), φ (toL (A + B)) = φ (toL A) + φ (toL B) :=
    fun A B => φ.map_add (toL A) (toL B)
  have hfr : ∀ v i j, φ (toL (fr (v, i, j) : Herm E a).1) = u v i j + w v i j := by
    intro v i j
    rw [fr_val, hadd, hs, hs, Complex.conj_conj]
    simp only [u, w]
    abel
  have hiM : ∀ v i j, φ (toL (iM (fr (v, i, j) : Herm E a).1)) = Complex.I • u v i j - Complex.I • w v i j := by
    intro v i j
    have e : iM ((fr (v, i, j) : Herm E a).1) = iM (Matrix.single i j (Pi.single v c : Cinf E)) +
        iM (Matrix.single j i (Pi.single v (starRingEnd ℂ c) : Cinf E)) := by
      rw [fr_val]
      exact smul_add _ _ _
    rw [e, iM_single, iM_single, hadd, hs, hs]
    simp only [u, w, map_mul, Complex.conj_I, Complex.conj_conj]
    module
  have L1 : ∑ k : InfinitePlace E × Fin a × Fin a, φ (toL (fr k : Herm E a).1) * φ (toL (fr k : Herm E a).1) =
      ∑ v, ∑ i, ∑ j, (u v i j + w v i j) * (u v i j + w v i j) := by
    simp only [Fintype.sum_prod_type, hfr]
  have L2 : ∑ k : InfinitePlace E × Fin a × Fin a, φ (toL (iM (fr k : Herm E a).1)) * φ (toL (iM (fr k : Herm E a).1)) =
      ∑ v, ∑ i, ∑ j, (Complex.I • u v i j - Complex.I • w v i j) * (Complex.I • u v i j - Complex.I • w v i j) := by
    simp only [Fintype.sum_prod_type, hiM]
  rw [L1, L2, sum_embeddings, Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hu : ∑ i, ∑ j, u v i j * u v i j = ∑ i, ∑ j, P v i j * P v j i :=
    alg_sum (P v) c (starRingEnd ℂ c) hc0 hc1
  have hw : ∑ i, ∑ j, w v i j * w v i j = ∑ i, ∑ j, Q v i j * Q v j i :=
    alg_sum (Q v) (starRingEnd ℂ c) c (by rw [add_comm]; exact hc0) (by rw [mul_comm (starRingEnd ℂ c)]; exact hc1)
  change _ = (2 : ℂ) • (∑ i, ∑ j, P v i j * P v j i + ∑ i, ∑ j, Q v i j * Q v j i)
  rw [← hu, ← hw, smul_add, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => alg_sq _ _

end GlobalTheory.CompanionTheory.FrameCasimir
