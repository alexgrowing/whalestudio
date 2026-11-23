import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameBasePtFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.LemCone
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace ProjFrameBasePtFree

theorem linForm_projMat {κ : Type} [Fintype κ] {D : ℕ} (e : Fin (D + 1) → Ix κ) (k : Fin (D + 1)) :
    linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e) ⟨(), k⟩ = X (e k) := by
  classical
  simp only [linForm, projMat]
  generalize e k = q
  obtain ⟨⟨⟩, j⟩ := q
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi
    simp [Ne.symm hi]
  · simp

theorem rename_mem_span {κ : Type} {D : ℕ} (e : Fin (D + 1) → Ix κ) {h : MvPolynomial (Fin (D + 1)) ℤ} {n : ℕ}
    (hh : h.IsHomogeneous n) (hn : 0 < n) :
    rename e h ∈ Ideal.span (Set.range fun k => (X (e k) : MvPolynomial (Ix κ) ℤ)) := by
  have h1 : h ∈ Ideal.span ((X : Fin (D + 1) → MvPolynomial (Fin (D + 1)) ℤ) '' Set.univ) := by
    rw [mem_ideal_span_X_image]
    intro m hm
    by_contra hcon
    push Not at hcon
    have hm0 : m = 0 := Finsupp.ext fun i => hcon i (Set.mem_univ i)
    have := hh (mem_support_iff.mp hm)
    rw [hm0, map_zero] at this
    omega
  have h2 := Ideal.mem_map_of_mem (rename e : MvPolynomial (Fin (D + 1)) ℤ →ₐ[ℤ] MvPolynomial (Ix κ) ℤ) h1
  rw [Ideal.map_span, Set.image_image, Set.image_univ] at h2
  simpa [rename_X] using h2

theorem pow_mem (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) (x : Ix κ → Ω)
    (e : Fin (D + 1) → Ix κ) (hfr : IsProjFrame x e) (p : Ix κ) :
    ∃ N : ℕ, (X p : MvPolynomial (Ix κ) ℤ) ^ N ∈
      coordIdeal ℤ x ⊔ Ideal.span (Set.range fun k => (X (e k) : MvPolynomial (Ix κ) ℤ)) := by
  obtain ⟨q, hmon, hq⟩ := hfr.integral p
  set N := q.natDegree with hNdef
  have hcoef : ∀ j, ∃ f : MvPolynomial (Fin (D + 1)) ℤ,
      coneMap ℤ (x ∘ e) f = ((q.coeff j : coneRing ℤ (x ∘ e)) : Polynomial Ω) :=
    fun j => (q.coeff j).2
  choose f hf using hcoef
  set F : MvPolynomial (Ix κ) ℤ := X p ^ N +
      ∑ j ∈ Finset.range N, rename e (homogeneousComponent (N - j) (f j)) * X p ^ j with hFdef
  have hFh : F.IsHomogeneous N := by
    refine (isHomogeneous_X_pow p N).add (IsHomogeneous.sum _ _ _ fun j hj => ?_)
    have hj' : N - j + j = N := Nat.sub_add_cancel (Finset.mem_range.mp hj).le
    have := ((homogeneousComponent_isHomogeneous (N - j) (f j)).rename_isHomogeneous (f := e)).mul
      (isHomogeneous_X_pow p j)
    rwa [hj'] at this
  have hFx : aeval x F = 0 := by
    have h0 := congrArg (fun r : Polynomial Ω => r.coeff N) hq
    simp only [Polynomial.coeff_zero] at h0
    rw [hmon.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_finsetSum, Polynomial.coeff_add,
      Polynomial.finsetSum_coeff] at h0
    rw [← h0, hFdef, map_add, map_sum]
    congr 1
    · rw [Polynomial.eval₂_X_pow, mul_pow, ← Polynomial.C_pow, Polynomial.coeff_C_mul_X_pow, if_pos rfl,
        map_pow, aeval_X]
    · refine Finset.sum_congr rfl fun j hj => ?_
      have hjN : j ≤ N := (Finset.mem_range.mp hj).le
      rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, mul_pow, ← Polynomial.C_pow,
        ← mul_assoc, Polynomial.coeff_mul_X_pow', if_pos hjN, Polynomial.coeff_mul_C]
      rw [map_mul, map_pow, aeval_X, aeval_rename]
      have : algebraMap (coneRing ℤ (x ∘ e)) (Polynomial Ω) (q.coeff j) = coneMap ℤ (x ∘ e) (f j) := (hf j).symm
      rw [this, coeff_coneMap]
  have hFP : F ∈ coordIdeal ℤ x := mem_coordIdeal_of_isHomogeneous ℤ x hFh hFx
  refine ⟨N, ?_⟩
  have hsum : (∑ j ∈ Finset.range N, rename e (homogeneousComponent (N - j) (f j)) * X p ^ j) ∈
      Ideal.span (Set.range fun k => (X (e k) : MvPolynomial (Ix κ) ℤ)) := by
    refine Ideal.sum_mem _ fun j hj => Ideal.mul_mem_right _ _ ?_
    have hjN : j < N := Finset.mem_range.mp hj
    exact rename_mem_span e (homogeneousComponent_isHomogeneous (N - j) (f j)) (by omega)
  have : (X p : MvPolynomial (Ix κ) ℤ) ^ N =
      F - ∑ j ∈ Finset.range N, rename e (homogeneousComponent (N - j) (f j)) * X p ^ j := by
    rw [hFdef]; ring
  rw [this]
  exact Ideal.sub_mem _ (Ideal.mem_sup_left hFP) (Ideal.mem_sup_right hsum)

end ProjFrameBasePtFree

open ProjFrameBasePtFree in

theorem ProjFrameBasePtFree.proof : ProjFrameBasePtFree.Statement := by
  intro D Ω _ _ κ _ x e hfr k₂ i
  obtain ⟨N, hN⟩ := pow_mem D Ω κ x e hfr ⟨(), i ()⟩
  refine ⟨N, ?_⟩
  have hspan : (Set.range fun j : GlobalTheory (Fin (D + 1)) k₂ =>
      linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e) ⟨k₂, j⟩) =
      Set.range fun k => (X (e k) : MvPolynomial (Ix κ) ℤ) := by
    cases k₂
    ext
    simp [linForm_projMat]
  rw [hspan, Fintype.prod_unique]
  exact hN

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
