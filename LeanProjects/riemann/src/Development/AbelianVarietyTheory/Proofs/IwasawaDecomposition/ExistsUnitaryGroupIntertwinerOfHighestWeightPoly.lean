import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import ReciprocityTheory.DualLattices.FischerSelfNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntertwinerIrreducibleUnitaryHighestWeightStatement

open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HighestPolynomial

open MvPolynomial ReciprocityTheory.PGsh

theorem differentiable_rowSubst {k : ℕ} {κ : Type} {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (P : MvPolynomial (Fin k × κ) ℂ) (ψ : MvPolynomial (Fin k × κ) ℂ →ₗ[ℂ] F) :
    Differentiable ℂ fun g : Fin k → Fin k → ℂ => ψ (rowSubst (Matrix.of g) P) := by
  induction P using MvPolynomial.induction_on generalizing ψ with
  | C c => simp only [rowSubst_C]; exact differentiable_const _
  | add p q hp hq => simp only [map_add]; exact (hp ψ).add (hq ψ)
  | mul_X p s hp =>
    have h : (fun g : Fin k → Fin k → ℂ => ψ (rowSubst (Matrix.of g) (p * X s))) =
        fun g : Fin k → Fin k → ℂ => ∑ l, g l s.1 •
          (ψ ∘ₗ LinearMap.mulRight ℂ (X (l, s.2))) (rowSubst (Matrix.of g) p) := by
      funext g
      rw [map_mul, rowSubst_X, Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [LinearMap.comp_apply, LinearMap.mulRight_apply, ← map_smul, MvPolynomial.smul_eq_C_mul, Matrix.of_apply]
      congr 1
      ring
    rw [h]
    refine Differentiable.fun_sum fun l _ => Differentiable.smul ?_ (hp _)
    fun_prop

theorem totalDegree_rowSubst_le {k : ℕ} {κ : Type} (g : Matrix (Fin k) (Fin k) ℂ)
    (P : MvPolynomial (Fin k × κ) ℂ) : (rowSubst g P).totalDegree ≤ P.totalDegree :=
  totalDegree_aeval_le _ (fun _ => totalDegree_finsetSum_le fun _ _ =>
    (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X])) P

theorem fischer_conj {k : ℕ} {κ : Type} (P Q : MvPolynomial (Fin k × κ) ℂ) :
    starRingEnd ℂ (fischer P Q) = fischer Q P := by
  classical
  rw [fischer_eq_sum P Q (P.support ∪ Q.support) Finset.subset_union_left,
    fischer_eq_sum Q P (P.support ∪ Q.support) Finset.subset_union_right, map_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  simp only [fw, map_mul, Complex.conj_conj, map_natCast]
  ring

theorem fischer_self_re_nonneg {k : ℕ} {κ : Type} (P : MvPolynomial (Fin k × κ) ℂ) : 0 ≤ (fischer P P).re := by
  rw [fischer_eq_sum P P P.support subset_rfl, Complex.re_sum]
  refine Finset.sum_nonneg fun A _ => ?_
  rw [Complex.mul_conj, fw, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)

@[reducible] def fischerCore {k : ℕ} {κ : Type} (S : Submodule ℂ (MvPolynomial (Fin k × κ) ℂ)) :
    InnerProductSpace.Core ℂ S where
  inner x y := fischer y.1 x.1
  conj_inner_symm x y := fischer_conj _ _
  re_inner_nonneg x := fischer_self_re_nonneg _
  add_left x y z := fischer_add_right _ _ _
  smul_left x y r := fischer_smul_right _ _ _
  definite x hx := by
    by_contra h
    exact fischer_self_ne_zero x.1 (fun h' => h (Subtype.ext h')) hx

theorem mem_UJset_allPos {k : ℕ} {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ UJset (allPos k)) : gᴴ * g = 1 := by
  have hJ : Formalism.REAL.Jm (allPos k) = 1 := by simp [Formalism.REAL.Jm, allPos]
  have h : gᴴ * Formalism.REAL.Jm (allPos k) * g = Formalism.REAL.Jm (allPos k) := hg
  rwa [hJ, Matrix.mul_one] at h

theorem exists_intertwiner_of_embedding (k : ℕ) (κ : Type) (ν : Fin k → ℕ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (τ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H))
    (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (j : E →ₗ[ℂ] MvPolynomial (Fin k × κ) ℂ) (hj : Function.Injective j)
    (hin : ∀ x y : E, inner ℂ x y = fischer (j y) (j x))
    (hst : ∀ g x, ∃ y, j y = rowSubst g (j x)) (D : E)
    (hτ : IsURepOn (UJset (allPos k)) τ) (hK : IsKTypeOf (allPos k) τ (fun a => (ν a : ℝ)) ⊤) (hD : j D ≠ 0)
    (hu : ∀ g, IsUpperUnitri g → rowSubst g (j D) = j D)
    (hd : ∀ d : Fin k → ℂ, rowSubst (Matrix.diagonal d) (j D) = (∏ a, d a ^ ν a) • j D) :
    ∃ L : H →ₗ[ℂ] MvPolynomial (Fin k × κ) ℂ,
      (∀ g ∈ UJset (allPos k), ∀ u, L (τ g u) = rowSubst g (L u)) ∧ ∃ v, L v = j D := by
  obtain ⟨r, hr⟩ := j.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hj)
  have hrj : ∀ x, r (j x) = x := fun x => LinearMap.congr_fun hr x
  let π : Matrix (Fin k) (Fin k) ℂ → (E →L[ℂ] E) := fun g =>
    LinearMap.toContinuousLinearMap (r ∘ₗ (rowSubst g).toLinearMap ∘ₗ j)
  have hπ : ∀ g x, π g x = r (rowSubst g (j x)) := fun g x => rfl
  have hjπ : ∀ g x, j (π g x) = rowSubst g (j x) := by
    intro g x
    obtain ⟨y, hy⟩ := hst g x
    rw [hπ, ← hy, hrj]
  have hdiff : ∀ w : E, Differentiable ℂ fun g : Fin k → Fin k → ℂ => π (Matrix.of g) w := fun w =>
    differentiable_rowSubst (j w) r
  have hrep : IsURepOn (UJset (allPos k)) π := by
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · ext x
      apply hj
      rw [hjπ, rowSubst_one]
      rfl
    · intro a _ b _
      ext x
      apply hj
      change _ = j (π a (π b x))
      rw [hjπ, hjπ, hjπ, rowSubst_mul]
    · intro g hg v
      rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ _ _ _ _ v, hin, hin, hjπ, fischer_rowSubst,
        rowSubst_mul, mem_UJset_allPos hg, rowSubst_one]
    · intro v
      exact (hdiff v).continuous.continuousOn
  obtain ⟨L, hL, v, hv⟩ := GlobalTheory.T.exists_intertwiner_with_highestWeight_vector_in_range k (fun a => (ν a : ℝ)) H τ E π D hτ hK hrep (fun w => hdiff w _)
    (fun h => hD (by rw [h, map_zero]))
    (by
      intro a b hab s
      apply hj
      rw [hjπ]
      refine hu _ ⟨fun i => ?_, fun i l hl => ?_⟩
      · rw [Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply_of_ne, add_zero]
        rintro ⟨h1, h2⟩
        exact hab.ne (h1.trans h2.symm)
      · rw [Matrix.add_apply, Matrix.one_apply_ne hl.ne', Matrix.single_apply_of_ne, add_zero]
        rintro ⟨h1, h2⟩
        subst h1 h2
        exact lt_asymm hab hl)
    (by
      intro θ _
      apply hj
      rw [hjπ, hd, map_smul]
      congr 1
      push_cast
      rw [Finset.sum_mul, Complex.exp_sum]
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [← Complex.exp_nat_mul, mul_assoc])
  exact ⟨j ∘ₗ L, fun g hg u => by rw [LinearMap.comp_apply, hL g hg, hjπ]; rfl, v, by rw [LinearMap.comp_apply, hv]⟩

theorem exists_intertwiner : ∀ (k : ℕ) (κ : Type) [Fintype κ] (ν : Fin k → ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (τ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)) (Δ : MvPolynomial (Fin k × κ) ℂ), IsURepOn (UJset (allPos k)) τ → IsKTypeOf (allPos k) τ (fun a => (ν a : ℝ)) ⊤ → Δ ≠ 0 → (∀ g, ReciprocityTheory.PGsh.IsUpperUnitri g → ReciprocityTheory.PGsh.rowSubst g Δ = Δ) → (∀ d : Fin k → ℂ, ReciprocityTheory.PGsh.rowSubst (Matrix.diagonal d) Δ = (∏ a, d a ^ ν a) • Δ) → ∃ L : H →ₗ[ℂ] MvPolynomial (Fin k × κ) ℂ, (∀ g ∈ UJset (allPos k), ∀ u, L (τ g u) = ReciprocityTheory.PGsh.rowSubst g (L u)) ∧ ∃ v, L v = Δ := by
  intro k κ _ ν H _ _ _ τ Δ hτ hK hΔ hu hd
  let S : Submodule ℂ (MvPolynomial (Fin k × κ) ℂ) := restrictTotalDegree (Fin k × κ) ℂ Δ.totalDegree
  have hfin : FiniteDimensional ℂ S := inferInstanceAs (Module.Finite ℂ (restrictTotalDegree (Fin k × κ) ℂ Δ.totalDegree))
  letI : InnerProductSpace.Core ℂ S := fischerCore S
  letI : NormedAddCommGroup S := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ S := InnerProductSpace.ofCore _
  exact exists_intertwiner_of_embedding k κ ν H τ S S.subtype S.injective_subtype (fun _ _ => rfl)
    (fun g x => ⟨⟨rowSubst g x.1, (mem_restrictTotalDegree _ _ _).mpr
      ((totalDegree_rowSubst_le g x.1).trans ((mem_restrictTotalDegree _ _ _).mp x.2))⟩, rfl⟩)
    ⟨Δ, (mem_restrictTotalDegree _ _ _).mpr le_rfl⟩ hτ hK hΔ hu hd

end GlobalTheory.HighestPolynomial

end
