import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

open NumberField MvPolynomial in

theorem _root_.GlobalTheory.det_span_common_denominator : ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (d : ℕ) (β : Module.Basis (Fin d) F V) (M : Submodule (𝓞 F) V), M.FG → ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ y ∈ Submodule.span (𝓞 F) {y | ∃ w : Fin d → V, (∀ i, w i ∈ M) ∧ y = β.det w}, c • y ∈ (1 : Submodule (𝓞 F) F) := by
  intro F V _ _ _ _ _ _ d β M hM
  obtain ⟨S, hS⟩ := hM
  obtain ⟨c₀, hc₀⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 F))
    (Finset.univ ×ˢ S) (fun p : Fin d × V => β.repr p.2 p.1)
  have hcoord : ∀ x ∈ M, ∀ i, (c₀ : 𝓞 F) • β.repr x i ∈ (1 : Submodule (𝓞 F) F) := by
    intro x hx i
    rw [← hS] at hx
    induction hx using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨r, hr⟩ := hc₀ (i, g) (Finset.mem_product.mpr ⟨Finset.mem_univ _, hg⟩)
      exact Submodule.mem_one.mpr ⟨r, hr⟩
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add, Finsupp.add_apply, smul_add]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      convert Submodule.smul_mem _ a hx using 1
      rw [← algebraMap_smul F a x, map_smul, Finsupp.smul_apply, smul_eq_mul]
      simp only [Algebra.smul_def]
      ring
  refine ⟨(c₀ : 𝓞 F) ^ d, pow_ne_zero _ (nonZeroDivisors.ne_zero c₀.2), ?_⟩
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    choose B hB using fun i j => Submodule.mem_one.mp (hcoord (w j) (hw j) i)
    rw [Submodule.mem_one]
    refine ⟨(Matrix.of B).det, ?_⟩
    have hmat : (algebraMap (𝓞 F) F).mapMatrix (Matrix.of B) =
        algebraMap (𝓞 F) F (c₀ : 𝓞 F) • β.toMatrix w := by
      ext i j
      simp [Module.Basis.toMatrix_apply, hB, Algebra.smul_def]
    rw [RingHom.map_det, hmat, Matrix.det_smul, Fintype.card_fin, Module.Basis.det_apply,
      Algebra.smul_def, map_pow]
  | zero => simp
  | add x y _ _ hx hy =>
    rw [smul_add]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [smul_comm]
    exact Submodule.smul_mem _ a hx
