import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DelSqIrreducibleUnitary
open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.KJInf.VnStable

variable {ι : Type} [Fintype ι] {a : ℕ}

theorem lft_rename (g : ι → Matrix (Fin a) (Fin a) ℂ) (τ : ι) (p : MvPolynomial (Fin a × Fin a) ℂ) :
    lft g (rename (Prod.mk τ) p) = rename (Prod.mk τ) (Formalism.GradedWeylDivisibility.rowAct ℂ (g τ) p) := by
  have : (lft g).comp (rename (Prod.mk τ)) = (rename (Prod.mk τ)).comp (Formalism.GradedWeylDivisibility.rowAct ℂ (n := a) (g τ)) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [lft, Formalism.GradedWeylDivisibility.rowAct, rename_X, aeval_X, map_sum]
  exact congrArg (fun φ : MvPolynomial (Fin a × Fin a) ℂ →ₐ[ℂ] PY ι a => φ p) this

theorem lft_ten (g : ι → Matrix (Fin a) (Fin a) ℂ) (f : ι → MvPolynomial (Fin a × Fin a) ℂ) :
    lft g (ten f) = ten (fun τ => Formalism.GradedWeylDivisibility.rowAct ℂ (g τ) (f τ)) := by
  simp only [ten, map_prod, lft_rename]

theorem lft_frDet (g : ι → Matrix (Fin a) (Fin a) ℂ) (τ : ι) :
    lft g (frDet ℂ a τ : PY ι a) = (g τ).det • (frDet ℂ a τ : PY ι a) := by
  unfold frDet
  rw [AlgHom.map_det]
  have hM : (lft g).mapMatrix (Matrix.of fun α s : Fin a => (X (τ, α, s) : PY ι a)) =
      (g τ).map C * Matrix.of fun α s : Fin a => (X (τ, α, s) : PY ι a) := by
    ext α s
    simp [lft, Matrix.mul_apply]
  rw [hM, Matrix.det_mul, smul_eq_C_mul]
  congr 1
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]

theorem prod_mem_prodS {A : Type} [CommRing A] [Algebra ℂ A] (s : Finset ι) (M : ι → Submodule ℂ A) (x : ι → A)
    (h : ∀ τ ∈ s, x τ ∈ M τ) : ∏ τ ∈ s, x τ ∈ ∏ τ ∈ s, M τ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact Submodule.one_le.mp le_rfl
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact Submodule.mul_mem_mul (h i (Finset.mem_insert_self _ _))
      (ih fun τ hτ => h τ (Finset.mem_insert_of_mem hτ))

theorem fg_prodS {A : Type} [CommRing A] [Algebra ℂ A] (s : Finset ι) (M : ι → Submodule ℂ A)
    (h : ∀ τ, (M τ).FG) : (∏ τ ∈ s, M τ).FG := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  | insert i s hi ih => rw [Finset.prod_insert hi]; exact (h i).mul ih

theorem ten_mem_prod (lam : ι → DomWeight a) (f : ι → MvPolynomial (Fin a × Fin a) ℂ)
    (hf : ∀ τ, f τ ∈ delSq ℂ a (lam τ)) :
    ten f ∈ ∏ τ, (delSq ℂ a (lam τ)).map (rename (Prod.mk τ)).toLinearMap := by
  unfold ten
  exact prod_mem_prodS _ _ _ (fun τ _ => Submodule.mem_map_of_mem (hf τ))

theorem cspan_fd (lam : ι → DomWeight a) : FiniteDimensional ℂ (CSpan lam) := by
  have hP : (∏ τ, (delSq ℂ a (lam τ)).map (rename (Prod.mk τ)).toLinearMap).FG := by
    apply fg_prodS
    intro τ
    apply Submodule.FG.map
    haveI := (GlobalTheory.WeylUnitary.delSq_irreducible_unitary a (lam τ)).1
    exact (Submodule.fg_iff_finiteDimensional _).mpr inferInstance
  have hle : CSpan lam ≤ ∏ τ, (delSq ℂ a (lam τ)).map (rename (Prod.mk τ)).toLinearMap := by
    unfold CSpan
    rw [Submodule.span_le]
    rintro p ⟨f, hf, rfl⟩
    exact ten_mem_prod lam f hf
  haveI : FiniteDimensional ℂ ↥(∏ τ, ((delSq ℂ a (lam τ)).map (rename (Prod.mk τ)).toLinearMap : Submodule ℂ (PY ι a))) :=
    (Submodule.fg_iff_finiteDimensional _).mp hP
  exact Submodule.finiteDimensional_of_le hle

theorem lft_cspan (lam : ι → DomWeight a) (g : ι → Matrix (Fin a) (Fin a) ℂ) :
    ∀ p ∈ CSpan lam, lft g p ∈ CSpan lam := by
  intro p hp
  unfold CSpan at hp ⊢
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    rw [lft_ten]
    exact Submodule.subset_span ⟨_, fun τ => (GlobalTheory.WeylUnitary.delSq_irreducible_unitary a (lam τ)).2.2.1 (g τ) (f τ) (hf τ), rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

end GlobalTheory.KJInf.VnStable

open GlobalTheory.KJInf.VnStable in

theorem GlobalTheory.KJInf.vn_finiteDimensional_and_lft_mem : ∀ (ι : Type) [Fintype ι] (a : ℕ) (lam : ι → DomWeight a) (n : ι → ℕ),
    FiniteDimensional ℂ (Vn lam n) ∧ ∀ (g : ι → Matrix (Fin a) (Fin a) ℂ), ∀ F ∈ Vn lam n, lft g F ∈ Vn lam n := by
  intro ι _ a lam n
  haveI := cspan_fd lam
  refine ⟨?_, ?_⟩
  · unfold Vn; infer_instance
  · intro g F hF
    unfold Vn at hF ⊢
    obtain ⟨p, hp, rfl⟩ := hF
    have hD : lft g (∏ τ, (frDet ℂ a τ : PY ι a) ^ n τ) = C (∏ τ, (g τ).det ^ n τ) * ∏ τ, (frDet ℂ a τ : PY ι a) ^ n τ := by
      rw [map_prod, map_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [map_pow, lft_frDet, smul_eq_C_mul, mul_pow, map_pow]
    refine ⟨(∏ τ, (g τ).det ^ n τ) • lft g p, Submodule.smul_mem _ _ (lft_cspan lam g p hp), ?_⟩
    simp only [LinearMap.mulRight_apply, map_mul, hD, smul_eq_C_mul]; ring
