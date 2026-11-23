import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockSubstitutionIdentitiesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeylDeterminantTwistTensorFiniteDimensionalStablStatement
open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KJInf

def evalLin {ι : Type} {a : ℕ} (y : ι → Matrix (Fin a) (Fin a) ℂ) : PY ι a →ₗ[ℂ] ℂ where
  toFun := evalAt y
  map_add' F G := by simp [evalAt]
  map_smul' c F := by simp [evalAt, MvPolynomial.smul_eval]

theorem evalLin_apply {ι : Type} {a : ℕ} (y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a) :
    evalLin y F = evalAt y F := rfl

theorem exists_evalAt_span (ι : Type) [Fintype ι] (a : ℕ) (lam : ι → DomWeight a) (n : ι → ℕ)
    (W : Type) [AddCommGroup W] [Module ℂ W] (T : PY ι a →ₗ[ℂ] W) :
    ∃ (m : ℕ) (y : Fin m → ι → Matrix (Fin a) (Fin a) ℂ) (P : Fin m → W),
      (∀ j, IsInv (y j)) ∧ ∀ F ∈ Vn lam n, T F = ∑ j, evalAt (y j) F • P j := by
  classical
  set V := Vn lam n with hV
  haveI : FiniteDimensional ℂ V := (GlobalTheory.T.weylDeterminantTwistTensor_finiteDimensional_stable ι a lam n).1
  have hsep : ∀ F : PY ι a, (∀ y, IsInv y → evalAt y F = 0) → F = 0 :=
    (GlobalTheory.T.fockSubstitution_identities ι a a le_rfl).2.2.2.2.2.2.1
  let S : Set (Module.Dual ℂ V) :=
    {φ | ∃ y : ι → Matrix (Fin a) (Fin a) ℂ, IsInv y ∧ φ = (evalLin y).comp V.subtype}
  obtain ⟨f, hfS, hspan, -⟩ := Submodule.exists_fun_fin_finrank_span_eq ℂ S
  choose y hy hfy using hfS
  let Φ := LinearMap.pi f
  have hinj : LinearMap.ker Φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro F hF
    have h0 : ∀ φ ∈ Submodule.span ℂ S, φ F = 0 := by
      intro φ hφ
      rw [← hspan] at hφ
      induction hφ using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨j, rfl⟩ := hx
        exact congrFun hF j
      | zero => simp
      | add x z _ _ hx hz => simp [hx, hz]
      | smul c x _ hx => simp [hx]
    have hF0 : (F : PY ι a) = 0 := by
      apply hsep
      intro z hz
      have := h0 ((evalLin z).comp V.subtype) (Submodule.subset_span ⟨z, hz, rfl⟩)
      simpa [evalLin_apply] using this
    exact Subtype.ext hF0
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective Φ hinj
  refine ⟨_, y, fun j => T (L (Pi.single j 1) : PY ι a), hy, ?_⟩
  intro F hF
  have hΦ : Φ ⟨F, hF⟩ = ∑ j, evalAt (y j) F • (Pi.single j 1 : Fin _ → ℂ) := by
    ext i
    simp only [Φ, LinearMap.pi_apply, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [hfy i]
    rfl
  have key : (⟨F, hF⟩ : V) = L (Φ ⟨F, hF⟩) := by
    rw [← LinearMap.comp_apply, hL]; rfl
  calc T F = T ((⟨F, hF⟩ : V) : PY ι a) := rfl
    _ = T ((L (Φ ⟨F, hF⟩) : V) : PY ι a) := by rw [← key]
    _ = ∑ j, evalAt (y j) F • T (L (Pi.single j 1) : PY ι a) := by
      rw [hΦ, map_sum]
      simp [map_smul, Submodule.coe_sum, Submodule.coe_smul]

end GlobalTheory.KJInf
