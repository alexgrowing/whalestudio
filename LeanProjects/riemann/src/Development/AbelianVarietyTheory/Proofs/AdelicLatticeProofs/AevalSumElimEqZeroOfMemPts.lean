import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RatComponentMemRatPolysVanishingOnMatrixSetStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfContractions
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem tensor_eq_zero_of_forall_contract {V W : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup W]
    [Module ℚ W] (t : V ⊗[ℚ] W)
    (h : ∀ m : W →ₗ[ℚ] ℚ, TensorProduct.rid ℚ V (LinearMap.lTensor V m t) = 0) : t = 0 := by
  first
  | exact @_root_.GlobalTheory.CoefficientContraction.eq_zero_of_contractions
  | exact _root_.GlobalTheory.CoefficientContraction.eq_zero_of_contractions
  | (apply _root_.GlobalTheory.CoefficientContraction.eq_zero_of_contractions <;> assumption)
  | (intros; apply _root_.GlobalTheory.CoefficientContraction.eq_zero_of_contractions <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CoefficientContraction.eq_zero_of_contractions <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CoefficientContraction.eq_zero_of_contractions ..)

theorem aeval_sum_elim_eq_zero_of_tensor {ι : Type} [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ))
    (hΓ : ∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ)
    (t : MvPolynomial (ι × ι) ℚ ⊗[ℚ] MvPolynomial (ι × ι) ℚ)
    (ht : ∀ g ∈ Γ, ∀ h ∈ Γ, Algebra.TensorProduct.productMap
      (MvPolynomial.aeval (fun ij : ι × ι => g ij.1 ij.2))
      (MvPolynomial.aeval (fun ij : ι × ι => h ij.1 ij.2)) t = (0 : ℂ))
    (R : Type) [CommRing R] [Algebra ℚ R] (x : Matrix ι ι R) (hx : x ∈ pts Γ R)
    (y : Matrix ι ι R) (hy : y ∈ pts Γ R) :
    Algebra.TensorProduct.productMap
      (MvPolynomial.aeval (fun ij : ι × ι => x ij.1 ij.2))
      (MvPolynomial.aeval (fun ij : ι × ι => y ij.1 ij.2)) t = (0 : R) := by
  set ex : MvPolynomial (ι × ι) ℚ →ₐ[ℚ] R := MvPolynomial.aeval (fun ij : ι × ι => x ij.1 ij.2) with hex
  set ey : MvPolynomial (ι × ι) ℚ →ₐ[ℚ] R := MvPolynomial.aeval (fun ij : ι × ι => y ij.1 ij.2) with hey
  have key : TensorProduct.map ex.toLinearMap ey.toLinearMap t = 0 := by
    apply tensor_eq_zero_of_forall_contract
    intro m
    have h1 : TensorProduct.rid ℚ _ (LinearMap.lTensor _ (m ∘ₗ ey.toLinearMap) t) ∈ vanI Γ := by
      intro g hg
      set eg : MvPolynomial (ι × ι) ℚ →ₐ[ℚ] ℂ := MvPolynomial.aeval (fun ij : ι × ι => g ij.1 ij.2) with heg
      refine (Module.forall_dual_apply_eq_zero_iff ℚ _).1 fun l => ?_
      let φ : MvPolynomial (ι × ι) ℚ ⊗[ℚ] MvPolynomial (ι × ι) ℚ →ₐ[ℚ] MvPolynomial (ι × ι) ℂ :=
        Algebra.TensorProduct.productMap
          (((Algebra.ofId ℂ (MvPolynomial (ι × ι) ℂ)).restrictScalars ℚ).comp eg)
          (MvPolynomial.mapAlgHom (Algebra.ofId ℚ ℂ))
      have h2 : TensorProduct.lid ℚ _ (LinearMap.rTensor _ (l ∘ₗ eg.toLinearMap) t) ∈ vanI Γ := by
        refine GlobalTheory.T.rat_component_mem_ratPolysVanishingOnMatrixSet ι Γ hΓ (φ t) ?_ l _ ?_
        · intro h hh
          rw [← ht g hg h hh]
          clear ht
          induction t using TensorProduct.induction_on with
          | zero => simp [evC]
          | tmul a b =>
            simp [evC, φ, ← heg, MvPolynomial.eval_map, MvPolynomial.aeval_def, Algebra.ofId_apply]
          | add s t hs ht =>
            simp only [evC] at hs ht
            simp only [evC, map_add, hs, ht]
        · intro k
          clear ht
          induction t using TensorProduct.induction_on with
          | zero => simp
          | tmul a b =>
            simp [φ, MvPolynomial.coeff_map, Algebra.ofId_apply]
            rw [mul_comm (eg a), ← eq_ratCast (algebraMap ℚ ℂ), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
          | add s t hs ht => simp only [map_add, MvPolynomial.coeff_add, hs, ht]
      have h3 : ey _ = 0 := hy _ h2
      have h4 := congrArg m h3
      rw [map_zero] at h4
      rw [← h4]
      change l (eg _) = _
      clear ht h2 h3 h4
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [mul_comm]
      | add s t hs ht => simp only [map_add, hs, ht]
    have h5 : ex _ = 0 := hx _ h1
    rw [← h5]
    clear ht h1 h5
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add s t hs ht => simp only [map_add, hs, ht]
  have h6 := congrArg (LinearMap.mul' ℚ R) key
  rw [map_zero] at h6
  rw [← h6]
  clear ht key h6
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add s t hs ht => simp only [map_add, hs, ht]

theorem aeval_sum_elim_eq_zero_of_mem_pts : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) → ∀ F : MvPolynomial ((ι × ι) ⊕ (ι × ι)) ℚ, (∀ g ∈ Γ, ∀ h ∈ Γ, MvPolynomial.aeval (Sum.elim (fun ij : ι × ι => g ij.1 ij.2) (fun ij : ι × ι => h ij.1 ij.2)) F = (0 : ℂ)) → ∀ (R : Type) [CommRing R] [Algebra ℚ R], ∀ x ∈ pts Γ R, ∀ y ∈ pts Γ R, MvPolynomial.aeval (Sum.elim (fun ij : ι × ι => x ij.1 ij.2) (fun ij : ι × ι => y ij.1 ij.2)) F = (0 : R) := by
  intro ι _ _ Γ hΓ F hF R _ _ x hx y hy
  let T : MvPolynomial ((ι × ι) ⊕ (ι × ι)) ℚ →ₐ[ℚ]
      MvPolynomial (ι × ι) ℚ ⊗[ℚ] MvPolynomial (ι × ι) ℚ :=
    MvPolynomial.aeval (Sum.elim (fun ij => MvPolynomial.X ij ⊗ₜ 1) (fun ij => 1 ⊗ₜ MvPolynomial.X ij))
  have hT : ∀ (S : Type) [CommRing S] [Algebra ℚ S] (a b : ι × ι → S),
      Algebra.TensorProduct.productMap (MvPolynomial.aeval a) (MvPolynomial.aeval b) (T F) =
        MvPolynomial.aeval (Sum.elim a b) F := by
    intro S _ _ a b
    have : (Algebra.TensorProduct.productMap (MvPolynomial.aeval a) (MvPolynomial.aeval b)).comp T =
        MvPolynomial.aeval (Sum.elim a b) := by
      ext (i | i) <;> simp [T]
    exact DFunLike.congr_fun this F
  rw [← hT]
  refine aeval_sum_elim_eq_zero_of_tensor Γ hΓ _ (fun g hg h hh => ?_) R x hx y hy
  rw [hT]
  exact hF g hg h hh

end GlobalTheory.ClassFin
