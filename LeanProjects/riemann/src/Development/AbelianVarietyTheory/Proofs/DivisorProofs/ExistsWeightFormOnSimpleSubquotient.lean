import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDualWeylWeightProjector
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HighWtEmb

theorem exists_prodProj (O : Type) [CommRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ)
    (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm] (w : ι → Fin N → ℕ) (z₀ : Gm)
    (hz : ∀ τ (a : alg O N lam), IsProj O N lam τ (w τ) a → a • z₀ = z₀) (s : Finset ι) :
    ∃ e : alg O N lam, e • z₀ = z₀ ∧ ∀ x : ∀ τ, dualWeyl O N N (res N (lam τ)),
      (e : Module.End O (NablaT O N lam)) (PiTensorProduct.tprod O x) =
        PiTensorProduct.tprod O (fun σ => if σ ∈ s then rowProj O N (res N (lam σ)) (w σ) (x σ) else x σ) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_smul _ _, fun x => by simp⟩
  | insert τ s hτ ih =>
    obtain ⟨e, he, hex⟩ := ih
    obtain ⟨p, hp, -⟩ := exists_unique_isProj O N ι lam τ (w τ)
    let pA : alg O N lam := ⟨p, Algebra.subset_adjoin (Or.inr ⟨τ, w τ, hp⟩)⟩
    refine ⟨pA * e, by rw [mul_smul, he]; exact hz τ pA hp, fun x => ?_⟩
    show p ((e : Module.End O (NablaT O N lam)) _) = _
    rw [hex]
    rw [hp _ (rowProj O N (res N (lam τ)) (w τ) (x τ)) (by simp [hτ, rowProj])]
    congr 1
    funext σ
    by_cases h : σ = τ
    · subst h; simp
    · simp [Function.update_of_ne h, h]

theorem prodProj_mul_eq_zero (O : Type) [CommRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ)
    (w : ι → Fin N → ℕ) (e : Module.End O (NablaT O N lam))
    (he : ∀ x : ∀ τ, dualWeyl O N N (res N (lam τ)),
      e (PiTensorProduct.tprod O x) = PiTensorProduct.tprod O (fun σ => rowProj O N (res N (lam σ)) (w σ) (x σ)))
    (τ : ι) (v : Fin N → ℕ) (a : Module.End O (NablaT O N lam)) (ha : IsProj O N lam τ v a) (hv : v ≠ w τ) : e * a = 0 := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp only [LinearMap.compMultilinearMap_apply, Module.End.mul_apply, LinearMap.zero_apply]
  rw [ha x (rowProj O N (res N (lam τ)) v (x τ)) (by simp [rowProj]), he]
  refine (PiTensorProduct.tprod O).map_coord_zero τ ?_
  simp only [Function.update_self]
  apply Subtype.ext
  simp only [rowProj, LinearMap.restrict_apply, ZeroMemClass.coe_zero]
  rw [weightedHomogeneousComponent_of_mem (weightedHomogeneousComponent_isWeightedHomogeneous _ _), if_neg hv.symm]

set_option synthInstance.maxHeartbeats 400000 in

theorem exists_weightForm : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (ϖ : O), Irreducible ϖ → ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm], SubQ O N lam ϖ Gm → ∀ (w : ι → Fin N → ℕ) (z₀ : Gm), z₀ ≠ 0 → (∀ τ (a : alg O N lam), IsProj O N lam τ (w τ) a → a • z₀ = z₀) → ∃ φ : Gm →+ O ⧸ Ideal.span {ϖ}, φ z₀ ≠ 0 ∧ (∀ (c : O) (z : Gm), φ (algebraMap O (alg O N lam) c • z) = Ideal.Quotient.mk (Ideal.span {ϖ}) c * φ z) ∧ ∀ τ (v : Fin N → ℕ) (a : alg O N lam), IsProj O N lam τ v a → v ≠ w τ → ∀ z, φ (a • z) = 0 := by
  intro O _ _ _ N ι _ _ lam ϖ hϖ Gm _ _ hSQ w z₀ hz0 hfix

  have hkill : ∀ z : Gm, algebraMap O (alg O N lam) ϖ • z = 0 := by
    obtain ⟨U, π, hπ, h0⟩ := hSQ
    intro z
    obtain ⟨x, rfl⟩ := hπ z
    rw [← map_smul]
    exact h0 _ x rfl
  letI iO : Module O Gm := Module.compHom Gm (algebraMap O (alg O N lam))
  have hT : Module.IsTorsionBySet O Gm (Ideal.span {ϖ} : Ideal O) :=
    (Module.isTorsionBySet_span_singleton_iff ϖ).2 fun z => hkill z
  haveI hmax : (Ideal.span {ϖ} : Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  letI kF : Field (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _
  letI iK : Module (O ⧸ Ideal.span {ϖ}) Gm := hT.module
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero (O ⧸ Ideal.span {ϖ}) hz0
  obtain ⟨e, he, hex⟩ := exists_prodProj O N ι lam Gm w z₀ hfix Finset.univ
  let φ : Gm →+ O ⧸ Ideal.span {ϖ} :=
    { toFun := fun z => f (e • z)
      map_zero' := by simp
      map_add' := fun y z => by simp [smul_add] }
  refine ⟨φ, ?_, fun c z => ?_, fun τ v a ha hv z => ?_⟩
  · show f (e • z₀) ≠ 0
    rw [he]; exact hf
  · show f (e • (algebraMap O (alg O N lam) c • z)) = _ * f (e • z)
    rw [← mul_smul, ← Algebra.commutes, mul_smul]
    have : algebraMap O (alg O N lam) c • (e • z) = (Ideal.Quotient.mk (Ideal.span {ϖ}) c) • (e • z) := rfl
    rw [this, map_smul, smul_eq_mul]
  · show f (e • (a • z)) = 0
    have h0 : e * a = 0 := by
      apply Subtype.ext
      exact prodProj_mul_eq_zero O N ι lam w (e : Module.End O (NablaT O N lam))
        (fun x => by rw [hex]; simp) τ v a ha hv
    rw [← mul_smul, h0, zero_smul, map_zero]

end GlobalTheory.HighWtEmb
