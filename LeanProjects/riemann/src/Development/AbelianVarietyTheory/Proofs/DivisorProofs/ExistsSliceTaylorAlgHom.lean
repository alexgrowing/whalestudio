import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConstantCoeffDpolyOfAdditiveTaylorPts
import Development.AbelianVarietyTheory.Definitions.Divisors.FderivFnCongr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraFormalPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraMulOfProdEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticAtIteratedFDerivSliceAndFderivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorHolomorphicExtOfValuesStatement

set_option autoImplicit false

noncomputable section

open Filter Topology TopologicalSpace GlobalTheory.AnPer TensorProduct

namespace GlobalTheory.AnPer.SliceTaylor

variable {I : Type} [Fintype I] [DecidableEq I] {g : ℕ}

theorem analyticAt_shift (q : (I ⊕ Fin g → ℂ) × (Fin g → ℂ)) :
    AnalyticAt ℂ (fun y : (I ⊕ Fin g → ℂ) × (Fin g → ℂ) ↦
      (((fun i ↦ y.1 (Sum.inl i)), y.2 + fun b ↦ y.1 (Sum.inr b)) : (I → ℂ) × (Fin g → ℂ))) q := by
  have h1 : ∀ j, AnalyticAt ℂ (fun y : (I ⊕ Fin g → ℂ) × (Fin g → ℂ) ↦ y.1 j) q := fun j ↦
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I ⊕ Fin g ↦ ℂ) j).comp
      (ContinuousLinearMap.fst ℂ (I ⊕ Fin g → ℂ) (Fin g → ℂ))).analyticAt q
  refine AnalyticAt.prod (analyticAt_pi_iff.2 fun i ↦ h1 _) ?_
  exact analyticAt_snd.add (analyticAt_pi_iff.2 fun i ↦ h1 _)

theorem analyticAt_joint {W : Opens ((I → ℂ) × (Fin g → ℂ))} (h : Hol W) {w : Fin g → ℂ}
    (hw : ((0 : I → ℂ), w) ∈ W) :
    AnalyticAt ℂ (fun y : (I ⊕ Fin g → ℂ) × (Fin g → ℂ) ↦
      h.fn ((fun i ↦ y.1 (Sum.inl i)), y.2 + fun b ↦ y.1 (Sum.inr b))) (0, w) := by
  refine AnalyticAt.comp_of_eq (h.analytic _ hw) (analyticAt_shift _) ?_
  ext <;> simp

theorem analyticAt_slice {W : Opens ((I → ℂ) × (Fin g → ℂ))} (h : Hol W) {w : Fin g → ℂ}
    (hw : ((0 : I → ℂ), w) ∈ W) :
    AnalyticAt ℂ (fun x : I ⊕ Fin g → ℂ ↦
      h.fn ((fun i ↦ x (Sum.inl i)), w + fun b ↦ x (Sum.inr b))) 0 :=
  AnalyticAt.comp_of_eq (f := fun x : I ⊕ Fin g → ℂ ↦ (x, w)) (analyticAt_joint h hw)
    (analyticAt_id.prod analyticAt_const) rfl

theorem eventually_mem {W : Opens ((I → ℂ) × (Fin g → ℂ))} {w : Fin g → ℂ}
    (hw : ((0 : I → ℂ), w) ∈ W) :
    ∀ᶠ x : I ⊕ Fin g → ℂ in 𝓝 0,
      (((fun i ↦ x (Sum.inl i)), w + fun b ↦ x (Sum.inr b)) : (I → ℂ) × (Fin g → ℂ)) ∈ W := by
  have hc : Continuous (fun x : I ⊕ Fin g → ℂ ↦
      (((fun i ↦ x (Sum.inl i)), w + fun b ↦ x (Sum.inr b)) : (I → ℂ) × (Fin g → ℂ))) := by
    fun_prop
  refine hc.continuousAt.eventually (W.isOpen.mem_nhds ?_)
  have e : (((fun i ↦ (0 : I ⊕ Fin g → ℂ) (Sum.inl i)), w + fun b ↦ (0 : I ⊕ Fin g → ℂ) (Sum.inr b)) :
      (I → ℂ) × (Fin g → ℂ)) = (0, w) := by
    ext <;> simp
  change _ ∈ W
  simp only [e]
  exact hw

end GlobalTheory.AnPer.SliceTaylor

open GlobalTheory.AnPer.SliceTaylor in

theorem GlobalTheory.AnPer.exists_sliceTaylor_algHom : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I ⊕ Fin g → D), (∀ s : Fin (N + 1) → I ⊕ Fin g, ∏ a, t (s a) = 0) → ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (W : Opens ((I → ℂ) × (Fin g → ℂ))) (W₀ : Opens E) (a : E → Fin g → ℂ), AnalyticOnNhd ℂ a W₀ → (∀ p ∈ W₀, ((0 : I → ℂ), a p) ∈ W) → ∃ ρ : Hol W →ₐ[ℂ] D ⊗[ℂ] Hol W₀, ∀ (h : Hol W) (p : E) (hp : p ∈ W₀), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) (ρ h) = GlobalTheory.PeriodFamily.taylor N t (fun x : I ⊕ Fin g → ℂ ↦ h.fn (fun i ↦ x (Sum.inl i), a p + fun b ↦ x (Sum.inr b))) := by
  intro I _ _ g D _ _ N t ht E _ _ _ W W₀ a ha hW
  have key : ∀ h : Hol W, ∃ r : D ⊗[ℂ] Hol W₀, ∀ (p : E) (hp : p ∈ W₀), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) r = GlobalTheory.PeriodFamily.taylor N t (fun x : I ⊕ Fin g → ℂ ↦ h.fn (fun i ↦ x (Sum.inl i), a p + fun b ↦ x (Sum.inr b))) := by
    intro h
    have han : ∀ (k : ℕ) (v : Fin k → (I ⊕ Fin g → ℂ)), AnalyticOnNhd ℂ (fun p ↦ iteratedFDeriv ℂ k
        (fun x : I ⊕ Fin g → ℂ ↦ h.fn (fun i ↦ x (Sum.inl i), a p + fun b ↦ x (Sum.inr b))) 0 v) W₀ :=
      fun k v p hp ↦
        AnalyticAt.comp_of_eq (GlobalTheory.T.analyticAt_iteratedFDeriv_slice_and_fderiv_eq _ (a p) k v (analyticAt_joint h (hW p hp))).1 (ha p hp) rfl
    unfold GlobalTheory.PeriodFamily.taylor
    refine ⟨∑ k ∈ Finset.range (N + 1), ∑ s : Fin k → I ⊕ Fin g,
      ((k.factorial : ℂ)⁻¹ • ∏ b, t (s b)) ⊗ₜ[ℂ] Hol.mk _ (han k fun b ↦ Pi.single (s b) 1), fun p hp ↦ ?_⟩
    simp only [map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun s _ ↦ ?_
    rw [Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, Hol.ev_apply, Hol.fn_mk _ _ hp,
      AlgHom.id_apply, Algebra.ofId_apply, mul_comm, ← Algebra.smul_def, smul_smul, mul_comm]
  choose r hr using key
  obtain ⟨hadd, -, hconst, hcongr, -, -⟩ := GlobalTheory.T.taylorPolynomialEvalAlgebra_formal_properties N t
  have hc : ∀ c : ℂ, r (algebraMap ℂ _ c) = algebraMap ℂ _ c := fun c ↦ by
    refine GlobalTheory.T.tensor_holomorphic_ext_of_values W₀ D _ _ fun p hp ↦ ?_
    rw [hr, AlgHom.commutes, ← hconst c]
    refine hcongr _ _ ?_
    filter_upwards [eventually_mem (hW p hp)] with x hx using Hol.fn_algebraMap c hx
  have hA : ∀ f h : Hol W, r (f + h) = r f + r h := fun f h ↦ by
    refine GlobalTheory.T.tensor_holomorphic_ext_of_values W₀ D _ _ fun p hp ↦ ?_
    rw [map_add, hr, hr, hr, ← hadd _ _ (analyticAt_slice f (hW p hp)) (analyticAt_slice h (hW p hp))]
    refine hcongr _ _ ?_
    filter_upwards [eventually_mem (hW p hp)] with x hx using Hol.fn_add f h hx
  have hM : ∀ f h : Hol W, r (f * h) = r f * r h := fun f h ↦ by
    refine GlobalTheory.T.tensor_holomorphic_ext_of_values W₀ D _ _ fun p hp ↦ ?_
    rw [map_mul, hr, hr, hr,
      ← GlobalTheory.T.taylorPolynomialEvalAlgebra_mul_of_prod_eq_zero N t ht _ _ (analyticAt_slice f (hW p hp)) (analyticAt_slice h (hW p hp))]
    refine hcongr _ _ ?_
    filter_upwards [eventually_mem (hW p hp)] with x hx using Hol.fn_mul f h hx
  exact ⟨{ toFun := r
           map_one' := by simpa only [map_one] using hc 1
           map_mul' := hM
           map_zero' := by simpa using hc 0
           map_add' := hA
           commutes' := hc }, hr⟩
