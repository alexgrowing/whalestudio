import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.SwapLaws
import Formalism.GelfandTransference.HadamardGelfand.Highest
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallyLineUnit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousCoeffRowAct

noncomputable section

open Matrix Filter Topology
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.RmHol
open PositivityTheory.RgTw (Mat)

namespace GlobalTheory.CompanionTheory.RmHol

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem differentiable_entry {r : ℕ} (a b : Fin r) :
    Differentiable ℂ fun M : Matrix (Fin r) (Fin r) ℂ => M a b :=
  (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ a b)).differentiable

theorem differentiable_det {r : ℕ} :
    Differentiable ℂ fun M : Matrix (Fin r) (Fin r) ℂ => M.det := by
  simp only [Matrix.det_apply']
  refine Differentiable.fun_sum fun σ _ => Differentiable.const_mul ?_ _
  have h : ∀ t : Finset (Fin r), Differentiable ℂ fun M : Matrix (Fin r) (Fin r) ℂ => ∏ i ∈ t, M (σ i) i := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      simp only [Finset.prod_insert ha]
      exact (differentiable_entry (σ a) a).mul ih
  exact h Finset.univ

theorem differentiable_coeff_rowAct {r m : ℕ} (f : MvPolynomial (Fin r × Fin m) ℂ) :
    ∀ s : (Fin r × Fin m) →₀ ℕ, Differentiable ℂ fun M : Matrix (Fin r) (Fin r) ℂ =>
      MvPolynomial.coeff s (Formalism.GradedWeylDivisibility.rowAct ℂ (n := m) Mᵀ f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    intro s
    simpa [MvPolynomial.algebraMap_eq] using
      (differentiable_const (MvPolynomial.coeff s (MvPolynomial.C a : MvPolynomial (Fin r × Fin m) ℂ)) :
        Differentiable ℂ fun _ : Matrix (Fin r) (Fin r) ℂ => _)
  | add p q hp hq =>
    intro s
    simp only [map_add, MvPolynomial.coeff_add]
    exact (hp s).add (hq s)
  | mul_X p v hp =>
    intro s
    have key : ∀ M : Matrix (Fin r) (Fin r) ℂ,
        MvPolynomial.coeff s (Formalism.GradedWeylDivisibility.rowAct ℂ (n := m) Mᵀ (p * MvPolynomial.X v)) =
        ∑ b : Fin r, M b v.1 * (if (b, v.2) ∈ s.support then
          MvPolynomial.coeff (s - Finsupp.single (b, v.2) 1) (Formalism.GradedWeylDivisibility.rowAct ℂ (n := m) Mᵀ p) else 0) := by
      intro M
      have hX : Formalism.GradedWeylDivisibility.rowAct ℂ (n := m) Mᵀ (MvPolynomial.X v) =
          ∑ b : Fin r, MvPolynomial.C (M b v.1) * MvPolynomial.X (b, v.2) := by
        simp [Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.aeval_X]
      rw [map_mul, hX, Finset.mul_sum, MvPolynomial.coeff_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [mul_left_comm, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_mul_X']
    simp only [key]
    refine Differentiable.fun_sum fun b _ => ?_
    refine (differentiable_entry b v.1).mul ?_
    split_ifs
    · exact hp _
    · exact differentiable_const _

theorem detPow_nonsingInvUnit {n : ℕ} {x : Mat n} (h : IsUnit x.det) (c : ℤ) :
    Formalism.BasicNotions.detPow ℂ n (Matrix.nonsingInvUnit x h) c = x.det ^ c := by
  have e : ((Matrix.GeneralLinearGroup.det (Matrix.nonsingInvUnit x h) : ℂˣ) : ℂ) = x.det := rfl
  rw [Formalism.BasicNotions.detPow, Units.val_zpow_eq_zpow_val, e]

theorem holRm (n : ℕ) (lam : Fin n → ℤ) : HolRm lam := by
  intro i j g hg
  obtain ⟨S, c, hc⟩ := GlobalTheory.CompanionTheory.WInfCont.exists_finset_factor (Formalism.BasicNotions.nablaSq ℂ n (dw lam)) ((wb lam).coord i)
  have hev : (fun x : Mat n => Rm lam x i j) =ᶠ[𝓝 g] fun x : Mat n =>
      ∑ s : S, c s * (x.det ^ (dw lam).detShift *
        MvPolynomial.coeff s.1 (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) xᵀ (wb lam j).1)) := by
    filter_upwards [isOpen_GLs.mem_nhds hg] with x hx
    have hu := isUnit_det_of_mem hx
    rw [Rm_of_unit lam hu, LinearMap.toMatrix_apply, ← Module.Basis.coord_apply, hc]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [GlobalTheory.Branching.sqRep_coe, Formalism.BasicNotions.sqAct, MvPolynomial.coeff_smul, smul_eq_mul,
      detPow_nonsingInvUnit hu]
    rfl
  refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
  refine DifferentiableAt.fun_sum fun s _ => DifferentiableAt.const_mul ?_ _
  refine DifferentiableAt.mul ?_ (differentiable_coeff_rowAct _ _ _)
  exact (differentiable_det g).zpow (Or.inl hg)

end GlobalTheory.CompanionTheory.RmHol
