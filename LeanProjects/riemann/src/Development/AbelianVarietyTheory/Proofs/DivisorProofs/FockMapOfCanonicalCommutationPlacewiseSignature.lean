import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FramedDConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockMapOfCanonicalCommutationRelations
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutingOperatorsPolynomialEvalPderiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfMapPderivEqAndMapOneNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHeisenbergOperatorOfCoordsEqSumMulLeftPderiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PderivProdRenameSigmaOfNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineSignMulSelf
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

noncomputable section

namespace GlobalTheory.CCRFock
open MvPolynomial

theorem atPl_linear_dep {W : Type} [Fintype W] [DecidableEq W] {Λ : W → Type} (w : W) :
    ∃ L : Module.End ℂ (MvPolynomial (Λ w) ℂ) →ₗ[ℂ] Module.End ℂ (⨂[ℂ] v : W, MvPolynomial (Λ v) ℂ),
      ∀ A, L A = GlobalTheory.RealLift.atPl (V := fun v : W => MvPolynomial (Λ v) ℂ) w A :=
  ⟨{ toFun := fun A => GlobalTheory.RealLift.atPl (V := fun v : W => MvPolynomial (Λ v) ℂ) w A
     map_add' := fun A B => by
       unfold GlobalTheory.RealLift.atPl
       exact PiTensorProduct.map_update_add
         (fun v : W => (LinearMap.id : MvPolynomial (Λ v) ℂ →ₗ[ℂ] MvPolynomial (Λ v) ℂ)) w A B
     map_smul' := fun c A => by
       unfold GlobalTheory.RealLift.atPl
       exact PiTensorProduct.map_update_smul
         (fun v : W => (LinearMap.id : MvPolynomial (Λ v) ℂ →ₗ[ℂ] MvPolynomial (Λ v) ℂ)) w c A }, fun _ => rfl⟩

theorem fock_map_of_ccr_dep : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {W : Type} [Fintype W] [DecidableEq W] {P Q R S : W → ℕ}
    (H : (∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) → Module.End ℂ V),
    (∀ c c', H (c + c') = H c + H c') → (∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c) →
    (∀ c c', H c * H c' - H c' * H c =
      ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1) →
    ∀ f₀ : V, f₀ ≠ 0 →
    (∀ w a b, H (Pi.single w (Matrix.single a b 1)) f₀ +
      (lineSign a b * Complex.I) • H (Pi.single w (Matrix.single a b Complex.I)) f₀ = 0) →
    ∃ Φ : (⨂[ℂ] w : W, Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) →ₗ[ℂ] V, Function.Injective Φ ∧
      ∀ c T, Φ (sumPl (fun w => heisOp (c w)) T) = H c (Φ T) := by
  intro V _ _ W _ _ P Q R S H hadd hsmul hcomm f₀ hf₀ hvac
  obtain ⟨m, D, hm, hdm, hD0, hH⟩ := GlobalTheory.HoweD.ccr_fock_ops_sig H hadd hsmul hcomm
  obtain ⟨θ, hθ, hθ'⟩ := GlobalTheory.CCRFock.exists_polMapD W (fun w => Ix (P w) (Q w) × Ix (R w) (S w))
  have hd0 : ∀ j, D j f₀ = 0 := fun j => hD0 j f₀ (hvac j.1 j.2.1 j.2.2)
  have hD := GlobalTheory.CCRFock.polEval_pderiv m D hm f₀ (fun i j => by convert hdm i j) hd0
  refine ⟨polEval m hm f₀ ∘ₗ θ, ?_, ?_⟩
  · exact (GlobalTheory.FockAlg.injective_of_pderiv (polEval m hm f₀) D hD (by rw [polEval_one]; exact hf₀)).comp hθ
  · intro c T
    rw [hH c, Fintype.sum_sigma]
    simp only [LinearMap.comp_apply, sumPl, LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    obtain ⟨L, hL⟩ := atPl_linear_dep (W := W) (Λ := fun w => Ix (P w) (Q w) × Ix (R w) (S w)) w
    rw [heisOp_eq_sum_mul_pderiv, ← hL, map_sum]
    simp only [LinearMap.sum_apply, map_sum, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
    simp only [hL]
    refine Finset.sum_congr rfl fun l _ => ?_
    obtain ⟨hX, hY⟩ := hθ' w l T
    rw [hX, hY, polEval_X, hD]

end GlobalTheory.CCRFock
