import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MapFinNeg
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsInfFamAndStdChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField

namespace GlobalTheory.Chain.VacVec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

private theorem Jm_mul_Jm_eq_oneFormalDegree {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  by_cases h : ε a <;> simp [h]

private theorem conjTranspose_Jm_eq_Jm {n : ℕ} (ε : Fin n → Bool) :
    Matrix.conjTranspose (Formalism.REAL.Jm ε) = Formalism.REAL.Jm ε := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : ε a <;> simp [h]

private theorem conj_cartan_involution_props {n : ℕ} (F J : Matrix (Fin n) (Fin n) ℂ) (hF : IsUnit F) (hJ : J * J = 1)
    (hJh : Matrix.conjTranspose J = J) :
    F⁻¹ * J * F * (F⁻¹ * J * F) = 1 ∧
      Matrix.conjTranspose (F⁻¹ * J * F) * (Matrix.conjTranspose F * J * F) * (F⁻¹ * J * F) =
        Matrix.conjTranspose F * J * F ∧
      Matrix.conjTranspose F * J * F * (F⁻¹ * J * F) = Matrix.conjTranspose F * F := by
  have hd : IsUnit F.det := (Matrix.isUnit_iff_isUnit_det F).mp hF
  have hdh : IsUnit (Matrix.conjTranspose F).det := by rw [Matrix.det_conjTranspose]; exact hd.star
  have hJJ : ∀ X : Matrix (Fin n) (Fin n) ℂ, J * (J * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]
  refine ⟨?_, ?_, ?_⟩
  · simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd, hJJ]
    exact Matrix.nonsing_inv_mul F hd
  · simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, hJh, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul_cancel_left _ _ hdh, Matrix.mul_nonsing_inv_cancel_left _ _ hd, hJJ]
  · simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd, hJJ]

open Matrix in
open scoped ComplexOrder in

theorem cart_isCartanInv {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    IsCartanInv (gramAt D V τ) (cart M τ) := by
  unfold IsCartanInv cart
  rw [← M.fr_gram τ]
  obtain ⟨h1, h2, h3⟩ := conj_cartan_involution_props _ _ (M.fr_unit τ) (Jm_mul_Jm_eq_oneFormalDegree (M.ε τ)) (conjTranspose_Jm_eq_Jm (M.ε τ))
  refine ⟨h1, h2, ?_⟩
  rw [h3]
  have hinj : Function.Injective (M.fr τ).mulVec := Matrix.mulVec_injective_iff_isUnit.mpr (M.fr_unit τ)
  simpa only [Matrix.mul_one] using Matrix.PosDef.one.conjTranspose_mul_mul_same hinj

private theorem exists_isVacVec_of_isSelfDualC {V W : HSp D} {S S' : D.what₂.Tau → SPar} (ψ : AddChar (AF D.host.F) ℂ)
    (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S') (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E))
    (hL : IsSelfDualC V L) (hL' : IsSelfDualC W L') : ∃ f, IsVacVec ψ θ M M' f := by
  obtain ⟨f, hne, hf⟩ := GlobalTheory.VacuumO.exists_ne_zero ψ θ hψ hθ V W (cart M) (cart M')
    (cart_isCartanInv M) (cart_isCartanInv M') L L' hL hL'
  have hone : (fun w => (1 : ℂ) * f w) = f := funext fun w => one_mul (f w)
  obtain ⟨hth, -, hvac⟩ := hf 1
  rw [hone] at hth hvac
  exact ⟨f, ⟨hth, hne, hvac⟩⟩

theorem exists_isVacVec {V W : HSp D} {S S' : D.what₂.Tau → SPar} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (M : DSModel V S) (M' : DSModel W S') (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) :
    ∃ f, IsVacVec ψ θ M M' f :=
  exists_isVacVec_of_isSelfDualC ψ θ M M' hψ hθ _ _ (GlobalTheory.PlaceModel.isSelfDualC_latFrame V)
    (GlobalTheory.PlaceModel.isSelfDualC_latFrame W)

theorem exists_char_fam_isVacVec {V W : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel W S') :
    ∃ ψ θ f, IsStdChar D ψ (-1) ∧ IsInfFam θ ∧ IsVacVec ψ θ M M' f := by
  obtain ⟨⟨θ, hθ⟩, ψ, hψ⟩ := GlobalTheory.Ker.exists_infFam_and_stdChar D
  obtain ⟨f, hf⟩ := exists_isVacVec ψ θ M M' hψ hθ
  exact ⟨ψ, θ, f, hψ, hθ, hf⟩

end GlobalTheory.Chain.VacVec

end
