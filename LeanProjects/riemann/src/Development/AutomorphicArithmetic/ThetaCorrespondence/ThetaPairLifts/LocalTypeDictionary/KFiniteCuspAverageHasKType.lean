import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormAvgHasType
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormAvgHasTypeStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.KFinCuspAvgType
open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.TypeSum GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined
variable {n : ℕ}
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool} {σ : Mx n → (H →L[ℂ] H)}
end GlobalTheory.KFinCuspAvgType
end
namespace GlobalTheory.KFinCuspAvgType
open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.TypeSum GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined
theorem kFinite_average_isTypeAt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ N : GlobalTheory.Grid.Node D, N.V.SigOK →
    ∀ (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), Continuous e → GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e →
    ∀ φ : GA D N.V → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ →
    IsTypeAt θ N.V τ (N.S τ) (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) := by
  intro hPr D θ hθ N _ τ e _ he φ hφ
  obtain ⟨H, i1, i2, σ, lam, ε', P, hE, hD, hP, hJ, hx⟩ := hφ.2.2 τ
  obtain ⟨-, hε⟩ := GlobalTheory.SignedParTest.isEnum_unique hE (N.M.enum τ)
  subst hε
  haveI : CompleteSpace H := hD.1
  have hσ : Std (N.M.ε τ) σ := std_of_isDS hPr.harishChandraModules hD
  have hσ1 := hσ.1
  set fr := N.M.fr τ with hfr
  have hf := N.M.fr_unit τ
  have hfJ := N.M.fr_gram τ
  rw [← hfr] at hf hfJ
  have hdP := (isUnit_iff_isUnit_det _).1 hP
  have hdf := (isUnit_iff_isUnit_det _).1 hf
  have hG : IsUnit (gramAt D N.V τ) := isUnit_gram hP hJ
  have hc1 : fr * P⁻¹ ∈ UJset (N.M.ε τ) := mul_inv_mem_UH hP hfJ hJ
  have hc2 : P * fr⁻¹ ∈ UJset (N.M.ε τ) := mul_inv_mem_UH hf hJ hfJ
  have e12 : fr * P⁻¹ * (P * fr⁻¹) = 1 := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hdP, Matrix.mul_nonsing_inv _ hdf]
  have e21 : P * fr⁻¹ * (fr * P⁻¹) = 1 := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hdf, Matrix.mul_nonsing_inv _ hdP]
  have hconj : ∀ {Q : Mx N.V.rank}, IsUnit Q → Qᴴ * Jm (N.M.ε τ) * Q = gramAt D N.V τ →
      ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ), Q * g * Q⁻¹ ∈ UJset (N.M.ε τ) := fun {Q} hQ hQJ g hg =>
    mul_inv_mem_UH hQ (by
      calc (Q * g)ᴴ * Jm (N.M.ε τ) * (Q * g) = gᴴ * (Qᴴ * Jm (N.M.ε τ) * Q) * g := by
            simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = gramAt D N.V τ := by rw [hQJ]; exact hg) hQJ
  refine ⟨H, i1, i2, σ, lam, N.M.ε τ, fr, hE, hD, hf, hfJ, fun x => ?_⟩
  have h1 := hasTypeAll_iff.2 (hx x)
  have h2 := hasTypeAll_transport _ H H (fun g => σ (P * g * P⁻¹)) σ (gramAt D N.V τ) (Jm (N.M.ε τ)) fr hG hf hfJ
    (uIso hσ1 hc1 hc2 e12 e21) (fun g hg v => by
      rw [uIso_apply, uIso_apply, ← sigma_mul hσ1 hc1 (hconj hP hJ g hg), ← sigma_mul hσ1 (hconj hf hfJ g hg) hc1]
      congr 2
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hdP, Matrix.nonsing_inv_mul_cancel_left _ _ hdf]) _ h1
  obtain ⟨S, hS, hc, v, ℓ, C, h⟩ := h2
  have h3 := GlobalTheory.SeriesToClosure.moves_avg hθ hf hfJ hσ he φ x S v ℓ C hS hc h
  have h4 : HasTypeAll (lieSet (N.M.ε τ)) (UJset (N.M.ε τ)) σ
      (GlobalTheory.SeriesToClosure.res θ N.V τ fr (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) x) := ⟨S, hS, hc, _, ℓ, C, h3⟩
  have hfi : IsUnit fr⁻¹ := (isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det _ hdf)
  have hfiJ : (fr⁻¹)ᴴ * gramAt D N.V τ * fr⁻¹ = Jm (N.M.ε τ) := by
    rw [← hfJ]
    calc (fr⁻¹)ᴴ * (frᴴ * Jm (N.M.ε τ) * fr) * fr⁻¹ = (fr * fr⁻¹)ᴴ * Jm (N.M.ε τ) * (fr * fr⁻¹) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [Matrix.mul_nonsing_inv _ hdf]; simp
  have h5 := hasTypeAll_transport _ H H σ (fun g => σ (fr * g * fr⁻¹)) (Jm (N.M.ε τ)) (gramAt D N.V τ) fr⁻¹
    (isUnit_Jm _) hfi hfiJ (LinearIsometryEquiv.refl ℂ H) (fun g _ w => by
      show σ g w = σ (fr * (fr⁻¹ * g * fr⁻¹⁻¹) * fr⁻¹) w
      rw [Matrix.nonsing_inv_nonsing_inv _ hdf]
      simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hdf, Matrix.mul_nonsing_inv _ hdf,
        Matrix.mul_one]) _ h4
  have e5 : (fun y => GlobalTheory.SeriesToClosure.res θ N.V τ fr (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) x (fr⁻¹⁻¹ * y * fr⁻¹)) =
      fun y => GlobalTheory.KFinCuspApprox.avgN θ N τ e φ (x * atTau θ N.V τ y) := funext fun y => by
    rw [Matrix.nonsing_inv_nonsing_inv _ hdf, GlobalTheory.SeriesToClosure.res_conj hf]
  rw [e5] at h5
  exact hasTypeAll_iff.1 h5
end GlobalTheory.KFinCuspAvgType
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kFinite_cusp_average_hasKType : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ N : GlobalTheory.Grid.Node D, N.V.SigOK → ∀ (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), Continuous e → GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e → ∀ φ : GA D N.V → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ → IsTypeAt θ N.V τ (N.S τ) (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) := by
  first | exact @_root_.GlobalTheory.KFinCuspAvgType.kFinite_average_isTypeAt | exact _root_.GlobalTheory.KFinCuspAvgType.kFinite_average_isTypeAt | (intros; apply _root_.GlobalTheory.KFinCuspAvgType.kFinite_average_isTypeAt <;> assumption)
end
