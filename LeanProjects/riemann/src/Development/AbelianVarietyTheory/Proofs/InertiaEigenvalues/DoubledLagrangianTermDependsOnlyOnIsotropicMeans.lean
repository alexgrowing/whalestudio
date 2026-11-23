import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntegrandPeriodic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedFrameOfIsotropicColumnsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralFundamentalDomainEqIteratedRationalSplitStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section
namespace GlobalTheory.LagMeans

set_option maxHeartbeats 400000 in

theorem lagTerm_eq_of_means : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V W : HSp D) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 → ∀ (Y : Lag W) (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), IsLagFrame W Y C → ∀ (s : ℕ) (I : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W I → Submodule.span D.host.E (Set.range I.transpose) = Y.1.comap (LinearMap.inl D.host.E _ _) → ∀ (ν : Measure (Mx D s V.rank)) (𝓨 : Set (Mx D s V.rank)), IsCovolOne (GlobalTheory.MixModel.ratMx D s V.rank) ν 𝓨 → ∀ f₁ f₁' f₂ : WO V W → ℂ, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₁' → IsThetaFunO ψ V W f₂ → (∀ x : WO V W, HMul.hMul ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) I * W.gram).map (incA D)) x = (0 : Mx D s V.rank) → ∫ y in 𝓨, f₁ (HMul.hMul (I.map (incA D)) y + x) ∂ν = ∫ y in 𝓨, f₁' (HMul.hMul (I.map (incA D)) y + x) ∂ν) → lagTerm μ 𝓕 C f₁ f₂ = lagTerm μ 𝓕 C f₁' f₂ := by
  intro D ψ hψ V W μ 𝓕 hμ Y C hC s I hI hspan ν 𝓨 hν f₁ f₁' f₂ h₁ h₁' h₂ hmean
  have hmem : ∀ j, ((fun a => I a j), (0 : Fin W.rank → D.host.E)) ∈ Y.1 := fun j => by
    have : (fun a => I a j) ∈ Y.1.comap (LinearMap.inl D.host.E _ _) := hspan ▸ Submodule.subset_span ⟨j, rfl⟩
    exact this
  have mcol : ∀ k, ((fun a => C.1 a k), (fun a => C.2 a k)) ∈ Y.1 := fun k => hC ▸ Submodule.subset_span ⟨k, rfl⟩
  obtain ⟨t, J, K, L, M, e1, e2, e3, e4, e5, e6, e7⟩ := GlobalTheory.T.exists_adapted_frame_of_isotropic_columns' D.host.E W.rank Y.1 Y.2.1 C hC s I hI.2.1 hmem
  obtain ⟨η, 𝓥, hη⟩ := GlobalTheory.MixModel.exists_isCovolOne D t V.rank
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.integral_fundamentalDomain_eq_iterated_rationalSplitting D W.rank V.rank s t J K L M e3 e4 e5 e6 e7 μ 𝓕 hμ ν 𝓨 hν η 𝓥 hη
  have hB : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) I * W.gram * C.1 = 0 := by
    rw [Matrix.mul_assoc]
    funext j k
    have := Y.2.2 _ (hmem j) _ (mcol k)
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Pi.zero_apply, star_zero, zero_mul, Finset.sum_const_zero] at this
    simpa only [Matrix.mul_apply, GlobalTheory.MixModel.cT_sig, Matrix.conjTranspose_apply, Matrix.zero_apply] using this
  have hψ' : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  have per : ∀ f, IsThetaFunO ψ V W f → ∀ γ ∈ GlobalTheory.MixModel.ratMx D W.rank V.rank, ∀ u : Mx D W.rank V.rank,
      f (ratMul C.1 (γ + u)) * star (f₂ (ratMul C.2 (γ + u))) = f (ratMul C.1 u) * star (f₂ (ratMul C.2 u)) := by
    rintro f hf _ ⟨γ, rfl⟩ u
    exact GlobalTheory.RawLift.Model.integrand_periodic hψ' hC hf h₂ γ u
  have cont : ∀ f, IsThetaFunO ψ V W f → Continuous fun u : Mx D W.rank V.rank => f (ratMul C.1 u) * star (f₂ (ratMul C.2 u)) :=
    fun f hf => (hf.cont.comp (continuous_const.matrix_mul continuous_id)).mul
      (continuous_star.comp (h₂.cont.comp (continuous_const.matrix_mul continuous_id)))
  unfold lagTerm
  rw [hκ _ (cont f₁ h₁) (per f₁ h₁), hκ _ (cont f₁' h₁') (per f₁' h₁')]
  congr 1
  congr 1
  funext v
  have r1 : ∀ y : Mx D s V.rank, ratMul C.1 (HMul.hMul (J.map (incA D)) y + HMul.hMul (K.map (incA D)) v) =
      HMul.hMul (I.map (incA D)) y + HMul.hMul ((C.1 * K).map (incA D)) v := fun y => by
    unfold ratMul
    rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul, e1]
  have r2 : ∀ y : Mx D s V.rank, ratMul C.2 (HMul.hMul (J.map (incA D)) y + HMul.hMul (K.map (incA D)) v) =
      HMul.hMul ((C.2 * K).map (incA D)) v := fun y => by
    unfold ratMul
    rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul, e2,
      Matrix.map_zero (incA D) (map_zero (incA D))]
    simp only [Matrix.zero_mul, zero_add]
  simp only [r1, r2]
  rw [integral_mul_const, integral_mul_const]
  congr 1
  refine hmean _ ?_
  rw [← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.mul_assoc, hB, Matrix.zero_mul, Matrix.map_zero (incA D) (map_zero (incA D))]
  exact Matrix.zero_mul _

end GlobalTheory.LagMeans
end
