import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTriplePolynomialFockStableMulTraceLinear
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TracePairingArchimedeanVarsNondegenerateRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroGaussianVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianPolynomialMultiplesDenseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianRealLiftExpansionStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

open scoped Classical

namespace GlobalTheory.PolDenseGood

theorem dense_pol_of_isPair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → Dense (M.Pol B.ψ B.emb : Set (SInf F (Fin n × Fin d))) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  obtain ⟨f₀, hf₀, hG⟩ := GlobalTheory.T.exists_nonzero_gaussian_vector F E σ B n d r s r' s' X W M hP.base hP.herm hP.skew GlobalTheory.T.archHeisenbergDerivatives_exist
    GlobalTheory.RealLift.actsLaws
  have hmem : f₀ ∈ M.Pol B.ψ B.emb := by
    rw [Model.Pol, Submodule.mem_sInf]
    exact fun N hN => hN.1 f₀ hG
  obtain ⟨Q, z, hQ, hz⟩ :=
    GlobalTheory.T.gaussian_real_lift_expansion F E σ B n d X W M χX χW om r s r' s' hP GlobalTheory.T.archHeisenbergDerivatives_exist GlobalTheory.RealLift.actsLaws f₀ hf₀ hG
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hf₀ (SchwartzMap.ext fun x => by simp [hz x])
  refine GlobalTheory.T.gaussian_polynomial_multiples_dense _ Q hQ (z⁻¹ • f₀) (fun x => ?_) _ (Submodule.smul_mem _ _ hmem) fun f hf ℓ => ?_
  · rw [SchwartzMap.smul_apply, hz x, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hz0, one_mul]
  have hinj : Function.Injective (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)).flip := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro q hq
    exact GlobalTheory.GaussLine.pairInf_nondeg F _ q fun x => by
      simpa using LinearMap.congr_fun hq x
  have hsurj : Function.Surjective (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)).flip :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank Subspace.dual_finrank_eq.symm).1 hinj
  obtain ⟨q, rfl⟩ := hsurj ℓ
  obtain ⟨f₁, h1, h2⟩ := GlobalTheory.PolMul.model_mul M B.ψ hP.base.std B.emb q f hf
  exact ⟨f₁, h1, fun x => by rw [h2 x]; rfl⟩

end GlobalTheory.PolDenseGood
