import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPlanePairConverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairRestrictsToAdaptedPlaneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairAdaptedPlaneSecondFormStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.NwInvTerm

theorem integral_term_invariant : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (d₂ : ℕ) (H : Plane E n d₂), (d₂ + 2 = n ∧ form σ X.J H.x H.x = 0 ∧ form σ X.J H.y H.y = 0 ∧ form σ X.J H.x H.y = 1 ∧
        (∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
    ∀ (V₁ : Spc F E d₂) (M₁ : Model σ V₁ W) (e : Fn F n d →ₗ[ℂ] Fn F d₂ d),
      V₁.J = H.ιᵀ * X.J * H.ι.map σ → M₁.IsGood B.ψ → IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
    ∀ (μ : Measure (unip σ X H)) (𝓕 : Set (unip σ X H)), μ.IsHaarMeasure →
      IsFundamentalDomain ((ratU σ X.J).subgroupOf (unip σ X H)) 𝓕 μ → μ 𝓕 = 1 →
    ∀ Ψ ∈ schA F (Fin n × Fin d), ∀ u' ∈ unip σ W H',
      ∫ u in 𝓕, thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F H'.x)) (om (u.1, 1) (om (1, u') Ψ)))) ∂μ = ∫ u in 𝓕, thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F H'.x)) (om (u.1, 1) Ψ))) ∂μ := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV₁ hM₁ he μ 𝓕 hμ h𝓕 h1 Ψ hΨ u' hu'
  have hspl := IsUWeilPair.isUSplitting hP.weil
  have hpres : ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ ∈ schA F (Fin n × Fin d) := fun x Φ hΦ => hspl.pres x Φ hΦ
  have hfix : mat u' *ᵥ incV F H'.x = incV F H'.x := by
    rw [GlobalTheory.UnipCT.unip_eq] at hu'
    exact hu'.1
  have hcomm : ∀ Φ ∈ schA F (Fin n × Fin d),
      M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F H'.x)) (om (1, u') Φ) =
        om (1, u') (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F H'.x)) Φ) := by
    intro Φ hΦ
    rw [hspl.impl (1, u') _ Φ hΦ]
    congr 2
    have h2 : ((((1, u') : UA σ X.J × UA σ W.J).2 : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) = mat u' := rfl
    have h1' : ((((1, u') : UA σ X.J × UA σ W.J).1 : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) = 1 := rfl
    show _ = ((((1, u') : UA σ X.J × UA σ W.J).1 : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) * _ *
      ((((1, u') : UA σ X.J × UA σ W.J).2 : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E))ᵀ
    rw [h1', h2, Matrix.one_mul, Matrix.vecMulVec_mul, Matrix.vecMul_transpose, hfix]
  have hA := GlobalTheory.T.pair_restricts_to_adapted_plane hKP F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV₁ hM₁ he
  choose vf hvf using fun u : unip σ X H => hA u.1 u.2
  have hρ : M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F H'.x)) Ψ ∈ schA F (Fin n × Fin d) :=
    GlobalTheory.EvZeroUniq.schr_mem_schA _ hP.base.std _ hΨ
  have hB := GlobalTheory.T.pair_adapted_plane_second_form hKP F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV₁ hM₁ he μ 𝓕 hμ h𝓕 h1
    vf (fun u => (hvf u).1) _ hρ u' hu'
  calc _ = ∫ u in 𝓕, thetaSum F (M₁.co.rho B.ψ (Matrix.vecMulVec (vf u) (incV F H'.x))
          (e (om (1, u') (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F H'.x)) Ψ)))) ∂μ := by
        congr 1
        funext u
        rw [(hvf u).2 _ (hpres _ _ hΨ), hcomm Ψ hΨ]
    _ = _ := hB
    _ = _ := by
        congr 1
        funext u
        rw [(hvf u).2 _ hΨ]

end GlobalTheory.NwInvTerm

end
