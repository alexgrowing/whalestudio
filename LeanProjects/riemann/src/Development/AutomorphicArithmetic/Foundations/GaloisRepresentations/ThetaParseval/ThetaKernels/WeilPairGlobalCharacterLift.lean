import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilDatumDoubleSpaceActsUnitScalarSeesawCM
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.IsStdCharFOfIsGoodK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.IsThetaFunOFHeisOFK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RationalLatticeSelfDual

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix ComplexConjugate Pointwise
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace PositivityTheory.ThKW.DblSchur
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.DblTargetDelta PositivityTheory.ThKW.Dbl GlobalTheory.ThetaSchurF
open GlobalTheory.WeilSchrodinger.DblTargetF (dblG)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {nS nT : ℕ}
variable {σ : E →ₐ[F] E} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
end PositivityTheory.ThKW.DblSchur
open PositivityTheory.ThKW.DblSchur PositivityTheory.ThKW.Dbl Formalism.IndefR.DatumF MeasureTheory GlobalTheory.DblTargetDelta in
theorem PositivityTheory.ThKW.weil_pair_global_character_lift : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle)
        (ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ)),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
      ∀ ωd : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
          Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS (nT + nT) → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
          (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ (h : Formalism.IndefR.DatumF.GAF σ JT) (hd : Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)),
        Formalism.IndefR.DatumF.mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) hd =
          Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.IndefR.DatumF.mtF σ JT h) 0 0 1) →
      ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ f₁ f₂ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ,
        Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₁ → Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₂ →
        ωd (1, hd) (GlobalTheory.DblTargetDelta.deltaT f₁ f₂) = c • GlobalTheory.DblTargetDelta.deltaT (ω (1, h) f₁) f₂ := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ χS χT ω hω ωd hωd h hd e
  have hψ : IsCharAF F B.ψ := (_root_.GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k F E σ B hB).1
  have hinv : ∀ e, σ (σ e) = e := fun e => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star]
  have hT' := GlobalTheory.WeilSchrodinger.DblTargetF.isHermND_dblG hT
  have hth := fun w f hf => _root_.GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k F E σ B hB nS nT JS JT ξ₀ w f hf
  obtain ⟨μ, 𝓕, μ₂, 𝓕₂, hμ, h𝓕, hμ₂, h𝓕₂, hprod⟩ := exists_prod_domain F E nS nT
  let T := {f // IsThetaFunOF σ JS JT ξ₀ B.ψ f}
  have hδ : ∀ f₁ f₂ g₁ g₂ : WOF F E nS nT → ℂ, ∫ x in 𝓕₂, deltaT f₁ f₂ x * star (deltaT g₁ g₂ x) ∂μ₂ =
      (∫ x in 𝓕, f₁ x * star (g₁ x) ∂μ) * ∫ x in 𝓕, conj (f₂ (-x)) * star (conj (g₂ (-x))) ∂μ := fun f₁ f₂ g₁ g₂ => by
    rw [← hprod]
    congr 1
    funext x
    simp only [deltaT_apply, star_mul']
    ring
  obtain ⟨c, hc, H⟩ := abstract hψ (GlobalTheory.T.adelicSymplecticTraceForm_alternating_swap F E σ hinv _ _ JS _ hS hT' ξ₀ hσξ)
    (_root_.GlobalTheory.T.rational_lattice_self_dual F E σ B hB _ _ JS _ hS hT' ξ₀ hξ)
    (fun p : T × T => ωd (1, hd) (deltaT p.1.1 p.2.1)) (fun p => deltaT (ω (1, h) p.1.1) p.2.1)
    (fun p => hωd.om_pres _ _ (theta_delta hψ.2.1 p.1.2 p.2.2))
    (fun p => theta_delta hψ.2.1 (hω.om_pres _ _ p.1.2) p.2.2)
    (fun w p => by
      have e1 : actOF σ JS JT 1 h (actOF σ JS JT 1 h⁻¹ (topR w)) = topR w := by
        rw [← GlobalTheory.WeilPartsF.actOF_mul, mul_one, mul_inv_cancel, act_one_left, show mtF σ JT 1 = 1 from rfl, Matrix.one_mul]
      have e2 : actOF σ JS _ 1 hd (glue (actOF σ JS JT 1 h⁻¹ (topR w)) (botR w)) = w := by
        rw [act_glue h hd e, e1]
        exact tb_ext (top_glue _ _) (bot_glue _ _)
      refine ⟨(⟨_, hth (actOF σ JS JT 1 h⁻¹ (topR w)) _ p.1.2⟩, ⟨_, hth (-botR w) _ p.2.2⟩), ?_, ?_⟩
      · have := hωd.om_heis 1 hd (glue (actOF σ JS JT 1 h⁻¹ (topR w)) (botR w)) _ (theta_delta hψ.2.1 p.1.2 p.2.2)
        rw [e2, heis_delta hψ.2.1, top_glue, bot_glue] at this
        exact this.symm
      · have := hω.om_heis 1 h (actOF σ JS JT 1 h⁻¹ (topR w)) _ p.1.2
        rw [e1] at this
        show _ = deltaT (ω (1, h) _) _
        rw [this, heis_delta hψ.2.1])
    μ₂ 𝓕₂ hμ₂ h𝓕₂ (fun p q => by
      rw [GlobalTheory.ThetaSchurF.scalar_eq hψ.2.1 μ₂ 𝓕₂ hμ₂ h𝓕₂ (ωd (1, hd)) (hωd.om_pres _) (hωd.om_unit μ₂ 𝓕₂ hμ₂ h𝓕₂ _) _ _
        (theta_delta hψ.2.1 p.1.2 p.2.2) (theta_delta hψ.2.1 q.1.2 q.2.2), hδ, hδ,
        GlobalTheory.ThetaSchurF.scalar_eq hψ.2.1 μ 𝓕 hμ h𝓕 (ω (1, h)) (hω.om_pres _) (hω.om_unit μ 𝓕 hμ h𝓕 _) _ _ p.1.2 q.1.2])
  exact ⟨c, hc, fun f₁ f₂ h₁ h₂ => H (⟨f₁, h₁⟩, ⟨f₂, h₂⟩)⟩
end
end
