import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.DiagonalLagrangianIntegralSiegelParabolicTransfo
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LeviK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.NormLawK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsCoordK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RatK

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace PositivityTheory.ThKW.LagrangianIntegralFactorisation
open PositivityTheory.ThKW.ModulusFactorDefinition
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end PositivityTheory.ThKW.LagrangianIntegralFactorisation
end
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.LagrangianIntegralFactorisation in
theorem PositivityTheory.ThKW.fundamental_domain_plancherel_global : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle) (ωd : GAF σ JS × GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
            Module.End ℂ (WOF F E nS (nT + nT) → ℂ)),
        IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∃ α : GL (Fin nT) (AF F ⊗[F] E) →* Circle, Continuous α ∧
        (∀ a : GL (Fin nT) E, α (Matrix.GeneralLinearGroup.map (incAF F E) a) = 1) ∧
        ∀ (h : GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)) (t : GL (Fin nT) (AF F ⊗[F] E)),
          mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) h * ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) = ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * t.1 →
          ∀ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
            GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (ωd (1, h) f) = (α t : ℂ) * ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (Matrix.GeneralLinearGroup.det t)) : ℝ) ^ ((Fintype.card (Fin nS) : ℝ) / 2) : ℝ) : ℂ) * GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) f := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 χS ωd hωd
  obtain ⟨m, hmc, hmC, hmr⟩ := _root_.PositivityTheory.ThKW.PhaseFourierInjectivity.levi_k F E σ B hB nT JT hT
  obtain ⟨α, hαc, hαq, hlaw⟩ := core (V := WOF F E nS (nT + nT) → ℂ)
    (IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ)
    (fun a b f g hf hg => GlobalTheory.WeilPartsF.theta_add (GlobalTheory.WeilPartsF.theta_smul a hf) (GlobalTheory.WeilPartsF.theta_smul b hg))
    (ωd.comp (MonoidHom.inr _ _)) (fun h f hf => hωd.om_pres _ f hf)
    (GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT))
    (fun a b f g hf hg => lagrInt_lin ν 𝓕 f g a b
      (PositivityTheory.ThKW.PhaseFourierInjectivity.integrable F E σ nS nT JS JT ξ₀ B.ψ ν 𝓕 hν h𝓕 f hf) (PositivityTheory.ThKW.PhaseFourierInjectivity.integrable F E σ nS nT JS JT ξ₀ B.ψ ν 𝓕 hν h𝓕 g hg))
    (fun h t => mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) h * dC (AF F ⊗[F] E) nT = dC (AF F ⊗[F] E) nT * t.1)
    (fun a b s u ha hb => by
      show mtF σ _ (a * b) * _ = _ * (s * u).1
      rw [mtF_mul, Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha, Matrix.mul_assoc, Units.val_mul])
    (fun a s ha => by
      show mtF σ _ a⁻¹ * _ = _ * (s⁻¹).1
      have e : dC (AF F ⊗[F] E) nT = mtF σ _ a⁻¹ * (dC (AF F ⊗[F] E) nT * s.1) := by
        rw [← ha, ← Matrix.mul_assoc, mtF_inv_mul, Matrix.one_mul]
      calc mtF σ _ a⁻¹ * dC (AF F ⊗[F] E) nT
          = mtF σ _ a⁻¹ * (dC (AF F ⊗[F] E) nT * (s.1 * (s⁻¹).1)) := by
            rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
        _ = mtF σ _ a⁻¹ * (dC (AF F ⊗[F] E) nT * s.1) * (s⁻¹).1 := by
            simp only [Matrix.mul_assoc]
        _ = dC (AF F ⊗[F] E) nT * (s⁻¹).1 := by rw [← e])
    (mfac F E nS) (mfac_one nS) (mfac_pos nS) (mfac_mul nS)
    (fun h t hr f hf => _root_.PositivityTheory.ThKW.PhaseFourierInjectivity.norm_law_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 χS ωd hωd h t hr f hf)
    m hmc hmC
    (fun f hf => _root_.PositivityTheory.ThKW.PhaseFourierInjectivity.cont_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 χS ωd hωd f hf)
    (GQF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) : Set _)
    (fun γ hγ t hr f hf => _root_.PositivityTheory.ThKW.PhaseFourierInjectivity.rat_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 χS ωd hωd γ hγ t hr f hf)
    (fun k hk => by
      obtain ⟨M, t, h1, h2⟩ := PositivityTheory.ThKW.PhaseFourierInjectivity.conj_pow F E σ nT JT hT k hk
      exact ⟨M, t, h1, fun n hn => h2 n (by rw [Units.val_one, Matrix.mul_one] at hn; exact hn)⟩)
  exact ⟨α, hαc, fun a => hαq _ (hmr a), fun h t hr f hf => hlaw h t hr f hf⟩
end
