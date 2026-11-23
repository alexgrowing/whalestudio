import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.NDDefs

noncomputable section

namespace PositivityTheory.PfSWUS.Loc

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont
open scoped TensorProduct

def LocFinE : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, n < M →
  ∀ (d : ℕ) (bs : Module.Basis (Fin d) F E) (ψ : AddChar (AF F) ℂ), HeckeCharacterZeroLocus.SiegelWeilU.IsCharAF F ψ →
  ∀ (v : HeightOneSpectrum (𝓞 F)),
    (∀ x : Fv F v ⊗[F] E, IsIntegral (v.adicCompletionIntegers F) x ↔
      ∀ k, (Algebra.TensorProduct.basis (Fv F v) bs).repr x k ∈ v.adicCompletionIntegers F) →
  ∀ (μv : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (νv : Measure (HermR (Fv F v) σ n))
    (lam : Measure (Fin n → Fv F v ⊗[F] E)),
    SdW F E σ M J (Fv F v) (psiV F ψ v) n μv → SdHerm F E σ (Fv F v) (psiV F ψ v) n νv → lam.IsAddHaarMeasure →
  ∀ (Φv : (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ), IsSB Φv →
  ∀ g : HermR (Fv F v) σ n → ℂ,
    IsContDensityOn μv (gramR (Fv F v) σ J) Subtype.val νv
      {S | IsUnit (S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det} Φv g →
  ∀ T : HermR (Fv F v) σ n, IsUnit (T : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det →
    ∃ W : ℂ → ℂ, AnalyticOnNhd ℂ W Set.univ ∧
      (∀ z : ℂ, (n : ℝ) / 2 < z.re → W z = ∫ b, ((nuV bs v lam σ b : ℝ) : ℂ) ^ (-(z - ((M : ℂ) - n) / 2)) *
        jtR (Fv F v) σ J (psiV F ψ v) μv Φv b *
        psiV F ψ v (-trPair (Fv F v) (T : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) b) ∂νv) ∧
      W (((M : ℂ) - n) / 2) = g T

end PositivityTheory.PfSWUS.Loc

end
