import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.MeasurableSetLatHLoc
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.TendstoUH
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.SelfDualMeasureLatticeOne
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenLowOf

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GFac

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw Filter
open PositivityTheory.SiegelWeilFormula.Gen
open GlobalTheory.CompanionTheory.SiegelND.Coef (hermInf hermFin hermV latH intH)
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem factor_core (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M n d : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    (T : Matrix (Fin n) (Fin n) E) (bs : Module.Basis (Fin d) F E) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ)
    {ι : Type} [Fintype ι] (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (fr : ι → GL (Fin M) ℂ) (g : ι → GL (Fin n) ℂ)
    (P : ι → PX M n) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fv F v ⊗[F] E))
    (L₁ L₂ : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (Fin n → Fv F v ⊗[F] E))
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ)
    (μ : Measure (Fin n → Fin M → AF F ⊗[F] E)) (ν : Measure (HermR (AF F) σ n))
    (haar : ∀ v, (lam v).IsAddHaarMeasure) (co : ∀ v, IsCO (L₁ v) ∧ IsCO (L₂ v))
    (std : ∀ᶠ v in cofinite, (L₁ v : Set (Fin n → Fv F v ⊗[F] E)) = latO bs v ∧ (L₂ v : Set (Fin n → Fv F v ⊗[F] E)) = latO bs v)
    (pure : IsPureFin bs Φf Φv) (prod : IsProdInfFin Φ (phiInf θ l fr g P) Φf) (sdW : SdW F E σ M J (AF F) ψ n μ)
    (sdH : SdHerm F E σ (AF F) ψ n ν)
    (μi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (νi : Measure (HermR (Ainf F) σ n))
    (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    (νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ n))
    (hμi : SdW F E σ M J (Ainf F) (psiInf F ψ) n μi) (hνi : SdHerm F E σ (Ainf F) (psiInf F ψ) n νi)
    (hμv : ∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) n (μv v)) (hνv : ∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) n (νv v))
    (z : ℂ) (hI : Integrable (whI (AF F) σ J ψ μ Φ (nuA θ g lam L₁ L₂) (T.map (inclR (AF F))) z) ν)
    (hIv : ∀ v, Integrable (whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v)) (T.map (inclR (Fv F v))) z)
        (νv v)) :
    Tendsto (fun s : Finset (HeightOneSpectrum (𝓞 F)) =>
        (∫ b, whI (Ainf F) σ J (psiInf F ψ) μi (phiInf θ l fr g P) (nuInf θ g) (T.map (inclR (Ainf F))) z b ∂νi) *
        ∏ v ∈ s, ∫ b, whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v)) (T.map (inclR (Fv F v))) z b
          ∂(νv v))
      atTop (nhds (∫ b, whI (AF F) σ J ψ μ Φ (nuA θ g lam L₁ L₂) (T.map (inclR (AF F))) z b ∂ν)) := by
  classical
  obtain ⟨S₀, hS₀⟩ := herm_split σ hCM ψ hψ n d bs ν sdH νi hνi νv hνv
  obtain ⟨S₁, hS₁⟩ := whI_split σ hCM M n d J hJ T bs ψ hψ θ l fr g P lam L₁ L₂ Φ Φf Φv μ haar co std pure prod sdW
    μi hμi μv hμv z
  refine (tendsto_UH σ hCM bs n ν _ hI).congr' ?_
  filter_upwards [eventually_ge_atTop (S₀ ∪ S₁)] with S hS
  have h0 : S₀ ⊆ S := fun v hv => hS (Finset.mem_union_left _ hv)
  have h1 : S₁ ⊆ S := fun v hv => hS (Finset.mem_union_right _ hv)
  rw [setIntegral_congr_fun (measurableSet_UH σ hCM bs n S) (fun b hb => hS₁ S h1 b hb)]
  exact hS₀ S h0 _ _ (fun v _ => (hIv v).aestronglyMeasurable)

theorem factorX : FactorX := by
  intro F E _ _ _ _ _ σ M n d J T bs ψ ι _ θ l ε fr g P lam L₁ L₂ Φ Φf Φv μ ν h μi νi μv νv hμi hνi hμv hνv z hI _ hIv
  exact factor_core σ h.cm M n d J h.herm T bs ψ h.chr θ l fr g P lam L₁ L₂ Φ Φf Φv μ ν h.haar h.co h.std h.pure h.prod
    h.sdW h.sdH μi νi μv νv hμi hνi hμv hνv z hI hIv

end PositivityTheory.SiegelWeilFormula.GFac

end
