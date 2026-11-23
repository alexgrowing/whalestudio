import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalTranslationEquivariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEmbeddingAtEveryPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlCharacterFactorsThroughDetOfTwoNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarFunctionalGoodPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryDeterminedBySplitImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulOfCommuteHeisenbergLinearModelSchwartzBruhStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelHeisenbergOperatorsTranslationCharStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGLEmbeddingUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupVStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryAdelicSchwartzOfNonzeroLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodingerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergPreservesSchwartzBStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergInnerPreservingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodicMeasurableSchwartzBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqComponentTensorEqConstMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsWeilCharacterDetEqAbsDetPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilMatrixTransportSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarIntertwinerExistsStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix

namespace GlobalTheory.WRightNorm

theorem lemE : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ (v : Pl F) (h : UA σ G.W.J),
    ∀ φ φ₁ : (Fin a' × Fin (a + a') → Fv F v) → ℂ, φ ∈ GlobalTheory.WeilM.SB _ → φ₁ ∈ GlobalTheory.WeilM.SB _ →
      Acts (evFin F v) (om' (1, h)) φ φ₁ →
      ∀ μ : @MeasureTheory.Measure (Fin a' × Fin (a + a') → Fv F v) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∫⁻ y, ‖φ₁ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v h φ φ₁ hφ hφ₁ hact μ hμ
  obtain ⟨r, K, hrm, hinv, hsch, hK, hKi, hint⟩ := GlobalTheory.T.exists_periodic_measurable_schwartz_bound (κ := Fin a' × Fin (a + a')) v
  letI mA : MeasurableSpace (Fin a' × Fin (a + a') → AF F) := borel _
  haveI : BorelSpace (Fin a' × Fin (a + a') → AF F) := ⟨rfl⟩
  have hμA : MeasureTheory.Measure.IsAddHaarMeasure
      (MeasureTheory.Measure.addHaar : MeasureTheory.Measure (Fin a' × Fin (a + a') → AF F)) := inferInstance
  obtain ⟨C, hC0, hCt, hC⟩ := GlobalTheory.T.lintegral_normSq_componentTensor_eq_const_mul v r hrm hinv _ hμA μ hμ K hK hKi (hint _ hμA).1 (hint _ hμA).2
  have hU := (GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil').unit
  have e := hU _ hμA (1, h) _ (hsch φ hφ)
  rw [hact r ⟨hinv, hsch φ hφ⟩, hC φ₁ hφ₁.1.continuous hφ₁.2, hC φ hφ.1.continuous hφ.2] at e
  exact (ENNReal.mul_right_inj hC0 hCt).mp e

theorem norm_scalar_eq : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ ι, G.M'.IsLinBar B.ψ B.τ₁ 1 1 ι → ∀ h ∈ UAt σ G.W (evFin F B.v₁), ∀ c : ℂ,
      (∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁), ∀ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁),
        Acts (evFin F B.v₁) (om' (1, h)) φ φ₁ → ι φ₁ = c • fun Y => ι φ (Y * (mat h).map (piW B.τ₁))) →
      ‖c‖ = ‖GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet (GlobalTheory.LocalUnitSubgroupClosure.cmpGL B.τ₁ h)) ((a' : ℂ) / 2)‖ := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hTr ι hι h hh c hc
  obtain ⟨K, hK⟩ := GlobalTheory.T.exists_local_GL_embedding_unitary F E σ B a a' G X om om' hTr B.v₁ hTr.chars.good B.τ₁
  choose SV hSV using fun g => GlobalTheory.T.weilRepresentationLocality_unitaryGroupV' B G X om om' hTr B.v₁ (K g) (hK g).1
  have hSplit := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil'
  have restS : ∀ g φ r, φ ∈ GlobalTheory.WeilM.SB _ → Rest (evFin F B.v₁) φ r → Rest (evFin F B.v₁) (SV g φ) r := fun g φ r hφ hr =>
    ⟨hr.1, by rw [← (hSV g φ hφ).2 r hr]; exact hSplit.pres _ _ hr.2⟩
  have h1 : ∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁), SV g φ ∈ GlobalTheory.WeilM.SB _ := fun g φ hφ => (hSV g φ hφ).1
  have hψ : Continuous B.ψ := hTr.base.std.1
  have atAct : ∀ g (γ : Matrix (Fin a') (Fin (a + a')) (AE F E)), At (evFin F B.v₁) γ →
      At (evFin F B.v₁) (GlobalTheory.WeilM.actAB (cA σ) (K g, (1 : UA σ G.W.J)) γ) := by
    intro g γ hγ u hu
    simp only [GlobalTheory.WeilM.actAB]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hγ u hu, Matrix.mul_zero, Matrix.zero_mul]
  have h4 : ∀ g (γ : Matrix (Fin a') (Fin (a + a')) (AE F E)), At (evFin F B.v₁) γ →
      ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁),
        SV g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) (GlobalTheory.LatVac.locCo G.M'.co B.v₁ γ) φ) =
          GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁)
            (GlobalTheory.LatVac.locCo G.M'.co B.v₁ (GlobalTheory.WeilM.actAB (cA σ) (K g, (1 : UA σ G.W.J)) γ)) (SV g φ) := by
    intro g γ hγ φ hφ
    have hw := GlobalTheory.T.schrodinger_preserves_schwartz_bruhat B.ψ hψ B.v₁ (GlobalTheory.LatVac.locCo G.M'.co B.v₁ γ) φ hφ
    refine GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq B.v₁ φ _ _ hφ fun r hr => ?_
    have hb1 := GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger G.M'.co B.ψ B.v₁ γ hγ φ r hr
    have hRw : Rest (evFin F B.v₁) (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) (GlobalTheory.LatVac.locCo G.M'.co B.v₁ γ) φ) r :=
      ⟨hr.1, by rw [← hb1]; exact GlobalTheory.T.weil_representation_preserves_schwartz G.M' B.ψ hTr.base.std γ _ hr.2⟩
    rw [← (hSV g _ hw).2 r hRw, ← hb1, hSplit.impl _ _ _ hr.2, (hSV g φ hφ).2 r hr,
      GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger G.M'.co B.ψ B.v₁ _ (atAct g γ hγ) (SV g φ) r (restS g φ r hφ hr)]
  obtain ⟨hψc, hψ1, wT, wM, hA⟩ := GlobalTheory.T.linearModel_heisenbergOperators_translation_char B G X om om' hTr K hK SV h1 h4
  obtain ⟨hTι, hMι, -, -⟩ := hA ι hι
  have hU0 : ∀ (w : (Fin a' × Fin (a + a') → Fv F B.v₁) × (Fin a' × Fin (a + a') → Fv F B.v₁)),
      ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁), GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) w φ ∈ GlobalTheory.WeilM.SB _ :=
    fun w => GlobalTheory.T.schroedingerOperatorHeisenberg_preserves_schwartzBruhat (GlobalTheory.LatVac.psiAt B.ψ B.v₁) hψc w
  obtain ⟨S, χ, hS, hSι, hid⟩ := GlobalTheory.T.linear_bar_intertwiner_exists hP F E σ B a a' G X om om' hTr ι hι
  have hSB : ∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁), S g φ ∈ GlobalTheory.WeilM.SB _ := fun g φ hφ => by
    obtain ⟨h', -, hS'⟩ := hS g
    exact (hS' φ hφ).1
  have hSI : ∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁),
      ∀ μ : @MeasureTheory.Measure (Fin a' × Fin (a + a') → Fv F B.v₁) (borel _),
      @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ := by
    intro g φ hφ μ hμ
    obtain ⟨h', -, hS'⟩ := hS g
    exact lemE F E σ B a a' G X om om' hTr B.v₁ h' φ (S g φ) hφ (hS' φ hφ).1 (hS' φ hφ).2 μ hμ
  obtain ⟨ν, hν1, hν⟩ := GlobalTheory.T.weil_matrix_transport_schwartz (GlobalTheory.LatVac.psiAt B.ψ B.v₁) hψc hψ1 ι hι.bij
    (fun C => GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) (wT C))
    (fun l => GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) (wM l))
    (fun C φ hφ => ⟨hU0 _ φ hφ, hTι C φ hφ⟩) (fun l φ hφ => ⟨hU0 _ φ hφ, hMι l φ hφ⟩)
    (fun μ hμ C φ _ φ' _ => GlobalTheory.T.schroedingerOperatorHeisenberg_inner_preserving _ hψc μ hμ _ φ φ') (fun μ hμ l φ _ φ' _ => GlobalTheory.T.schroedingerOperatorHeisenberg_inner_preserving _ hψc μ hμ _ φ φ')
    S hSB hSI χ hSι
  rw [hid h hh c hc, hν, norm_mul, hν1, one_mul]

end GlobalTheory.WRightNorm
