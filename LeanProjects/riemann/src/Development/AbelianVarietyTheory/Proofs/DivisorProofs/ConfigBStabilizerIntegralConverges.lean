import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStabilizerExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarStabilizerPeriodCaseBStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarStabilizerPeriodCaseBSecondStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.OuterFubini

theorem iter_swap {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (ν : Measure α) (μ₁ : Measure β) (μ₂ : Measure γ) [SFinite ν] [SFinite μ₁] [SFinite μ₂]
    (f : α → β → γ → ℂ) (hf : Integrable (fun p : α × β × γ => f p.1 p.2.1 p.2.2) (ν.prod (μ₁.prod μ₂))) :
    ∫ x, ∫ y, ∫ z, f x y z ∂μ₂ ∂μ₁ ∂ν = ∫ y, ∫ z, ∫ x, f x y z ∂ν ∂μ₂ ∂μ₁ := by
  have h1 : ∀ᵐ x ∂ν, ∫ y, ∫ z, f x y z ∂μ₂ ∂μ₁ = ∫ q, f x q.1 q.2 ∂(μ₁.prod μ₂) := by
    filter_upwards [hf.prod_right_ae] with x hx
    exact (integral_prod (fun q : β × γ => f x q.1 q.2) hx).symm
  rw [integral_congr_ae h1, integral_integral_swap (f := fun x (q : β × γ) => f x q.1 q.2) hf]
  exact integral_prod (fun q : β × γ => ∫ x, f x q.1 q.2 ∂ν) hf.integral_prod_right

theorem ideles_lcsc (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    IsTopologicalGroup (AE F E)ˣ ∧ LocallyCompactSpace (AE F E)ˣ ∧ SecondCountableTopology (AE F E)ˣ := by
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : SecondCountableTopology (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : LocallyCompactSpace (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  exact ⟨inferInstance, Units.isClosedEmbedding_embedProduct.locallyCompactSpace,
    Units.isEmbedding_embedProduct.secondCountableTopology⟩

theorem outer : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b)
    (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
      ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
      ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ h h₁,
        ∫ g in G₁.M'.dom, (∫ k, ∫ l, theta om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, h) Φ'))) g h₁ * (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1) ∂μ ∂μK) ∂G₁.M'.μ =
          ∫ k, ∫ l, G₁.M'.I om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, h) Φ'))) h₁ * (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1) ∂μ ∂μK := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he' K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ' h h₁
  obtain ⟨_, _, _, _⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ b G₁.V'.J
  haveI : BorelSpace (UA σ G₁.V'.J) := ⟨rfl⟩
  haveI := hT₁.geo.hM'.haar
  haveI : SigmaCompactSpace (UA σ G₁.V'.J) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SFinite G₁.M'.μ := @instSFiniteOfSigmaFinite _ _ _ (MeasureTheory.SigmaFinite.of_isFiniteMeasureOnCompacts G₁.M'.μ)
  obtain ⟨_, _, _⟩ := ideles_lcsc F E
  haveI : SigmaCompactSpace (AE F E)ˣ := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SFinite μ := @instSFiniteOfSigmaFinite _ _ _ (MeasureTheory.SigmaFinite.of_isFiniteMeasureOnCompacts μ)
  obtain ⟨K₀, -, -, hK₀, hc, -, -⟩ := GlobalTheory.T.theta_stabilizer_exists hKP.base F E σ B (b + 2) G.V' G.q (b + 2 - G.q) hT.base hT.geo.hV'
  have hKK : (K : Set (UA σ G.V'.J)) = K₀ := by
    ext g
    exact (hK g).trans (hK₀ g).symm
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp (hKK ▸ hc)
  haveI : IsFiniteMeasure μK := CompactSpace.isFiniteMeasure
  haveI : SFinite μK := @instSFiniteOfSigmaFinite _ _ _ (IsFiniteMeasure.toSigmaFinite μK)
  have hint : Integrable (fun p : UA σ G₁.V'.J × K × (AE F E)ˣ => theta om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' p.2.2) (om' (p.2.1.1, h) Φ'))) p.1 h₁ * (X.ν p.2.2 : ℂ) * ((absE F E p.2.2 : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1)) ((G₁.M'.μ.restrict G₁.M'.dom).prod (μK.prod μ)) :=
    ⟨GlobalTheory.T.haar_stabilizer_period_case_b hKP F E σ B a b G G₁ H H' hC e' he' K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ' h h₁,
     GlobalTheory.T.haar_stabilizer_period_case_b_second hKP F E σ B a b G G₁ H H' hC e' he' K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ' h h₁⟩
  rw [iter_swap _ _ _ (fun (g : UA σ G₁.V'.J) (k : K) (l : (AE F E)ˣ) => theta om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, h) Φ'))) g h₁ * (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1)) hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => integral_congr_ae (Filter.Eventually.of_forall fun l => ?_))
  simp only [Model.I, integral_mul_const]

end GlobalTheory.OuterFubini
