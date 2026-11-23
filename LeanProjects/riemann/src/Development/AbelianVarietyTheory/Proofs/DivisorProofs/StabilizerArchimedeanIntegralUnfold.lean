import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLineStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaHaarIntegralFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarUnitaryRightInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabolicLineStabilizerDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedLineStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactOpenCompactAtInfinityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineStabilizerModulusHaarStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
open GlobalTheory.IwasawaKAvgInt

namespace GlobalTheory.IwasawaKAvgInt

theorem xne {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {n₁ : ℕ} {X : Spc F E (n₁ + 2)} {X₁ : Spc F E n₁} {H : Plane E (n₁ + 2) n₁} {i₀ i₁ : ℕ}
    (hH : H.IsAdapted σ B X X₁ i₀ i₁) : H.x ≠ 0 := by
  intro h
  have := hH.xy
  rw [h] at this
  simp [form] at this

theorem kInt_right_inv_of_integrable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n₁ : ℕ) (X : Spc F E (n₁ + 2)) (X₁ : Spc F E n₁) (H : Plane E (n₁ + 2) n₁) (i₀ i₁ r s : ℕ), B.IsGood σ →
    X.IsHerm σ B r s → H.IsAdapted σ B X X₁ i₀ i₁ → ∀ K : Subgroup (UA σ X.J), IsStab B K →
    ∀ μK : Measure (KAt K (evI F)), μK.IsHaarMeasure → ∀ Ψ : UA σ X.J → ℂ,
    (∀ g ∈ UAt σ X (evI F), Integrable (fun k : KAt K (evI F) => Ψ (k.1 * g)) μK) →
    (∀ p ∈ UAt σ X (evI F), ∀ g ∈ UAt σ X (evI F), ∀ t : (AE F E)ˣ, mat p *ᵥ incV F H.x = t.1 • incV F H.x →
      Ψ (p * g) = (((absE F E t : ℝ) ^ (n₁ + 1) : ℝ) : ℂ) * Ψ g) →
    ∀ g ∈ UAt σ X (evI F), ∫ k, Ψ (k.1 * g) ∂μK = ∫ k, Ψ k.1 ∂μK := by
  intro F E _ _ _ _ _ σ B n₁ X X₁ H i₀ i₁ r s hB hX hH K hK μK hμK Ψ hint hequiv g hg
  obtain ⟨hTG, hLC, hSC, hT2⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ (n₁ + 2) X.J
  haveI := hTG; haveI := hLC; haveI := hSC; haveI := hT2
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  have hGc : IsClosed ((UAtSub σ X (evI F) : Subgroup (UA σ X.J)) : Set (UA σ X.J)) := isClosed_UAtSub X (evI F)
  haveI : LocallyCompactSpace (UAtSub σ X (evI F)) := hGc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hPc := GlobalTheory.T.isClosed_line_stabilizer F E σ (n₁ + 2) X H.x (xne hH)
  haveI : LocallyCompactSpace (lineStab σ X H.x) := hPc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hKc := GlobalTheory.T.isCompact_open_compact_at_infinity F E σ B (n₁ + 2) X r s hB hX K hK
  haveI : CompactSpace (KAt K (evI F)) := isCompact_iff_compactSpace.mp hKc
  let ι : KAt K (evI F) →* UAtSub σ X (evI F) := Subgroup.inclusion inf_le_right
  have hιc : Continuous ι := Continuous.subtype_mk continuous_subtype_val _
  have hιi : Function.Injective ι := Subgroup.inclusion_injective _
  let δ : lineStab σ X H.x → ℝ≥0 := fun p => absE F E p.2.choose ^ (n₁ + 1)
  have hδ : ∀ p : lineStab σ X H.x, (Measure.haar : Measure (lineStab σ X H.x)).map (· * p) = δ p • Measure.haar :=
    fun p => GlobalTheory.T.line_stabilizer_modulus_haar F E σ B n₁ X X₁ H i₀ i₁ r s hB hX hH _ inferInstance p _ p.2.choose_spec
  have hdec : ∀ x : UAtSub σ X (evI F), ∃ p ∈ lineStab σ X H.x, ∃ k : KAt K (evI F), x = p * ι k := by
    intro x
    obtain ⟨p, hp, hpt, k, hk, he⟩ := GlobalTheory.T.parabolic_line_stabilizer_decomposition F E σ B n₁ X X₁ H i₀ i₁ r s hB hX hH K hK x.1 x.2
    exact ⟨⟨p, hp⟩, hpt, ⟨k, hk⟩, Subtype.ext he⟩
  have key := GlobalTheory.T.iwasawa_haar_integral_formula (UAtSub σ X (evI F)) (KAt K (evI F)) ι (lineStab σ X H.x) Measure.haar Measure.haar μK δ
    hιc hιi hPc inferInstance inferInstance hμK (GlobalTheory.T.haar_unitary_right_invariant F E σ B (n₁ + 2) X r s hB hX _ inferInstance) hδ hdec
    (fun x => Ψ x.1) (fun x => hint x.1 x.2) (fun p x => by
      have h := hequiv p.1.1 p.1.2 x.1 x.2 _ p.2.choose_spec
      show Ψ (p.1.1 * x.1) = _
      rw [h]
      simp [δ]) ⟨g, hg⟩
  exact key

end GlobalTheory.IwasawaKAvgInt
