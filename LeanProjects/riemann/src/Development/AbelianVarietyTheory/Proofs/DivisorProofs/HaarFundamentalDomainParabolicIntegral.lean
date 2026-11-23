import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundamentalDomainClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalClosedNonzero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAHaarUnfoldingMeasure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviHaarStabilizerMeasureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingFundamentalDomainIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviMapPreservesRationalPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviElementUniqueBisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviRationalPointVectorActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentHaarLeviDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFundamentalDomainAltBis

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.FoldLine

theorem units_lcsc (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
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

theorem levi_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} (H : Plane E d d₁) {t t' : (AE F E)ˣ} {h₁ h₁' : UA σ W₁.J}
    {h h' : UA σ W.J} (e : IsLevi H t h₁ h) (e' : IsLevi H t' h₁' h') : IsLevi H (t * t') (h₁ * h₁') (h * h') := by
  obtain ⟨ex, ey, eι⟩ := e
  obtain ⟨ex', ey', eι'⟩ := e'
  have mm : ∀ {k : ℕ} {J : Matrix (Fin k) (Fin k) E} (a b : UA σ J), mat (a * b) = mat a * mat b := fun _ _ => rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [mm, ← Matrix.mulVec_mulVec, ex', Matrix.mulVec_smul, ex, smul_smul, Units.val_mul, mul_comm]
  · rw [mm, ← Matrix.mulVec_mulVec, ey', Matrix.mulVec_smul, ey, smul_smul, mul_inv_rev, Units.val_mul, map_mul]
  · rw [mm, mm, Matrix.mul_assoc, eι', ← Matrix.mul_assoc, eι, Matrix.mul_assoc]

theorem unip_fix {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n n₁ : ℕ} (X : Spc F E n) (H : Plane E n n₁) : ∀ u ∈ unip σ X H, mat u *ᵥ incV F H.x = incV F H.x := by
  intro u hu
  induction hu using Subgroup.closure_induction with
  | mem v hv => exact hv.1
  | one => exact Matrix.one_mulVec _
  | mul a b _ _ ha hb =>
    show (mat a * mat b) *ᵥ _ = _
    rw [← Matrix.mulVec_mulVec, hb, ha]
  | inv a _ ha =>
    have e := congrArg (fun z => mat a⁻¹ *ᵥ z) ha
    simp only [Matrix.mulVec_mulVec, GlobalTheory.StabHaar.mat_inv_mul, Matrix.one_mulVec] at e
    exact e.symm

theorem levi_cont {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E) {n n₁ : ℕ} (X Y : Spc F E n) (X₁ : Spc F E n₁) (H : Plane E n n₁) {r s i₀ i₁ : ℕ}
    (hXY : (reS X Y).IsHerm σ B r s) (hH : H.IsAdapted σ B (reS X Y) X₁ i₀ i₁)
    (m : (AE F E)ˣ → UA σ X₁.J → UA σ X.J) (hm : ∀ l g₀, IsLevi (W₁ := X₁) H l g₀ (m l g₀)) :
    Continuous fun p : (AE F E)ˣ × UA σ X₁.J => m p.1 p.2 := by
  obtain rfl := hH.rank
  have hL : Submodule.span E ((reS X Y).L : Set (Fin (n₁ + 2) → E)) = ⊤ := hXY.lat.span_eq_top
  choose a b c hdec using fun j : Fin (n₁ + 2) => GlobalTheory.IterBochner.exists_decomp B H (reS X Y) X₁ hH hL (Pi.single j 1)
  exact GlobalTheory.IterBochner.continuous_of_isLevi (W := X) (W₁ := X₁) H a b c hdec m hm

theorem lintegral_fd_le_iwasawa : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (X Y : Spc F E n) (X₁ : Spc F E n₁) (H : Plane E n n₁) (r s i₀ i₁ : ℕ), B.IsGood σ → X.IsHerm σ B r s → (reS X Y).IsHerm σ B r s → H.IsAdapted σ B (reS X Y) X₁ i₀ i₁ → ∀ (μX : Measure (UA σ X.J)) (μ₁ : Measure (UA σ X₁.J)) (D₁ : Set (UA σ X₁.J)), μX.IsHaarMeasure → μ₁.IsHaarMeasure → IsFundamentalDomain (ratU σ X₁.J) D₁ μ₁ → ∀ (K : Subgroup (UA σ X.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab (X := X) B K → μK.IsHaarMeasure → μ.IsHaarMeasure → ∀ m : (AE F E)ˣ → UA σ X₁.J → UA σ X.J, (∀ l g₀, IsLevi (W₁ := X₁) H l g₀ (m l g₀)) → ∀ Q : Subgroup (UA σ X.J), (∀ q, q ∈ Q ↔ q ∈ ratU σ X.J ∧ mat q *ᵥ incV F H.x = incV F H.x) → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ 𝓓 : Set (UA σ X.J), IsFundamentalDomain Q 𝓓 μX → ∀ f : UA σ X.J → ℝ≥0∞, AEMeasurable f μX → (∀ q ∈ Q, ∀ g, f (q * g) = f g) → (∀ u ∈ unip σ X H, ∀ g, f (u * g) = f g) → ∫⁻ g in 𝓓, f g ∂μX ≤ C * ∫⁻ k, ∫⁻ l, ∫⁻ g₀ in D₁, f (m l g₀ * k.1) * ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - (n : ℝ))) ∂μ₁ ∂μ ∂μK := by
  intro F E _ _ _ _ _ σ B n n₁ X Y X₁ H r s i₀ i₁ hB hX hXY hH μX μ₁ D₁ hμX hμ₁ hD₁ K μK μ hK hμK hμ m hm Q hQ
  obtain ⟨hTG, hLC, hSC, hT2⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ n X.J
  obtain ⟨hTG₁, hLC₁, hSC₁, hT2₁⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ n₁ X₁.J
  obtain ⟨hTGi, hLCi, hSCi⟩ := units_lcsc F E
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  haveI : BorelSpace (UA σ X₁.J) := ⟨rfl⟩
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  haveI := hμX
  haveI := hμ₁
  haveI := hμ
  haveI : SFinite μ₁ := @instSFiniteOfSigmaFinite _ _ _ (MeasureTheory.SigmaFinite.of_isFiniteMeasureOnCompacts μ₁)
  haveI : SFinite μ := @instSFiniteOfSigmaFinite _ _ _ (MeasureTheory.SigmaFinite.of_isFiniteMeasureOnCompacts μ)
  haveI : Countable (ratU σ X.J) := GlobalTheory.QDom.countable_ratU σ X.J
  haveI : Countable (ratU σ X₁.J) := GlobalTheory.QDom.countable_ratU σ X₁.J
  obtain ⟨μN, c, hμN, hc0, hcT, hform⟩ := GlobalTheory.T.levi_haar_stabilizer_measure F E σ B n n₁ X Y X₁ H r s i₀ i₁ hB hX hXY hH μX μ₁ hμX hμ₁ K μK μ hK hμK hμ m hm
  haveI := hμN
  have hx0 : H.x ≠ 0 := fun h0 => by
    have h1 := hH.xy
    rw [h0] at h1
    simp [form] at h1
  have hcl := GlobalTheory.UnipClosed.isClosed_unip F E σ n n₁ X H hx0
  haveI : LocallyCompactSpace (unip σ X H) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (unip σ X H) := hcl.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  haveI : SFinite μN := @instSFiniteOfSigmaFinite _ _ _ (MeasureTheory.SigmaFinite.of_isFiniteMeasureOnCompacts μN)
  obtain ⟨𝓕, h𝓕, -, h𝓕top⟩ := GlobalTheory.T.exists_unip_fundamentalDomain_finite_pos_measure F E σ B n n₁ X Y X₁ H r s i₀ i₁ hB hX hXY hH μN hμN
  have hQr : Q ≤ ratU σ X.J := fun q hq => ((hQ q).1 hq).1
  have hQc : Countable Q := (Subgroup.inclusion_injective hQr).countable
  have hsub : Q.subgroupOf (unip σ X H) = (ratU σ X.J).subgroupOf (unip σ X H) := by
    ext u
    simp only [Subgroup.mem_subgroupOf]
    exact ⟨fun h => hQr h, fun h => (hQ _).2 ⟨h, unip_fix X H _ u.2⟩⟩
  have h𝓕' : IsFundamentalDomain (Q.subgroupOf (unip σ X H)) 𝓕 μN := by rw [hsub]; exact h𝓕
  have hmulm : ∀ l g₀, ∀ γ ∈ ratU σ X₁.J, m l (γ * g₀) = m 1 γ * m l g₀ := by
    intro l g₀ γ _
    refine GlobalTheory.T.levi_element_unique_bis F E σ B n n₁ X Y X₁ H r s i₀ i₁ hB hX hXY hH l (γ * g₀) _ _ (hm l (γ * g₀)) ?_
    simpa only [one_mul] using levi_mul H (hm 1 γ) (hm l g₀)
  have hιQ : ∀ γ ∈ ratU σ X₁.J, m 1 γ ∈ Q := by
    intro γ hγ
    refine (hQ _).2 ⟨GlobalTheory.T.levi_map_preserves_rational_points F E σ B n n₁ X Y X₁ H r s i₀ i₁ hB hX hXY hH m hm γ hγ, ?_⟩
    rw [(hm 1 γ).1, Units.val_one, one_smul]
  have huniq : ∀ q ∈ Q, ∃! γ : ratU σ X₁.J, (m 1 γ)⁻¹ * q ∈ unip σ X H := fun q hq =>
    GlobalTheory.T.levi_rational_point_vector_action F E σ B n n₁ X Y X₁ H r s i₀ i₁ hB hX hXY hH m hm q ((hQ q).1 hq).1 ((hQ q).1 hq).2
  have hcont := levi_cont B X Y X₁ H hXY hH m hm
  have hjoint : Measurable (fun p : unip σ X H × UA σ X₁.J × (AE F E)ˣ × K => p.1.1 * m p.2.2.1 p.2.1 * p.2.2.2.1) := by
    apply Continuous.measurable
    exact ((continuous_subtype_val.comp continuous_fst).mul
      (hcont.comp ((continuous_fst.comp (continuous_snd.comp continuous_snd)).prodMk (continuous_fst.comp continuous_snd)))).mul
      (continuous_subtype_val.comp (continuous_snd.comp (continuous_snd.comp continuous_snd)))
  have habs : ∀ l : (AE F E)ˣ, 0 < (absE F E l : ℝ) := by
    intro l
    have h1 : absE F E l * absE F E l⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    exact NNReal.coe_pos.2 (pos_iff_ne_zero.2 (left_ne_zero_of_mul_eq_one h1))
  have hw : Measurable fun l : (AE F E)ˣ => ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - (n : ℝ))) :=
    ENNReal.measurable_ofReal.comp ((NNReal.continuous_coe.comp GlobalTheory.Doubling.continuous_absE).measurable.pow_const _)
  have hw0 : ∀ l : (AE F E)ˣ, ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - (n : ℝ))) ≠ 0 := fun l =>
    (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos (habs l) _)).ne'
  refine ⟨c * μN 𝓕, ENNReal.mul_ne_top hcT h𝓕top, ?_⟩
  intro 𝓓 h𝓓 f hf hfQ hfN
  exact GlobalTheory.T.unfolding_fundamental_domain_integral μX μ₁ μ μK (unip σ X H) Q (ratU σ X₁.J) μN (fun k : K => k.1) m (fun γ => m 1 γ)
    (fun l => ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - (n : ℝ)))) c D₁ 𝓕
    hQc inferInstance inferInstance inferInstance inferInstance (fun g => (continuous_mul_left g).measurable)
    (fun g => (continuous_mul_left g).measurable) (fun g => (continuous_mul_right g).measurable) hjoint hw hw0
    (fun _ => ENNReal.ofReal_ne_top) inferInstance hform hc0 hcT hmulm hιQ huniq
    (fun γ _ f hf => GlobalTheory.T.unipotent_haar_levi_decomposition F E σ B n n₁ X Y X₁ H r s i₀ i₁ hB hX hXY hH m hm μN hμN γ f hf)
    inferInstance h𝓕' h𝓕top hD₁ inferInstance 𝓓 h𝓓 f hf hfQ hfN

end GlobalTheory.FoldLine
