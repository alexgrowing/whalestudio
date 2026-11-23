import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarFundamentalDomainParabolicIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingIntegralCountable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinSeriesMeasurable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentNormalizerRational
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviNormalisesUnip
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralFundamentalDomainEqConstantTerm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarInvAndAutOfLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulVecMulVecMulVec

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

noncomputable section

namespace GlobalTheory.ConeRearr

theorem integral_of_lintegral {α β : Type} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    {f : α → ℂ} {g : β → ℂ} (hf : Measurable f) (hg : Measurable g) {C : ℝ≥0∞} (hC0 : C ≠ 0) (hC : C ≠ ⊤)
    (h : ∀ p : ℂ → ℝ≥0∞, Measurable p → ∫⁻ x, p (f x) ∂μ = C * ∫⁻ y, p (g y) ∂ν) (hi : Integrable f μ) :
    Integrable g ν ∧ ∫ x, f x ∂μ = (C.toReal : ℂ) * ∫ y, g y ∂ν := by
  have hmap : μ.map f = C • ν.map g := by
    ext s hs
    have h1 := h (s.indicator 1) (measurable_one.indicator hs)
    rw [← lintegral_map (measurable_one.indicator hs) hf, ← lintegral_map (measurable_one.indicator hs) hg,
      lintegral_indicator_one hs, lintegral_indicator_one hs] at h1
    simpa using h1
  refine ⟨⟨hg.aestronglyMeasurable, ?_⟩, ?_⟩
  · have h1 := h (fun z => ‖z‖ₑ) measurable_enorm
    have h2 : ∫⁻ x, ‖f x‖ₑ ∂μ < ⊤ := hi.2
    rw [h1] at h2
    exact lt_top_iff_ne_top.2 fun h3 => by
      have h4 : ∫⁻ y, ‖g y‖ₑ ∂ν = ⊤ := h3
      rw [h4, ENNReal.mul_top hC0] at h2
      exact lt_irrefl _ h2
  · have e1 : ∫ x, f x ∂μ = ∫ z, z ∂(μ.map f) := (integral_map hf.aemeasurable aestronglyMeasurable_id).symm
    have e2 : ∫ y, g y ∂ν = ∫ z, z ∂(ν.map g) := (integral_map hg.aemeasurable aestronglyMeasurable_id).symm
    rw [e1, e2, hmap, integral_smul_measure, Complex.real_smul]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem inclR_inj : Function.Injective (inclR (F := F) (E := E) (AF F)) := by
  haveI : Nontrivial (AF F) := (NumberField.AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  haveI : Nontrivial (AE F E) := Module.FaithfullyFlat.lTensor_nontrivial F (AF F) E
  exact RingHom.injective _

theorem absE_pos (l : (AE F E)ˣ) : (0 : ℝ) < absE F E l := by
  have h := map_mul (absE F E) l l⁻¹
  rw [mul_inv_cancel, map_one] at h
  exact_mod_cast pos_iff_ne_zero.mpr (left_ne_zero_of_mul_eq_one h.symm)

variable {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem smul_incV_inj {x : Fin n → E} (hx : x ≠ 0) {l l' : AE F E} (h : l • incV F x = l' • incV F x) : l = l' := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
  have hu : IsUnit (incV F x i) := (isUnit_iff_ne_zero.2 hi).map (inclR (F := F) (AF F))
  exact hu.mul_left_inj.1 (congrFun h i)

theorem rat_eigen {x : Fin n → E} (hx : x ≠ 0) {p : UA σ J} (hp : p ∈ ratU σ J) {l : (AE F E)ˣ}
    (hl : mat p *ᵥ incV F x = l.1 • incV F x) : ∃ ξ : Eˣ, l = Units.map (inclR (F := F) (AF F)).toMonoidHom ξ := by
  obtain ⟨q, hq⟩ := Subgroup.mem_subgroupOf.1 hp
  have hM : mat p = incM F q.1 := by rw [mat, ← hq]; rfl
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
  rw [hM, ← GlobalTheory.StabNormal.incM_mulVec] at hl
  have e := congrFun hl i
  have e2 : l.1 = inclR (F := F) (AF F) ((q.1 *ᵥ x) i * (x i)⁻¹) := by
    rw [map_mul]
    show _ = incV F (q.1 *ᵥ x) i * _
    rw [e, Pi.smul_apply, smul_eq_mul, mul_assoc, incV, ← map_mul, mul_inv_cancel₀ hi, map_one, mul_one]
  have h0 : (q.1 *ᵥ x) i * (x i)⁻¹ ≠ 0 := fun h0 => by
    rw [h0, map_zero] at e2
    have h1 := l.mul_inv
    rw [e2, zero_mul, ← map_one (inclR (F := F) (E := E) (AF F)), ← map_zero (inclR (F := F) (E := E) (AF F))] at h1
    exact zero_ne_one (inclR_inj h1)
  exact ⟨Units.mk0 _ h0, Units.ext e2⟩

theorem ht_mul {K : Subgroup (UA σ J)} {x : Fin n → E} {hf : UA σ J → ℝ} (hI : GlobalTheory.ConeSmall.IsIwaHt K x hf)
    (hdec : ∀ g, ∃ (p k : UA σ J) (l : (AE F E)ˣ), k ∈ K ∧ mat p *ᵥ incV F x = l.1 • incV F x ∧ g = p * k)
    {p : UA σ J} {l : (AE F E)ˣ} (hp : mat p *ᵥ incV F x = l.1 • incV F x) (g : UA σ J) :
    hf (p * g) = absE F E l * hf g := by
  obtain ⟨q, k, l', hk, hq, rfl⟩ := hdec g
  have e : mat (p * q) *ᵥ incV F x = (l * l').1 • incV F x := by
    rw [GlobalTheory.StabNormal.mat_mul, ← Matrix.mulVec_mulVec, hq, Matrix.mulVec_smul, hp, smul_smul, Units.val_mul, mul_comm]
  rw [← mul_assoc, hI _ k _ hk e, hI q k l' hk hq, map_mul, NNReal.coe_mul]

theorem ht_rat {K : Subgroup (UA σ J)} {x : Fin n → E} (hx : x ≠ 0) {hf : UA σ J → ℝ} (hI : GlobalTheory.ConeSmall.IsIwaHt K x hf)
    (hdec : ∀ g, ∃ (p k : UA σ J) (l : (AE F E)ˣ), k ∈ K ∧ mat p *ᵥ incV F x = l.1 • incV F x ∧ g = p * k)
    {p : UA σ J} (hp : p ∈ ratStab σ J x) (g : UA σ J) : hf (p * g) = hf g := by
  obtain ⟨hr, l, hl⟩ := hp
  obtain ⟨ξ, rfl⟩ := rat_eigen hx hr hl
  rw [ht_mul hI hdec hl, GlobalTheory.Doubling.absE_inclR, NNReal.coe_one, one_mul]

theorem plane_x_ne {B : Base F E} {n₁ : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {H : Plane E n n₁} {i₀ i₁ : ℕ}
    (hH : H.IsAdapted σ B X X₁ i₀ i₁) : H.x ≠ 0 := fun h0 => by
  have h1 := hH.xy
  rw [h0] at h1
  simp [form] at h1

theorem ratStab_normalises {B : Base F E} {n₁ : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {H : Plane E n n₁} {r s i₀ i₁ : ℕ}
    (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hH : H.IsAdapted σ B X X₁ i₀ i₁) :
    ∀ γ ∈ ratStab σ X.J H.x, ∀ u ∈ unip σ X H, γ * u * γ⁻¹ ∈ unip σ X H := by
  rintro γ ⟨hr, l, hl⟩ u hu
  obtain ⟨ξ, rfl⟩ := rat_eigen (plane_x_ne hH) hr hl
  obtain ⟨m, hmr, hm⟩ := GlobalTheory.RatLeviPlane.exists_ratLevi F E σ B n n₁ X X₁ H r s i₀ i₁ hB hX hH ξ
  have hq : m⁻¹ * γ ∈ ratU σ X.J ⊓ Subgroup.closure {g : UA σ X.J | mat g *ᵥ incV F H.x = incV F H.x} := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hmr) hr, Subgroup.subset_closure ?_⟩
    show mat (m⁻¹ * γ) *ᵥ _ = _
    rw [GlobalTheory.StabNormal.mat_mul, ← Matrix.mulVec_mulVec, hl, ← hm.1, Matrix.mulVec_mulVec, GlobalTheory.StabNormal.mat_inv_mul,
      Matrix.one_mulVec]
  have h1 := (GlobalTheory.StabNormal.stab_normalises_unip F E σ B n n₁ X X₁ H r s i₀ i₁ hX hH _ m hm _ hq).1 u hu
  have h2 := (GlobalTheory.LeviNormal.levi_normalises_unip F E σ n n₁ X X₁ H _ m hm _ h1).1
  convert h2 using 1
  group

theorem integral_eq_ct {B : Base F E} {n₁ : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {H : Plane E n n₁} {r s i₀ i₁ : ℕ}
    (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hH : H.IsAdapted σ B X X₁ i₀ i₁) (μX : Measure (UA σ X.J))
    (hμX : μX.IsHaarMeasure) {𝓓 : Set (UA σ X.J)} (h𝓓 : IsFundamentalDomain (ratStab σ X.J H.x) 𝓓 μX)
    {θ φ c : UA σ X.J → ℂ} (hθ : Measurable θ) (hφ : Measurable φ) (hθr : ∀ γ ∈ ratU σ X.J, ∀ g, θ (γ * g) = θ g)
    (hφr : ∀ γ ∈ ratStab σ X.J H.x, ∀ g, φ (γ * g) = φ g) (hφn : ∀ u ∈ unip σ X H, ∀ g, φ (u * g) = φ g)
    (hi : IntegrableOn (fun g => θ g * φ g) 𝓓 μX) (hc : IsCT H θ c) :
    ∫ g in 𝓓, θ g * φ g ∂μX = ∫ g in 𝓓, c g * φ g ∂μX := by
  obtain ⟨hTG, hLC, hSC, hT2⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ n X.J
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  haveI := hμX
  haveI : SFinite μX := @instSFiniteOfSigmaFinite _ _ _ (MeasureTheory.SigmaFinite.of_isFiniteMeasureOnCompacts μX)
  haveI : Countable (ratU σ X.J) := GlobalTheory.QDom.countable_ratU σ X.J
  have hΓr : ratStab σ X.J H.x ≤ ratU σ X.J := fun q hq => hq.1
  haveI : Countable (ratStab σ X.J H.x) := (Subgroup.inclusion_injective hΓr).countable
  have hcl := GlobalTheory.UnipClosed.isClosed_unip F E σ n n₁ X H (plane_x_ne hH)
  haveI : LocallyCompactSpace (unip σ X H) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (unip σ X H) := hcl.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  let ν₀ : Measure (unip σ X H) := Measure.haar
  obtain ⟨𝓕, h𝓕₀, h0, htop⟩ := GlobalTheory.T.exists_unip_fundamentalDomain_finite_pos_measure F E σ B n n₁ X X X₁ H r s i₀ i₁ hB hX hX hH ν₀ inferInstance
  let ν : Measure (unip σ X H) := (ν₀ 𝓕)⁻¹ • ν₀
  haveI hν : ν.IsHaarMeasure := Measure.IsHaarMeasure.smul ν₀ (ENNReal.inv_ne_zero.2 htop) (ENNReal.inv_ne_top.2 h0)
  haveI : SFinite ν := @instSFiniteOfSigmaFinite _ _ _ (MeasureTheory.SigmaFinite.of_isFiniteMeasureOnCompacts ν)
  have h𝓕 : IsFundamentalDomain ((ratU σ X.J).subgroupOf (unip σ X H)) 𝓕 ν :=
    h𝓕₀.mono (Measure.smul_absolutelyContinuous)
  have h1 : ν 𝓕 = 1 := by
    simp only [ν, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel h0 htop
  have hsub : (ratStab σ X.J H.x).subgroupOf (unip σ X H) = (ratU σ X.J).subgroupOf (unip σ X H) := by
    ext u
    simp only [Subgroup.mem_subgroupOf]
    exact ⟨fun h => hΓr h, fun h => ⟨h, 1, by rw [GlobalTheory.FoldLine.unip_fix X H _ u.2, Units.val_one, one_smul]⟩⟩
  haveI : Countable ((ratU σ X.J).subgroupOf (unip σ X H)) :=
    Function.Injective.countable (f := fun u : (ratU σ X.J).subgroupOf (unip σ X H) => (⟨u.1.1, u.2⟩ : ratU σ X.J))
      fun u v h => Subtype.ext (Subtype.ext (congrArg (fun z : ratU σ X.J => z.1) h))
  obtain ⟨hinv, haut⟩ := GlobalTheory.LatticeHaar.haar_inv_and_aut_of_lattice ν _ 𝓕 h𝓕 (by rw [h1]; exact one_ne_zero) (by rw [h1]; exact ENNReal.one_ne_top)
  have hnorm := ratStab_normalises hB hX hH
  have hconj : ∀ γ ∈ ratStab σ X.J H.x, ∀ f : UA σ X.J → ℝ≥0∞, Measurable f →
      ∫⁻ u, f (u.1 * γ) ∂ν = ∫⁻ u, f (γ * u.1) ∂ν := by
    intro γ hγ f hf
    let α : unip σ X H ≃* unip σ X H :=
      { toFun := fun u => ⟨γ⁻¹ * u.1 * γ⁻¹⁻¹, hnorm _ (inv_mem hγ) _ u.2⟩
        invFun := fun u => ⟨γ * u.1 * γ⁻¹, hnorm _ hγ _ u.2⟩
        left_inv := fun u => Subtype.ext (by simp only []; group)
        right_inv := fun u => Subtype.ext (by simp only []; group)
        map_mul' := fun u v => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
    have hα := haut α (((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _)
      (((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _) (fun u => by
        simp only [Subgroup.mem_subgroupOf]
        have hγr := hΓr hγ
        refine ⟨fun h => ?_, fun h => mul_mem (mul_mem (inv_mem hγr) h) (inv_mem (inv_mem hγr))⟩
        have h2 := mul_mem (mul_mem hγr h) (inv_mem hγr)
        have e : γ * (α u).1 * γ⁻¹ = u.1 := by
          show γ * (γ⁻¹ * u.1 * γ⁻¹⁻¹) * γ⁻¹ = _
          group
        rwa [e] at h2)
    rw [← hα.lintegral_comp (f := fun u : unip σ X H => f (γ * u.1))
      (hf.comp ((continuous_const.mul continuous_subtype_val).measurable))]
    refine lintegral_congr fun u => ?_
    congr 1
    show _ = γ * (γ⁻¹ * u.1 * γ⁻¹⁻¹)
    group
  have hΘ : Measurable fun g => θ g * φ g := hθ.mul hφ
  have hΘ2 : Measurable fun p : UA σ X.J × unip σ X H => θ (p.2.1 * p.1) * φ (p.2.1 * p.1) :=
    hΘ.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst).measurable
  obtain ⟨hi2, he⟩ := integral_of_lintegral (μX.restrict 𝓓) ((μX.restrict 𝓓).prod (ν.restrict 𝓕)) hΘ hΘ2 one_ne_zero
    ENNReal.one_ne_top (fun p hp => by
      have hp2 : Measurable fun y : UA σ X.J × unip σ X H => p (θ (y.2.1 * y.1) * φ (y.2.1 * y.1)) := hp.comp hΘ2
      rw [one_mul, lintegral_prod _ hp2.aemeasurable]
      exact GlobalTheory.lintegral_fundamentalDomain_eq_constantTerm μX (unip σ X H) (ratStab σ X.J H.x) ν hinv hnorm hconj 𝓕 (by rw [hsub]; exact h𝓕) h1 𝓓 h𝓓
        (fun g => p (θ g * φ g)) (hp.comp hΘ) (fun γ hγ g => by simp only [hθr γ (hΓr hγ) g, hφr γ hγ g])) hi
  rw [he, integral_prod _ hi2, ENNReal.toReal_one, Complex.ofReal_one, one_mul]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only
  rw [hc ν 𝓕 hν h𝓕 h1 g, ← integral_mul_const]
  exact integral_congr_ae (Eventually.of_forall fun u => by simp only [hφn _ u.2])

theorem integral_iwasawa {B : Base F E} {n₁ : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {H : Plane E n n₁} {r s i₀ i₁ : ℕ}
    (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hH : H.IsAdapted σ B X X₁ i₀ i₁) (μX : Measure (UA σ X.J))
    (μ₁ : Measure (UA σ X₁.J)) (D₁ : Set (UA σ X₁.J)) (hμX : μX.IsHaarMeasure) (hμ₁ : μ₁.IsHaarMeasure)
    (hD₁ : IsFundamentalDomain (ratU σ X₁.J) D₁ μ₁) (K : Subgroup (UA σ X.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ)
    (hK : IsStab (X := X) B K) (hKc : IsCompact (K : Set (UA σ X.J))) (hμK : μK.IsHaarMeasure) (hμ : μ.IsHaarMeasure)
    (m : (AE F E)ˣ → UA σ X₁.J → UA σ X.J) (hm : ∀ l g₀, IsLevi (W₁ := X₁) H l g₀ (m l g₀))
    (Q : Subgroup (UA σ X.J)) (hQ : ∀ q, q ∈ Q ↔ q ∈ ratU σ X.J ∧ mat q *ᵥ incV F H.x = incV F H.x) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ 𝓓 : Set (UA σ X.J), IsFundamentalDomain Q 𝓓 μX → ∀ f : UA σ X.J → ℂ, Measurable f →
      (∀ q ∈ Q, ∀ g, f (q * g) = f g) → (∀ u ∈ unip σ X H, ∀ g, f (u * g) = f g) → IntegrableOn f 𝓓 μX →
      ∫ g in 𝓓, f g ∂μX = C * ∫ k, ∫ l, (((absE F E l : ℝ) ^ (1 - (n : ℝ)) : ℝ) : ℂ) *
        ∫ g₀ in D₁, f (m l g₀ * k.1) ∂μ₁ ∂μ ∂μK := by
  obtain ⟨hTG, hLC, hSC, hT2⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ n X.J
  obtain ⟨hTG₁, hLC₁, hSC₁, hT2₁⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ n₁ X₁.J
  obtain ⟨hTGi, hLCi, hSCi⟩ := GlobalTheory.FoldLine.units_lcsc F E
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  haveI : BorelSpace (UA σ X₁.J) := ⟨rfl⟩
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  haveI := hμX
  haveI := hμ₁
  haveI := hμ
  haveI := hμK
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  haveI : IsFiniteMeasure μK := CompactSpace.isFiniteMeasure
  haveI : SFinite μK := @instSFiniteOfSigmaFinite _ _ _ (MeasureTheory.IsFiniteMeasure.toSigmaFinite μK)
  haveI : SFinite μ₁ := @instSFiniteOfSigmaFinite _ _ _ (MeasureTheory.SigmaFinite.of_isFiniteMeasureOnCompacts μ₁)
  haveI : SFinite μ := @instSFiniteOfSigmaFinite _ _ _ (MeasureTheory.SigmaFinite.of_isFiniteMeasureOnCompacts μ)
  haveI : Countable (ratU σ X.J) := GlobalTheory.QDom.countable_ratU σ X.J
  haveI : Countable (ratU σ X₁.J) := GlobalTheory.QDom.countable_ratU σ X₁.J
  obtain ⟨μN, c, hμN, hc0, hcT, hform⟩ := GlobalTheory.T.levi_haar_stabilizer_measure F E σ B n n₁ X X X₁ H r s i₀ i₁ hB hX hX hH μX μ₁ hμX hμ₁ K μK μ hK hμK hμ m hm
  haveI := hμN
  obtain ⟨𝓕, h𝓕, h𝓕0, h𝓕top⟩ := GlobalTheory.T.exists_unip_fundamentalDomain_finite_pos_measure F E σ B n n₁ X X X₁ H r s i₀ i₁ hB hX hX hH μN hμN
  have hQr : Q ≤ ratU σ X.J := fun q hq => ((hQ q).1 hq).1
  have hQc : Countable Q := (Subgroup.inclusion_injective hQr).countable
  have hsub : Q.subgroupOf (unip σ X H) = (ratU σ X.J).subgroupOf (unip σ X H) := by
    ext u
    simp only [Subgroup.mem_subgroupOf]
    exact ⟨fun h => hQr h, fun h => (hQ _).2 ⟨h, GlobalTheory.FoldLine.unip_fix X H _ u.2⟩⟩
  have h𝓕' : IsFundamentalDomain (Q.subgroupOf (unip σ X H)) 𝓕 μN := by rw [hsub]; exact h𝓕
  have hmulm : ∀ l g₀, ∀ γ ∈ ratU σ X₁.J, m l (γ * g₀) = m 1 γ * m l g₀ := by
    intro l g₀ γ _
    refine GlobalTheory.T.levi_element_unique_bis F E σ B n n₁ X X X₁ H r s i₀ i₁ hB hX hX hH l (γ * g₀) _ _ (hm l (γ * g₀)) ?_
    simpa only [one_mul] using GlobalTheory.FoldLine.levi_mul H (hm 1 γ) (hm l g₀)
  have hιQ : ∀ γ ∈ ratU σ X₁.J, m 1 γ ∈ Q := by
    intro γ hγ
    refine (hQ _).2 ⟨GlobalTheory.T.levi_map_preserves_rational_points F E σ B n n₁ X X X₁ H r s i₀ i₁ hB hX hX hH m hm γ hγ, ?_⟩
    rw [(hm 1 γ).1, Units.val_one, one_smul]
  have huniq : ∀ q ∈ Q, ∃! γ : ratU σ X₁.J, (m 1 γ)⁻¹ * q ∈ unip σ X H := fun q hq =>
    GlobalTheory.T.levi_rational_point_vector_action F E σ B n n₁ X X X₁ H r s i₀ i₁ hB hX hX hH m hm q ((hQ q).1 hq).1 ((hQ q).1 hq).2
  have hcont := GlobalTheory.FoldLine.levi_cont B X X X₁ H hX hH m hm
  have hjoint : Measurable (fun p : unip σ X H × UA σ X₁.J × (AE F E)ˣ × K => p.1.1 * m p.2.2.1 p.2.1 * p.2.2.2.1) := by
    apply Continuous.measurable
    exact ((continuous_subtype_val.comp continuous_fst).mul
      (hcont.comp ((continuous_fst.comp (continuous_snd.comp continuous_snd)).prodMk (continuous_fst.comp continuous_snd)))).mul
      (continuous_subtype_val.comp (continuous_snd.comp (continuous_snd.comp continuous_snd)))
  let w : (AE F E)ˣ → ℝ≥0∞ := fun l => ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - (n : ℝ)))
  have hw : Measurable w :=
    ENNReal.measurable_ofReal.comp ((NNReal.continuous_coe.comp GlobalTheory.Doubling.continuous_absE).measurable.pow_const _)
  have hw0 : ∀ l : (AE F E)ˣ, w l ≠ 0 := fun l => (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos (absE_pos l) _)).ne'
  refine ⟨((c * μN 𝓕).toReal : ℂ), ?_, ?_⟩
  · exact_mod_cast (ENNReal.toReal_pos (mul_ne_zero hc0 h𝓕0) (ENNReal.mul_ne_top hcT h𝓕top)).ne'
  intro 𝓓 h𝓓 f hf hfQ hfN hi
  have hj2 : Measurable fun p : K × (AE F E)ˣ × UA σ X₁.J => f (m p.2.1 p.2.2 * p.1.1) :=
    hf.comp ((hcont.comp continuous_snd).mul (continuous_subtype_val.comp continuous_fst)).measurable
  obtain ⟨hi2, he⟩ := integral_of_lintegral (μX.restrict 𝓓) (μK.prod ((μ.withDensity w).prod (μ₁.restrict D₁))) hf hj2
    (mul_ne_zero hc0 h𝓕0) (ENNReal.mul_ne_top hcT h𝓕top) (fun p hp => by
      rw [GlobalTheory.UnfoldSemidirect.lintegral_fundamentalDomain_eq μX μ₁ μ μK (unip σ X H) Q (ratU σ X₁.J) μN (fun k : K => k.1) m
        (fun γ => m 1 γ) w c D₁ 𝓕
        hQc inferInstance inferInstance inferInstance (fun g => (continuous_mul_left g).measurable)
        (fun g => (continuous_mul_left g).measurable) (fun g => (continuous_mul_right g).measurable) hjoint hw hw0
        (fun _ => ENNReal.ofReal_ne_top) inferInstance hform hc0 hcT hmulm hιQ huniq
        (fun γ _ f hf => GlobalTheory.T.unipotent_haar_levi_decomposition F E σ B n n₁ X X X₁ H r s i₀ i₁ hB hX hX hH m hm μN hμN γ f hf)
        inferInstance h𝓕' h𝓕0 h𝓕top hD₁ inferInstance 𝓓 h𝓓 (fun g => p (f g)) (hp.comp hf)
        (fun q hq g => by simp only [hfQ q hq g]) (fun u hu g => by simp only [hfN u hu g])]
      congr 1
      have hp2 : Measurable fun y : K × (AE F E)ˣ × UA σ X₁.J => p (f (m y.2.1 y.2.2 * y.1.1)) := hp.comp hj2
      rw [lintegral_prod _ hp2.aemeasurable]
      refine lintegral_congr fun k => ?_
      have hk : Measurable fun y : (AE F E)ˣ × UA σ X₁.J => p (f (m y.1 y.2 * k.1)) :=
        (hp.comp hj2).comp measurable_prodMk_left
      rw [lintegral_prod _ hk.aemeasurable, lintegral_withDensity_eq_lintegral_mul _ hw hk.lintegral_prod_right']
      refine lintegral_congr fun l => ?_
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, Pi.mul_apply, mul_comm]) hi
  rw [he, integral_prod _ hi2]
  congr 1
  refine integral_congr_ae (hi2.prod_right_ae.mono fun k hk => ?_)
  simp only
  rw [integral_prod _ hk, integral_withDensity_eq_integral_toReal_smul hw (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun l => ?_)
  simp only [w]
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (absE_pos l).le _), Complex.real_smul]

end GlobalTheory.ConeRearr

end
