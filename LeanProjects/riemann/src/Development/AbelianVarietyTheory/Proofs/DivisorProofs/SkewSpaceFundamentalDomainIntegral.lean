import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPairDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationUnramifiedIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTopSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingZeroMeanNormalizedSubgroup

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.CuspConeVanish

open GlobalTheory.UnipMass

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {d d₁ : ℕ}

private theorem mat_inv_fix {J : Matrix (Fin d) (Fin d) E} (p : UA σ J) {v : Fin d → AE F E} (h : mat p *ᵥ v = v) :
    mat p⁻¹ *ᵥ v = v := by
  conv_lhs => rw [← h]
  rw [Matrix.mulVec_mulVec, GlobalTheory.StabCosetDomain.mat_inv_mul, Matrix.one_mulVec]

private def ratStab (σ : E →ₐ[F] E) (J : Matrix (Fin d) (Fin d) E) (x : Fin d → E) : Subgroup (UA σ J) where
  carrier := {p | p ∈ ratU σ J ∧ mat p *ᵥ incV F x = incV F x}
  one_mem' := ⟨one_mem _, by simp [mat]⟩
  mul_mem' := fun {p q} hp hq => ⟨mul_mem hp.1 hq.1, by
    rw [GlobalTheory.StabCosetDomain.mat_mul, ← Matrix.mulVec_mulVec, hq.2, hp.2]⟩
  inv_mem' := fun {p} hp => ⟨inv_mem hp.1, mat_inv_fix p hp.2⟩

private theorem existsUnique_coset {J : Matrix (Fin d) (Fin d) E} {x : Fin d → E} (hx0 : x ≠ 0) (hxx : form σ J x x = 0)
    (γ : {w : Fin d → E // w ≠ 0 ∧ form σ J w w = 0} → UA σ J)
    (hγ : ∀ w, γ w ∈ ratU σ J ∧ mat (γ w) *ᵥ incV F w.1 = incV F x) (δ : UA σ J) (hδ : δ ∈ ratU σ J) :
    ∃! w, δ * (γ w)⁻¹ ∈ ratStab σ J x := by
  obtain ⟨g₀, hmat, hunit⟩ := GlobalTheory.StabCosetDomain.rat_desc δ⁻¹ (inv_mem hδ)
  have hmv : mat δ⁻¹ *ᵥ incV F x = incV F (g₀ *ᵥ x) := by
    rw [hmat]; funext i; exact (RingHom.map_mulVec (inclR (F := F) (AF F)) g₀ x i).symm
  have hv0 : g₀ *ᵥ x ≠ 0 := by
    intro h0
    have hz : incV F (0 : Fin d → E) = 0 := funext fun i => by simp [incV]
    have hy : mat δ⁻¹ *ᵥ incV F (0 : Fin d → E) = incV F 0 := by
      rw [hz, Matrix.mulVec_zero]
    exact hx0 (GlobalTheory.StabCosetDomain.eq_of_mulVec δ⁻¹ (hmv.trans (by rw [h0])) hy)
  have hviso : form σ J (g₀ *ᵥ x) (g₀ *ᵥ x) = 0 := by
    rw [GlobalTheory.StabCosetDomain.form_pres hunit]; exact hxx
  have key : ∀ w : {w : Fin d → E // w ≠ 0 ∧ form σ J w w = 0}, δ * (γ w)⁻¹ ∈ ratStab σ J x ↔ w.1 = g₀ *ᵥ x := by
    intro w
    rw [← inv_mem_iff, mul_inv_rev, inv_inv]
    constructor
    · intro h
      have h2 := h.2
      rw [GlobalTheory.StabCosetDomain.mat_mul, ← Matrix.mulVec_mulVec, hmv] at h2
      exact GlobalTheory.StabCosetDomain.eq_of_mulVec (γ w) (hγ w).2 h2
    · intro h
      refine ⟨mul_mem (hγ w).1 (inv_mem hδ), ?_⟩
      rw [GlobalTheory.StabCosetDomain.mat_mul, ← Matrix.mulVec_mulVec, hmv, ← h]
      exact (hγ w).2
  exact ⟨⟨g₀ *ᵥ x, hv0, hviso⟩, (key _).2 rfl, fun w hw => Subtype.ext ((key w).1 hw)⟩

private theorem span_of_adapted {B : Base F E} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁} {i₀ i₁ r' s' : ℕ}
    (hW : W.IsSkew σ B r' s') (hH : H'.IsAdapted σ B W W₁ i₀ i₁) (v : Fin d → E) :
    ∃ (s t : E) (u : Fin d₁ → E), v = s • H'.x + H'.ι *ᵥ u + t • H'.y := by
  have hv : v ∈ Submodule.span E (W.L : Set (Fin d → E)) := by
    rw [hW.lat.span_eq_top]; trivial
  induction hv using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨s, t, u, -, -, -, hz⟩ := hH.split z hz
    exact ⟨s, t, u, hz⟩
  | zero => exact ⟨0, 0, 0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨s, t, u, rfl⟩ := hy
    obtain ⟨s', t', u', rfl⟩ := hz
    exact ⟨s + s', t + t', u + u', by rw [Matrix.mulVec_add]; module⟩
  | smul a y _ hy =>
    obtain ⟨s, t, u, rfl⟩ := hy
    exact ⟨a * s, a * t, a • u, by rw [Matrix.mulVec_smul]; module⟩

private theorem conj_mem_unip {W : Spc F E d} {H' : Plane E d d₁} (h : Hyp σ W H') (hxy : form σ W.J H'.x H'.y = 1)
    (hspan : ∀ v : Fin d → E, ∃ (s t : E) (u : Fin d₁ → E), v = s • H'.x + H'.ι *ᵥ u + t • H'.y)
    (p : UA σ W.J) (hp : mat p *ᵥ incV F H'.x = incV F H'.x) (n : UA σ W.J) (hn : n ∈ unip σ W H') :
    p * n * p⁻¹ ∈ unip σ W H' := by
  obtain ⟨hn1, hn2⟩ := StdMat.mem_unip_std σ W H' n hn
  have hp' := mat_inv_fix p hp
  have hm : mat (p * n * p⁻¹) = mat p * mat n * mat p⁻¹ := rfl
  have hyx : hA σ W.J (incV F H'.y) (incV F H'.x) = -1 := by
    rw [StdMat.hA_skew_eq σ W.J h.σσ h.skew, hA_incV, hxy, map_one, map_one]
  refine Subgroup.subset_closure ⟨?_, fun z => ?_⟩
  · rw [hm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hp', hn1, hp]
  · obtain ⟨s, t, z', e⟩ := StdMat.decomp_eq H'.x H'.y H'.ι hspan (mat p⁻¹ *ᵥ (incM F H'.ι *ᵥ z))
    have ht : t = 0 := by
      have h1 : hA σ W.J (mat p⁻¹ *ᵥ (incM F H'.ι *ᵥ z)) (mat p⁻¹ *ᵥ incV F H'.x) = 0 := by
        rw [StdMat.hA_mat_eq, h.ιx]
      rw [hp', e, hA_add_left, hA_add_left, StdMat.hA_smul_l, StdMat.hA_smul_l, h.xx, h.ιx, hyx] at h1
      linear_combination -h1
    rw [ht, zero_smul, add_zero] at e
    obtain ⟨a, ha⟩ := hn2 z'
    refine ⟨a, ?_⟩
    have e2 : mat p *ᵥ (s • incV F H'.x + incM F H'.ι *ᵥ z') = incM F H'.ι *ᵥ z := by
      rw [← e, Matrix.mulVec_mulVec, show mat p * mat p⁻¹ = 1 from Units.mul_inv p.1, Matrix.one_mulVec]
    rw [hm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e, Matrix.mulVec_add, Matrix.mulVec_smul, hn1, ha,
      ← add_assoc, Matrix.mulVec_add, e2, Matrix.mulVec_smul, hp]

open scoped Pointwise in

private theorem cosetReps_unfold {G ι : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] [Countable ι]
    (μ : Measure G) [μ.IsMulLeftInvariant] (Γ P : Subgroup G) [Countable Γ] (hPΓ : P ≤ Γ) (𝓕 : Set G)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (γ : ι → G) (hγ : ∀ i, γ i ∈ Γ) (hu : ∀ δ ∈ Γ, ∃! i, δ * (γ i)⁻¹ ∈ P)
    (Φ : G → ℂ) (hΦ : Measurable Φ) (hlin : ∫⁻ x in 𝓕, ∑' i, ‖Φ (γ i * x)‖ₑ ∂μ < ⊤) :
    ∃ 𝓕P : Set G, IsFundamentalDomain P 𝓕P μ ∧ IntegrableOn Φ 𝓕P μ ∧
      IntegrableOn (fun x => ∑' i, Φ (γ i * x)) 𝓕 μ ∧ ∫ x in 𝓕, ∑' i, Φ (γ i * x) ∂μ = ∫ x in 𝓕P, Φ x ∂μ := by
  have hnm : ∀ i, NullMeasurableSet (γ i • 𝓕) μ := fun i => h𝓕.nullMeasurableSet_smul (⟨γ i, hγ i⟩ : Γ)
  have hdis : ∀ a b : G, a ∈ Γ → b ∈ Γ → a ≠ b → AEDisjoint μ (a • 𝓕) (b • 𝓕) := fun a b ha hb hab =>
    h𝓕.aedisjoint (i := ⟨a, ha⟩) (j := ⟨b, hb⟩) (fun h => hab (congrArg Subtype.val h))
  have hinj : ∀ p ∈ P, ∀ q ∈ P, ∀ i j, p * γ i = q * γ j → i = j := by
    intro p hp q hq i j e
    refine (hu (p * γ i) (mul_mem (hPΓ hp) (hγ i))).unique (by simpa using hp) ?_
    rw [e]; simpa using hq
  have hpw : Pairwise (Function.onFun (AEDisjoint μ) fun i => γ i • 𝓕) := fun i j hij =>
    hdis _ _ (hγ i) (hγ j) fun e => hij (hinj 1 (one_mem _) 1 (one_mem _) i j (by rw [e]))
  have hmeas : ∀ i, Measurable fun x => Φ (γ i * x) := fun i => hΦ.comp (measurable_const_mul _)
  have hl : ∀ i, ∫⁻ x in γ i • 𝓕, ‖Φ x‖ₑ ∂μ = ∫⁻ x in 𝓕, ‖Φ (γ i * x)‖ₑ ∂μ := fun i =>
    ((measurePreserving_mul_left μ (γ i)).setLIntegral_comp_emb (measurableEmbedding_mulLeft (γ i))
      (fun x => ‖Φ x‖ₑ) 𝓕).symm
  have hI : ∀ i, ∫ x in γ i • 𝓕, Φ x ∂μ = ∫ x in 𝓕, Φ (γ i * x) ∂μ := fun i =>
    (measurePreserving_mul_left μ (γ i)).setIntegral_image_emb (measurableEmbedding_mulLeft (γ i)) Φ 𝓕
  have hlin' : ∑' i, ∫⁻ x in 𝓕, ‖Φ (γ i * x)‖ₑ ∂μ < ⊤ := by
    rwa [← lintegral_tsum fun i => (hmeas i).enorm.aemeasurable]
  have hint : IntegrableOn Φ (⋃ i, γ i • 𝓕) μ := by
    refine ⟨hΦ.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_iUnion₀ hnm hpw]
    simpa only [hl] using hlin'
  refine ⟨⋃ i, γ i • 𝓕, ⟨NullMeasurableSet.iUnion hnm, ?_, ?_⟩, hint, ⟨?_, ?_⟩, ?_⟩
  · filter_upwards [h𝓕.ae_covers] with x ⟨g, hg⟩
    obtain ⟨i, hi, -⟩ := hu (g : G)⁻¹ (inv_mem g.2)
    refine ⟨⟨_, inv_mem hi⟩, Set.mem_iUnion.2 ⟨i, (g : G) * x, hg, ?_⟩⟩
    simp [Subgroup.smul_def, mul_assoc]
  · intro p q hpq
    change AEDisjoint μ ((p : G) • ⋃ i, γ i • 𝓕) ((q : G) • ⋃ i, γ i • 𝓕)
    rw [Set.smul_set_iUnion, Set.smul_set_iUnion, AEDisjoint.iUnion_left_iff]
    intro i
    rw [AEDisjoint.iUnion_right_iff]
    intro j
    rw [smul_smul, smul_smul]
    refine hdis _ _ (mul_mem (hPΓ p.2) (hγ i)) (mul_mem (hPΓ q.2) (hγ j)) fun e => hpq ?_
    obtain rfl := hinj p p.2 q q.2 i j e
    exact Subtype.ext (mul_right_cancel e)
  · exact AEStronglyMeasurable.tsum fun i => (hmeas i).aestronglyMeasurable
  · rw [hasFiniteIntegral_iff_enorm]
    exact (lintegral_mono fun x => enorm_tsum_le_tsum_enorm).trans_lt hlin
  · rw [integral_tsum (fun i => (hmeas i).aestronglyMeasurable) hlin'.ne, integral_iUnion_ae hnm hpw hint]
    simp only [hI]

private theorem det_ne_zero_of_cartan (B : Base F E) {n : ℕ} (Y : Spc F E n)
    (h : ∀ w, IsCartan (Complex.I • Y.J.map (B.emb w).1) (Y.θ w)) : Y.J.det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hJv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  let w : InfinitePlace F := Classical.arbitrary _
  let τ : E →+* ℂ := (B.emb w).1
  let M : Matrix (Fin n) (Fin n) ℂ := Complex.I • Y.J.map τ
  let v' : Fin n → ℂ := fun i => τ (v i)
  have hv' : v' ≠ 0 := fun h => hv (funext fun i => τ.injective (by simpa [v'] using congrFun h i))
  have hMv : M *ᵥ v' = 0 := by
    ext i
    have := congrArg τ (congrFun hJv i)
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.zero_apply, map_zero] at this
    simp only [M, v', Matrix.smul_mulVec, Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply, Matrix.smul_apply, mul_assoc, ← Finset.mul_sum, this, mul_zero]
  have hx : star v' ≠ 0 := fun h => hv' (by simpa using congrArg star h)
  have := (h w).2.2 (star v') hx
  rw [star_star] at this
  change 0 < (_ ⬝ᵥ M *ᵥ v').re at this
  rw [hMv, dotProduct_zero, Complex.zero_re] at this
  exact lt_irrefl _ this

end GlobalTheory.CuspConeVanish

set_option maxHeartbeats 1600000 in
open GlobalTheory.UnipMass GlobalTheory.CuspConeVanish in

theorem _root_.GlobalTheory.T.skew_space_fundamental_domain_integral : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r' s' : ℕ),
    B.IsGood σ → W.IsSkew σ B r' s' → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (μ : Measure (UA σ W.J)) (𝓕 : Set (UA σ W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ W.J) 𝓕 μ →
    ∀ f : UA σ W.J → ℂ, Continuous f → (∀ p ∈ ratU σ W.J, ∀ h, f (p * h) = f h) → IsCT H' f 0 →
      (∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖f h‖ * (qht h : ℝ) ^ N ≤ C) →
    ∀ (T : UA σ W.J → ℂ) (γ : {w : Fin d → E // w ≠ 0 ∧ form σ W.J w w = 0} → UA σ W.J),
      Continuous T → (∀ u ∈ unip σ W H', ∀ h, T (u * h) = T h) →
      (∀ p ∈ ratU σ W.J, mat p *ᵥ incV F H'.x = incV F H'.x → ∀ h, T (p * h) = T h) →
      (∀ w, γ w ∈ ratU σ W.J ∧ mat (γ w) *ᵥ incV F w.1 = incV F H'.x) →
      (∀ h, Summable fun w => ‖T (γ w * h)‖) → (∃ (C : ℝ) (k : ℕ), ∀ h, ∑' w, ‖T (γ w * h)‖ ≤ C * (qht h : ℝ) ^ k) →
      IntegrableOn (fun h => f h * (starRingEnd ℂ) (∑' w, T (γ w * h))) 𝓕 μ ∧
        ∫ h in 𝓕, f h * (starRingEnd ℂ) (∑' w, T (γ w * h)) ∂μ = 0 := by
  intro hK F E _ _ _ _ _ σ B d d₁ W W₁ H' i₀ i₁ r' s' hB hW hH μ 𝓕 hμ h𝓕 f hfc hfi hct hdec T γ hTc hTN hTP hγ hsum hbd
  classical
  have hcm := hB.cm
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hcm
  have hspan := span_of_adapted hW hH
  have h : Hyp σ W H' := ⟨hσ, hW.skew, by rw [hA_incV, hH.xx, map_zero],
    StdMat.hA_ι_incV_eq σ W.J H'.ι H'.x fun u => (hH.orth u).1⟩
  have hx0 : H'.x ≠ 0 := fun h0 => by
    have h1 := hH.xy
    rw [h0] at h1
    simp [form] at h1
  obtain ⟨hTG, hLC, hSC, hT2⟩ := topUA σ W.J
  haveI := hTG
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI : BorelSpace (UA σ W.J) := ⟨rfl⟩
  haveI := hμ

  have hd := GlobalTheory.CuspConeVanish.det_ne_zero_of_cartan B W hW.cartan
  obtain ⟨c₀, hc₀, hcs⟩ := GlobalTheory.CMImag.exists_imag_ne_zero F E σ hcm
  have hJ := GlobalTheory.ThKOrthVInt.isHermND_smul_of_skew hσ hW.skew hd hc₀ hcs
  have hfin := GlobalTheory.ThKOrthVInt.measure_fundDom_lt_top_smul hK.siegelSetUnitary hcm hc₀ hJ h𝓕

  have hcl := GlobalTheory.T.unipotent_radical_closed_nonzero F E σ _ _ W H' hx0
  haveI : LocallyCompactSpace (unip σ W H') := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (unip σ W H') :=
    hcl.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  haveI := countable_ratU' σ W.J (unip σ W H')
  haveI := GlobalTheory.T.discrete_rational_points_subgroup F E σ _ W.J (unip σ W H')
  obtain ⟨K, hKc, hcov⟩ := cocompact h hH.xx hH.yy hH.xy hH.orth hspan
  obtain ⟨ν, 𝓕N, hν, h𝓕N, hmass⟩ : ∃ (ν : Measure (unip σ W H')) (𝓕N : Set (unip σ W H')), ν.IsHaarMeasure ∧
      IsFundamentalDomain ((ratU σ W.J).subgroupOf (unip σ W H')) 𝓕N ν ∧ ν 𝓕N = 1 := GlobalTheory.T.cocompact_lattice_unit_covolume _ _ K hKc hcov
  haveI := hν

  set P := ratStab σ W.J H'.x with hP
  have hPle : P ≤ ratU σ W.J := fun p hp => hp.1
  haveI := GlobalTheory.UnitaryVol.countable_ratU σ W.J
  haveI : Countable P := (Subgroup.inclusion_injective hPle).countable
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  have hPN : P.subgroupOf (unip σ W H') = (ratU σ W.J).subgroupOf (unip σ W H') := by
    ext n
    simp only [Subgroup.mem_subgroupOf]
    exact ⟨fun hn => hn.1, fun hn => ⟨hn, (StdMat.mem_unip_std σ W H' n.1 n.2).1⟩⟩
  have hnorm : ∀ p ∈ P, ∀ n ∈ unip σ W H', p * n * p⁻¹ ∈ unip σ W H' := fun p hp n hn =>
    conj_mem_unip h hH.xy hspan p hp.2 n hn
  have hnt : ν 𝓕N ≠ ⊤ := by rw [hmass]; exact ENNReal.one_ne_top

  let Φ : UA σ W.J → ℂ := fun x => f x * (starRingEnd ℂ) (T x)
  have hΦc : Continuous Φ := hfc.mul (Complex.continuous_conj.comp hTc)
  have hΦγ : ∀ w x, Φ (γ w * x) = f x * (starRingEnd ℂ) (T (γ w * x)) := fun w x => by
    simp only [Φ, hfi _ (hγ w).1]
  obtain ⟨C, k, hC⟩ := hbd
  obtain ⟨Cf, hCf⟩ := hdec k
  have hb : ∀ x, ∑' w, ‖Φ (γ w * x)‖ₑ ≤ ENNReal.ofReal (max C 0 * Cf) := by
    intro x
    have e1 : ∀ w, ‖Φ (γ w * x)‖ₑ = ENNReal.ofReal (‖f x‖ * ‖T (γ w * x)‖) := fun w => by
      rw [hΦγ, ← ofReal_norm_eq_enorm, norm_mul, Complex.norm_conj]
    simp only [e1]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun w => by positivity) ((hsum x).mul_left _), tsum_mul_left]
    refine ENNReal.ofReal_le_ofReal ?_
    calc ‖f x‖ * ∑' w, ‖T (γ w * x)‖ ≤ ‖f x‖ * (max C 0 * (qht x : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_left ((hC x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
            (norm_nonneg _)
      _ = max C 0 * (‖f x‖ * (qht x : ℝ) ^ k) := by ring
      _ ≤ max C 0 * Cf := mul_le_mul_of_nonneg_left (hCf x) (le_max_right _ _)
  have hlin : ∫⁻ x in 𝓕, ∑' w, ‖Φ (γ w * x)‖ₑ ∂μ < ⊤ := by
    refine (lintegral_mono hb).trans_lt ?_
    rw [setLIntegral_const]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  obtain ⟨𝓕P, h𝓕P, hI1, hI2, hI3⟩ := cosetReps_unfold μ (ratU σ W.J) P hPle 𝓕 h𝓕 γ
    (fun w => (hγ w).1) (existsUnique_coset hx0 hH.xx γ hγ) Φ hΦc.measurable hlin
  have hsum' : (fun x => ∑' w, Φ (γ w * x)) = fun x => f x * (starRingEnd ℂ) (∑' w, T (γ w * x)) := by
    funext x
    simp only [hΦγ]
    rw [tsum_mul_left, Complex.conj_tsum]
  rw [hsum'] at hI2
  refine ⟨hI2, ?_⟩
  rw [← hsum', hI3]
  have hcomm : Φ = fun x => (starRingEnd ℂ) (T x) * f x := funext fun x => mul_comm _ _
  rw [hcomm] at hI1 ⊢
  exact GlobalTheory.UnfoldNormal.unfold_zero_mean _ μ P (unip σ W H') inferInstance hcl hnorm ν 𝓕N hν (hPN ▸ h𝓕N) hnt
    (fun x => (starRingEnd ℂ) (T x)) f (Complex.continuous_conj.comp hTc).measurable hfc.measurable
    (fun n hn x => by simp only [hTN n hn]) (fun p hp x => by simp only [hTP p hp.1 hp.2])
    (fun p hp x => hfi p hp.1 x) (fun x => (hct ν 𝓕N hν h𝓕N hmass x).symm) 𝓕P h𝓕P hI1
