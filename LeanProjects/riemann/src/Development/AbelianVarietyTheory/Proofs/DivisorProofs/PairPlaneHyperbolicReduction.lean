import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermNDSmulSkewForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftInvariantDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneDecomposition

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

private theorem plane_span {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a)
    {n d₂ : ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J j i) = J i j) (H : Plane E n d₂) (hn : d₂ + 2 = n)
    (hxx : form σ J H.x H.x = 0) (hyy : form σ J H.y H.y = 0) (hxy : form σ J H.x H.y = 1)
    (ho : ∀ u, form σ J (H.ι *ᵥ u) H.x = 0 ∧ form σ J (H.ι *ᵥ u) H.y = 0) (hi : Function.Injective H.ι.mulVec) :
    ∀ v : Fin n → E, ∃ (s t : E) (u : Fin d₂ → E), v = s • H.x + H.ι *ᵥ u + t • H.y := by
  have hyx : form σ J H.y H.x = 1 := by
    have : form σ J H.y H.x = σ (form σ J H.x H.y) := by
      simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hJ]; ring
    rw [this, hxy, map_one]
  let L : ((E × E) × (Fin d₂ → E)) →ₗ[E] (Fin n → E) :=
    ((LinearMap.toSpanSingleton E _ H.x).coprod (LinearMap.toSpanSingleton E _ H.y)).coprod H.ι.mulVecLin
  have hL : ∀ p, L p = p.1.1 • H.x + H.ι *ᵥ p.2 + p.1.2 • H.y := by
    intro p
    simp only [L, LinearMap.coprod_apply, LinearMap.toSpanSingleton_apply, Matrix.mulVecLin_apply]
    abel
  have hf : ∀ (s t : E) (u : Fin d₂ → E) (w), form σ J (s • H.x + H.ι *ᵥ u + t • H.y) w =
      s * form σ J H.x w + form σ J (H.ι *ᵥ u) w + t * form σ J H.y w := by
    intro s t u w
    simp only [form, add_dotProduct, smul_dotProduct, smul_eq_mul]
  have hinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨⟨s, t⟩, u⟩ h
    rw [hL] at h
    have h1 := hf s t u H.y
    have h2 := hf s t u H.x
    simp only at h
    rw [h, hxy, (ho u).2, hyy] at h1
    rw [h, hxx, (ho u).1, hyx] at h2
    simp only [form, zero_dotProduct, mul_one, mul_zero, add_zero, zero_add] at h1 h2
    subst h1 h2
    simp only [zero_smul, add_zero, zero_add] at h
    have : u = 0 := hi (by rw [h, Matrix.mulVec_zero])
    rw [this]; rfl
  have hsurj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp; omega)).1 hinj
  intro v
  obtain ⟨p, hp⟩ := hsurj v
  exact ⟨p.1.1, p.1.2, p.2, by rw [← hL, hp]⟩

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.pair_plane_hyperbolic_reduction : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (d₂ : ℕ) (H : Plane E n d₂), (d₂ + 2 = n ∧ form σ X.J H.x H.x = 0 ∧ form σ X.J H.y H.y = 0 ∧ form σ X.J H.x H.y = 1 ∧
        (∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
    ∀ f : UA σ W.J → ℂ, Continuous f → (∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖f h‖ * (qht h : ℝ) ^ N ≤ C) →
    ∀ Φ ∈ schA F (Fin n × Fin d),
    ∀ (μ : Measure (UA σ W.J)) (𝓕 : Set (UA σ W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ W.J) 𝓕 μ →
    ∀ (μN : Measure (unip σ X H)) (𝓕N : Set (unip σ X H)), μN.IsHaarMeasure →
      IsFundamentalDomain ((ratU σ X.J).subgroupOf (unip σ X H)) 𝓕N μN → μN 𝓕N = 1 →
    ∀ g : UA σ X.J, Integrable (fun p : unip σ X H × UA σ W.J => f p.2 * (starRingEnd ℂ) (theta om Φ (p.1.1 * g) p.2))
      ((μN.restrict 𝓕N).prod (μ.restrict 𝓕)) := by
  intro hK F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₂ H ⟨hn, hxx, hyy, hxy, ho, hi⟩ f hf hdec Φ hΦ μ 𝓕 hμ h𝓕
    μN 𝓕N hμN h𝓕N hm g
  have hcm := hP.base.cm
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hcm
  obtain ⟨K, hKc, hcov⟩ := GlobalTheory.UnipHermCover.cocompact_herm F E σ hcm n d₂ X H hP.herm.herm hxx hyy hxy ho
    (plane_span σ hσ X.J hP.herm.herm H hn hxx hyy hxy ho hi)
  obtain ⟨hcont, hinv, C, k, hbd⟩ := ((GlobalTheory.T.theta_basic_properties hK.base) F E σ B n d X W M χX χW om r s r' s' hP).1 Φ hΦ
  obtain ⟨tg1, lc1, sc1, -⟩ := GlobalTheory.UnipCT.topFacts σ X.J
  obtain ⟨tg2, lc2, sc2, -⟩ := GlobalTheory.UnipCT.topFacts σ W.J
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  haveI : BorelSpace (UA σ W.J) := ⟨rfl⟩
  have hC0 : 0 ≤ C := by
    have h0 := (norm_nonneg _).trans (hbd 1 1)
    have h1 : (0 : ℝ) < (ht (1 : UA σ X.J) : ℝ) := lt_of_lt_of_le zero_lt_one (by exact_mod_cast one_le_heightGL F _)
    have h2 : (0 : ℝ) < (ht (1 : UA σ W.J) : ℝ) := lt_of_lt_of_le zero_lt_one (by exact_mod_cast one_le_heightGL F _)
    exact nonneg_of_mul_nonneg_left h0 (pow_pos (mul_pos h1 h2) k)
  have hug : Continuous fun u : unip σ X H => u.1 * g := continuous_subtype_val.mul continuous_const
  have hhc : Continuous fun u : unip σ X H => (ht (u.1 * g) : ℝ) :=
    NNReal.continuous_coe.comp ((GlobalTheory.Grow.continuous_heightGL F).comp (continuous_subtype_val.comp hug))
  obtain ⟨A₀, hA₀⟩ := hKc.exists_bound_of_continuousOn hhc.continuousOn
  set A : ℝ := max A₀ 0 with hAdef
  have hA0 : 0 ≤ A := le_max_right _ _
  have hb1 : ∀ (u : unip σ X H) h, ‖theta om Φ (u.1 * g) h‖ ≤ C * A ^ k * (ht h : ℝ) ^ k := by
    intro u h
    obtain ⟨γ, hγ⟩ := hcov u
    have hr : γ.1.1 ∈ ratU σ X.J := Subgroup.mem_subgroupOf.1 γ.2
    have e := hinv γ.1.1 hr 1 (one_mem _) (u.1 * g) h
    rw [one_mul, ← mul_assoc] at e
    have h1 : (ht (γ.1.1 * u.1 * g) : ℝ) ≤ A := ((le_abs_self _).trans (hA₀ _ hγ)).trans (le_max_left _ _)
    rw [← e, mul_assoc C, ← mul_pow]
    refine (hbd _ _).trans (mul_le_mul_of_nonneg_left ?_ hC0)
    gcongr
  have hCA : 0 ≤ C * A ^ k := mul_nonneg hC0 (pow_nonneg hA0 k)
  have hb2 : ∀ (u : unip σ X H) h, ‖theta om Φ (u.1 * g) h‖ ≤ C * A ^ k * (qht h : ℝ) ^ k := by
    intro u h
    have hγ : ∀ γ : ratU σ W.J, ‖theta om Φ (u.1 * g) h‖ ≤ C * A ^ k * ((ht (γ.1 * h) ^ k : ℝ≥0) : ℝ) := by
      intro γ
      have e := hinv 1 (one_mem _) γ.1 γ.2 (u.1 * g) h
      rw [one_mul] at e
      rw [← e, NNReal.coe_pow]
      exact hb1 u _
    have hm : (qht h) ^ k = ⨅ γ : ratU σ W.J, ht (γ.1 * h) ^ k := by
      show (⨅ γ : ratU σ W.J, ht (γ.1 * h)) ^ k = _
      exact Monotone.map_ciInf_of_continuousAt (f := fun x : ℝ≥0 => x ^ k) (continuous_pow k).continuousAt
        (fun x y hxy => pow_le_pow_left₀ (by positivity) hxy k) (OrderBot.bddBelow _)
    have e2 : (qht h : ℝ) ^ k = ⨅ γ : ratU σ W.J, ((ht (γ.1 * h) ^ k : ℝ≥0) : ℝ) := by
      rw [← NNReal.coe_pow, ← NNReal.coe_iInf, hm]
    rw [e2, Real.mul_iInf_of_nonneg hCA]
    exact le_ciInf hγ
  obtain ⟨C₂, hC₂⟩ := hdec k
  obtain ⟨ξ, hξ0, hξ⟩ := GlobalTheory.UnipMassHerm.exists_anti hcm
  have hJ := GlobalTheory.ThK.SqIntHerm.isHermND_smul_map F E σ B d W r' s' hP.skew ξ hξ0 hξ
  have hfin : μ 𝓕 < ⊤ :=
    GlobalTheory.ThKContSmall.measure_fundamental_domain_lt_top hK.siegelSetUnitary hcm hJ _ (GlobalTheory.SiegelSet.ug_eq_hr hσ hξ0) μ hμ 𝓕 h𝓕
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 hfin.ne
  haveI : IsFiniteMeasure (μN.restrict 𝓕N) := isFiniteMeasure_restrict.2 (by rw [hm]; exact ENNReal.one_ne_top)
  have hFc : Continuous fun p : unip σ X H × UA σ W.J => f p.2 * (starRingEnd ℂ) (theta om Φ (p.1.1 * g) p.2) :=
    (hf.comp continuous_snd).mul
      (Complex.continuous_conj.comp (hcont.comp ((hug.comp continuous_fst).prodMk continuous_snd)))
  refine Integrable.mono' (integrable_const (C * A ^ k * C₂)) hFc.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
  rw [norm_mul, Complex.norm_conj]
  calc ‖f p.2‖ * ‖theta om Φ (p.1.1 * g) p.2‖ ≤ ‖f p.2‖ * (C * A ^ k * (qht p.2 : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_left (hb2 _ _) (norm_nonneg _)
    _ = C * A ^ k * (‖f p.2‖ * (qht p.2 : ℝ) ^ k) := by ring
    _ ≤ C * A ^ k * C₂ := mul_le_mul_of_nonneg_left (hC₂ _) hCA
