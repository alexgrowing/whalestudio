import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralOfLintegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviLiftOfAdaptedPlane
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStabilizerExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundamentalDomainHasSumIntegralCosetReps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFibreEquiv

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

noncomputable section

namespace GlobalTheory.ConeRearr

theorem ht_pos {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {K : Subgroup (UA σ J)} {x : Fin n → E} {hf : UA σ J → ℝ} (hI : GlobalTheory.ConeSmall.IsIwaHt K x hf)
    (hdec : ∀ g, ∃ (p k : UA σ J) (l : (AE F E)ˣ), k ∈ K ∧ mat p *ᵥ incV F x = l.1 • incV F x ∧ g = p * k) (g : UA σ J) :
    0 < hf g := by
  obtain ⟨p, k, l, hk, hp, rfl⟩ := hdec g
  rw [hI p k l hk hp]
  exact absE_pos l

theorem stab_compact (hKP : GlobalTheory.ThK.KP) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {B : Base F E} {n : ℕ} {X : Spc F E n} {r s : ℕ} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s)
    {K : Subgroup (UA σ X.J)} (hK : IsStab B K) : IsCompact (K : Set (UA σ X.J)) := by
  obtain ⟨K', -, -, hK'stab, hK'cpt, -, -⟩ := GlobalTheory.StabHaar.stabEx hKP.base F E σ B n X r s hB hX
  have hKK : K = K' := Subgroup.ext fun g => (hK g).trans (hK'stab g).symm
  rwa [hKK]

theorem pow_comb (x : ℝ) (hx : 0 < x) (a b : ℕ) (s : ℂ) :
    ((x ^ (1 - ((b + 2 : ℕ) : ℝ)) : ℝ) : ℂ) * (((x ^ (((a + (b + 2) : ℕ) : ℝ) / 2) : ℝ) : ℂ) * (x : ℂ) ^ (s + (((b + 2 : ℕ) : ℂ) - 1) / 2)) =
      (x : ℂ) ^ (s + ((a : ℂ) + 1) / 2) := by
  have h0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx.ne'
  rw [Complex.ofReal_cpow hx.le, Complex.ofReal_cpow hx.le, ← Complex.cpow_add _ _ h0, ← Complex.cpow_add _ _ h0]
  congr 1
  push_cast
  ring

theorem hasSum_levi : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ),
    IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure → ∃ c : ℂ, c ≠ 0 ∧
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ Φ' ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))),
    ∀ hf : UA σ G.V'.J → ℝ, GlobalTheory.ConeSmall.IsIwaHt K H.x hf → (∀ g, ∃ (p k : UA σ G.V'.J) (l : (AE F E)ˣ), k ∈ K ∧ mat p *ᵥ incV F H.x = l.1 • incV F H.x ∧ g = p * k) →
    ∀ 𝓓 : Set (UA σ G.V'.J), IsFundamentalDomain (ratStab σ G.V'.J H.x) 𝓓 G.M'.μ → ∀ s : ℂ,
    ∀ mL : Eˣ → UA σ G.V'.J, (∀ ξ, mL ξ ∈ ratU σ G.V'.J ∧ IsLevi (W₁ := G₁.V') H (Units.map (inclR (F := F) (AF F)).toMonoidHom ξ) 1 (mL ξ)) → ∀ h,
    (∀ ξ, IntegrableOn (fun g => ‖thX B G.M' H H' e' om' Φ' (mL ξ * g) h‖ * hf g ^ (s.re + (((b + 2 : ℕ) : ℝ) - 1) / 2)) 𝓓 G.M'.μ) →
    Summable (fun ξ => ∫ g in 𝓓, ‖thX B G.M' H H' e' om' Φ' (mL ξ * g) h‖ * hf g ^ (s.re + (((b + 2 : ℕ) : ℝ) - 1) / 2) ∂G.M'.μ) →
    HasSum (fun ξ => ∫ g in 𝓓, thX B G.M' H H' e' om' Φ' (mL ξ * g) h * (hf g : ℂ) ^ (s + (((b + 2 : ℕ) : ℂ) - 1) / 2) ∂G.M'.μ)
      (c * GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (s + ((a : ℂ) + 1) / 2) h) := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he' K μK μ hK hμK hμ
  by_cases hex : ∃ X om om' om₁ om₁', IsTriple B G X om om' ∧ IsTriple B G₁ X om₁ om₁'
  swap
  · exact ⟨1, one_ne_zero, fun X om om' om₁ om₁' hT hT₁ => (hex ⟨X, om, om', om₁, om₁', hT, hT₁⟩).elim⟩
  obtain ⟨_, _, _, _, _, hT₀, hT₀₁⟩ := hex
  have hB := hT₀.base
  have hV := hT₀.geo.hV'
  have hKc := stab_compact hKP hB hV hK
  choose m hm using GlobalTheory.LeviFrameH.exists_levi_herm F E σ B _ _ G.V' G₁.V' H _ _ _ _ hB hV hC.hH
  let Q : Subgroup (UA σ G.V'.J) := ratU σ G.V'.J ⊓ Subgroup.closure {g : UA σ G.V'.J | mat g *ᵥ incV F H.x = incV F H.x}
  have hQ : ∀ q, q ∈ Q ↔ q ∈ ratU σ G.V'.J ∧ mat q *ᵥ incV F H.x = incV F H.x := fun q =>
    ⟨fun h => ⟨h.1, GlobalTheory.StabNormal.fix_of_mem_closure' _ h.2⟩, fun h => ⟨h.1, Subgroup.subset_closure h.2⟩⟩
  obtain ⟨C, hC0, hI⟩ := integral_iwasawa hB hV hC.hH G.M'.μ G₁.M'.μ G₁.M'.dom hT₀.geo.hM'.haar hT₀₁.geo.hM'.haar
    hT₀₁.geo.hM'.dom K μK μ hK hKc hμK hμ m hm Q hQ
  refine ⟨C, hC0, ?_⟩
  intro X om om' om₁ om₁' hT hT₁ Φ' hΦ hf hIw hdec 𝓓 h𝓓 s mL hmL h hint hsum
  obtain ⟨hTG, hLC, hSC, hT2⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ _ G.V'.J
  haveI : BorelSpace (UA σ G.V'.J) := ⟨rfl⟩
  haveI := hT.geo.hM'.haar
  haveI : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
  haveI : Countable Eˣ := Units.val_injective.countable
  haveI : Countable (ratU σ G.V'.J) := GlobalTheory.QDom.countable_ratU σ G.V'.J
  have hx0 := plane_x_ne hC.hH
  have hΓr : ratStab σ G.V'.J H.x ≤ ratU σ G.V'.J := fun q hq => hq.1
  have hmΓ : ∀ ξ, mL ξ ∈ ratStab σ G.V'.J H.x := fun ξ => ⟨(hmL ξ).1, _, (hmL ξ).2.1⟩
  have hQΓ : Q ≤ ratStab σ G.V'.J H.x := fun q hq => ⟨((hQ q).1 hq).1, 1, by rw [((hQ q).1 hq).2, Units.val_one, one_smul]⟩
  have hcos : ∀ δ ∈ ratStab σ G.V'.J H.x, ∃! ξ, δ * (mL ξ)⁻¹ ∈ Q := by
    rintro δ ⟨hr, l, hl⟩
    obtain ⟨ξ₀, rfl⟩ := rat_eigen hx0 hr hl
    have key : ∀ ξ, mat (δ * (mL ξ)⁻¹) *ᵥ incV F H.x = (inclR (F := F) (AF F) ((ξ⁻¹ * ξ₀ : Eˣ) : E)) • incV F H.x := by
      intro ξ
      rw [GlobalTheory.StabNormal.mat_mul, ← Matrix.mulVec_mulVec, GlobalTheory.ConeSmallMeas.mulVec_inv_of _ _ _ (hmL ξ).2.1,
        Matrix.mulVec_smul, hl, smul_smul, ← map_inv, Units.val_mul, map_mul]
      rfl
    refine ⟨ξ₀, (hQ _).2 ⟨mul_mem hr (inv_mem (hmL ξ₀).1), ?_⟩, fun ξ hξ => ?_⟩
    · rw [key, inv_mul_cancel, Units.val_one, map_one, one_smul]
    · have h1 := ((hQ _).1 hξ).2
      rw [key] at h1
      have h2 : inclR (F := F) (AF F) ((ξ⁻¹ * ξ₀ : Eˣ) : E) = 1 := smul_incV_inj hx0 (by rw [h1, one_smul])
      rw [← map_one (inclR (F := F) (E := E) (AF F))] at h2
      exact inv_mul_eq_one.1 (Units.ext (inclR_inj h2))
  obtain ⟨D₁, hD₁, hX⟩ := GlobalTheory.exists_fundamentalDomain_hasSum_integral_cosetReps G.M'.μ (fun g => (continuous_mul_left g).measurable) (ratStab σ G.V'.J H.x) Q
    (Subgroup.inclusion_injective hΓr).countable hQΓ 𝓓 h𝓓 mL hmΓ hcos
  have hcont : Continuous hf := GlobalTheory.ConeSmallMeas.continuous_ht K hKc H.x hf hIw hdec
  have hnorm : ∀ g, ‖(hf g : ℂ) ^ (s + (((b + 2 : ℕ) : ℂ) - 1) / 2)‖ = hf g ^ (s.re + (((b + 2 : ℕ) : ℝ) - 1) / 2) := by
    intro g
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (ht_pos hIw hdec g)]
    congr 1
    simp
  let f : UA σ G.V'.J → ℂ := fun g => thX B G.M' H H' e' om' Φ' g h * (hf g : ℂ) ^ (s + (((b + 2 : ℕ) : ℂ) - 1) / 2)
  have hfm : Measurable f :=
    (continuous_thX hC he' hT hT₁ hΦ h).measurable.mul ((Complex.measurable_ofReal.comp hcont.measurable).pow_const _)
  have hfL : ∀ ξ g, f (mL ξ * g) = thX B G.M' H H' e' om' Φ' (mL ξ * g) h * (hf g : ℂ) ^ (s + (((b + 2 : ℕ) : ℂ) - 1) / 2) := fun ξ g => by
    simp only [f, ht_rat hx0 hIw hdec (hmΓ ξ)]
  obtain ⟨hiD, hS⟩ := hX f hfm.aestronglyMeasurable (fun ξ => by simpa only [hfL, norm_mul, hnorm] using hint ξ)
    (by simpa only [hfL, norm_mul, hnorm] using hsum)
  have hfN : ∀ u ∈ unip σ G.V' H, ∀ g, f (u * g) = f g := by
    intro u hu g
    have h1 := ht_mul hIw hdec (p := u) (l := 1) (by rw [GlobalTheory.FoldLine.unip_fix _ H u hu, Units.val_one, one_smul]) g
    rw [map_one, NNReal.coe_one, one_mul] at h1
    simp only [f, thX_unip hKP.base hC he' hT hT₁ hΦ hu, h1]
  have hfQ : ∀ q ∈ Q, ∀ g, f (q * g) = f g := by
    intro q hq g
    obtain ⟨γ, hγ, -⟩ := GlobalTheory.T.levi_rational_point_vector_action F E σ B _ _ G.V' G.V' G₁.V' H _ _ _ _ hB hV hV hC.hH m hm q ((hQ q).1 hq).1 ((hQ q).1 hq).2
    have e : q * g = m 1 γ * ((m 1 γ)⁻¹ * q * g) := by group
    have p1 := (GlobalTheory.ThK.Check.isPair_of_isTriple hT₁).2
    have hρ := he'.maps _ (GlobalTheory.HeisSchA.rho_mem_schA G.M' B.ψ hT.base.std (shiftB σ H H' 1) _
      ((IsUWeilPair.isUSplitting hT.weil').pres ((m 1 γ)⁻¹ * q * g, h) _ hΦ))
    have hinv := ((GlobalTheory.T.theta_basic_properties hKP.base F E σ B _ _ _ _ G₁.M' _ _ om₁' _ _ _ _ p1).1 _ hρ).2.1 γ γ.2 1 (one_mem _) 1 1
    simp only [mul_one] at hinv
    have h1 : thX B G.M' H H' e' om' Φ' (q * g) h = thX B G.M' H H' e' om' Φ' g h := by
      rw [e, thX_levi hKP.base hC he' hT hT₁ hΦ (hm 1 γ), hinv,
        ← thX_levi hKP.base hC he' hT hT₁ hΦ (GlobalTheory.ThK.Check.isLevi_one H), one_mul, thX_unip hKP.base hC he' hT hT₁ hΦ hγ]
    simp only [f, h1, ht_rat hx0 hIw hdec (hQΓ hq)]
  rw [hI D₁ hD₁ f hfm hfQ hfN hiD] at hS
  simp only [hfL] at hS
  convert hS using 2
  unfold GlobalTheory.ConeSmall.coneI
  refine integral_congr_ae (Eventually.of_forall fun k => integral_congr_ae (Eventually.of_forall fun l => ?_))
  simp only [f, thX_levi hKP.base hC he' hT hT₁ hΦ (hm l _), hIw _ k.1 l k.2 (hm l _).1]
  rw [integral_mul_const, integral_const_mul, ← pow_comb _ (absE_pos l) a b s]
  unfold Model.I
  ring

theorem rearrangement : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ),
    IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure → ∃ c : ℂ, c ≠ 0 ∧
    ∀ (C₀ : ℂ) γ, IsWitt (σ := σ) (J := G.W.J) H'.x γ →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁,
    (∀ h, IsCT H (fun g => theta om' Φ' g h) fun g => C₀ * ∑' w, termW B G.M' H H' e' om' Φ' γ w g h) →
    ∀ hf : UA σ G.V'.J → ℝ, GlobalTheory.ConeSmall.IsIwaHt K H.x hf → (∀ g, ∃ (p k : UA σ G.V'.J) (l : (AE F E)ˣ), k ∈ K ∧ mat p *ᵥ incV F H.x = l.1 • incV F H.x ∧ g = p * k) →
    ∀ 𝓓 : Set (UA σ G.V'.J), IsFundamentalDomain (ratStab σ G.V'.J H.x) 𝓓 G.M'.μ → ∀ s : ℂ,
    (∀ h, IntegrableOn (fun g => theta om' Φ' g h * (hf g : ℂ) ^ (s + (((b + 2 : ℕ) : ℂ) - 1) / 2)) 𝓓 G.M'.μ) →
    (∀ h, (∀ w, IntegrableOn (fun g => ‖termW B G.M' H H' e' om' Φ' γ w g h‖ * hf g ^ (s.re + (((b + 2 : ℕ) : ℝ) - 1) / 2)) 𝓓 G.M'.μ) ∧
        Summable fun w => ∫ g in 𝓓, ‖termW B G.M' H H' e' om' Φ' γ w g h‖ * hf g ^ (s.re + (((b + 2 : ℕ) : ℝ) - 1) / 2) ∂G.M'.μ) →
    ∀ T : Set (UA σ G.W.J), GlobalTheory.ConeSmallCT.IsReps T H'.x → ∀ h,
      HasSum (fun t : T => C₀ * c * GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (s + ((a : ℂ) + 1) / 2) (t.1 * h))
        (∫ g in 𝓓, theta om' Φ' g h * (hf g : ℂ) ^ (s + (((b + 2 : ℕ) : ℂ) - 1) / 2) ∂G.M'.μ) := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hCfg e' he' K μK μ hK hμK hμ
  obtain ⟨c, hc, hL3⟩ := hasSum_levi hKP F E σ B a b G G₁ H H' hCfg e' he' K μK μ hK hμK hμ
  refine ⟨c, hc, ?_⟩
  intro C₀ γ hγ X om om' om₁ om₁' hT hT₁ Φ' hΦ' hCT hf hI hdec 𝓓 h𝓓 s hInt hClaim T hTr h
  obtain ⟨hClaimI, hClaimS⟩ := hClaim h
  have hΦ := GlobalTheory.ConeMeasV.polData_le_schA hT.geo.hM' hΦ'.1
  obtain ⟨hTG, hLC, hSC, hT2⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ _ G.V'.J
  haveI : BorelSpace (UA σ G.V'.J) := ⟨rfl⟩
  have hhf : Measurable hf :=
    (GlobalTheory.ConeSmallMeas.continuous_ht K (stab_compact hKP hT.base hT.geo.hV' hK) H.x hf hI hdec).measurable
  have hnorm : ∀ g, ‖(hf g : ℂ) ^ (s + (((b + 2 : ℕ) : ℂ) - 1) / 2)‖ = hf g ^ (s.re + (((b + 2 : ℕ) : ℝ) - 1) / 2) := by
    intro g
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (ht_pos hI hdec g)]
    congr 1
    simp
  have hfm : Measurable (fun g => (hf g : ℂ) ^ (s + (((b + 2 : ℕ) : ℂ) - 1) / 2)) :=
    (Complex.measurable_ofReal.comp hhf).pow_const _
  haveI : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
  haveI : Countable (IsoV σ G.W.J) := by unfold IsoV; infer_instance
  have hFint : ∀ w, Integrable (fun g => termW B G.M' H H' e' om' Φ' γ w g h * (hf g : ℂ) ^ (s + (((b + 2 : ℕ) : ℂ) - 1) / 2)) (G.M'.μ.restrict 𝓓) := by
    intro w
    refine Integrable.mono' (hClaimI w) ?_ ?_
    · exact ((continuous_thX hCfg he' hT hT₁ hΦ (γ w * h)).measurable.mul hfm).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun g => ?_)
      rw [norm_mul, hnorm]
  have hFsum : Summable fun w => ∫ g, ‖termW B G.M' H H' e' om' Φ' γ w g h * (hf g : ℂ) ^ (s + (((b + 2 : ℕ) : ℂ) - 1) / 2)‖ ∂(G.M'.μ.restrict 𝓓) := by
    refine hClaimS.congr (fun w => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall (fun g => ?_))
    simp only [norm_mul, hnorm]
  have hS := hasSum_integral_of_summable_integral_norm hFint hFsum
  simp_rw [tsum_mul_right] at hS
  have hTB := (GlobalTheory.T.theta_basic_properties hKP.base F E σ B _ _ _ _ G.M' _ _ om' _ _ _ _ (GlobalTheory.ThK.Check.isPair_of_isTriple hT).2).1 _ hΦ
  have h1 := integral_eq_ct hT.base hT.geo.hV' hCfg.hH G.M'.μ hT.geo.hM'.haar h𝓓 (θ := fun g => theta om' Φ' g h)
    (φ := fun g => (hf g : ℂ) ^ (s + (((b + 2 : ℕ) : ℂ) - 1) / 2)) (hTB.1.comp (continuous_id.prodMk continuous_const)).measurable hfm
    (fun δ hδ g => by simpa only [one_mul] using hTB.2.1 δ hδ 1 (one_mem _) g h)
    (fun δ hδ g => by simp only [ht_rat (plane_x_ne hCfg.hH) hI hdec hδ])
    (fun u hu g => by
      have h1 := ht_mul hI hdec (p := u) (l := 1) (by rw [GlobalTheory.FoldLine.unip_fix _ H u hu, Units.val_one, one_smul]) g
      rw [map_one, NNReal.coe_one, one_mul] at h1
      simp only [h1]) (hInt h) (hCT h)
  simp_rw [mul_assoc] at h1
  rw [integral_const_mul] at h1
  have hex : ∀ w : IsoV σ G.W.J, ∃! t, t ∈ T ∧ ∃ l : (AE F E)ˣ, mat (γ w * t⁻¹) *ᵥ incV F H'.x = l.1 • incV F H'.x :=
    fun w => hTr.2 _ (hγ w).1
  let r : IsoV σ G.W.J → T := fun w => ⟨(hex w).exists.choose, (hex w).exists.choose_spec.1⟩
  have hr : ∀ w (t : T), r w = t ↔ ∃ l : (AE F E)ˣ, mat (γ w * t.1⁻¹) *ᵥ incV F H'.x = l.1 • incV F H'.x := by
    intro w t
    constructor
    · rintro rfl
      exact (hex w).exists.choose_spec.2
    · intro ht
      apply Subtype.ext
      exact (hex w).unique (hex w).exists.choose_spec ⟨t.2, ht⟩
  have hx0 : H'.x ≠ 0 := plane_x_ne hCfg.hH'
  have hxx : form σ G.W.J H'.x H'.x = 0 := hCfg.hH'.xx
  choose mL hmL using GlobalTheory.RatLeviPlane.exists_ratLevi F E σ B _ _ G.V' G₁.V' H _ _ _ _ hT.base hT.geo.hV' hCfg.hH
  have hσσ : ∀ x : E, σ (σ x) = x := GlobalTheory.ThK.Inhab.conj_conj hT.base.cm
  let φ₀ : Eˣ → Eˣ := fun ξ => (Units.map (σ : E →* E) ξ)⁻¹
  have hφ₀ : Function.Involutive φ₀ := fun ξ => Units.ext (by simp [φ₀, hσσ])
  let φ : Eˣ ≃ Eˣ := hφ₀.toPerm
  have hφ : ∀ ξ : Eˣ, σ (φ ξ : Eˣ) * ξ = 1 := fun ξ => by simp [φ, φ₀, hσσ]
  have hfib : ∀ t : T, HasSum (fun w : {w // r w = t} => ∫ g in 𝓓, termW B G.M' H H' e' om' Φ' γ w.1 g h * (hf g : ℂ) ^ (s + (((b + 2 : ℕ) : ℂ) - 1) / 2) ∂G.M'.μ)
      (c * GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (s + ((a : ℂ) + 1) / 2) (t.1 * h)) := by
    intro t
    obtain ⟨κ, hκ⟩ := GlobalTheory.WittFibre.wittFibre_equiv F E σ G.W.J H'.x hx0 hxx γ hγ t.1 (hTr.1 t.2)
    let e1 : {w // r w = t} ≃ {w : IsoV σ G.W.J // ∃ l : (AE F E)ˣ, mat (γ w * t.1⁻¹) *ᵥ incV F H'.x = l.1 • incV F H'.x} :=
      Equiv.subtypeEquivRight (fun w => hr w t)
    let eT : {w // r w = t} ≃ Eˣ := (e1.trans κ).trans φ
    have hterm : ∀ (w : {w // r w = t}) g, termW B G.M' H H' e' om' Φ' γ w.1 g h =
        thX B G.M' H H' e' om' Φ' (mL (eT w) * g) (t.1 * h) := by
      intro w g
      have hp : γ w.1 * t.1⁻¹ ∈ ratU σ G.W.J := mul_mem (hγ w.1).1 (inv_mem (hTr.1 t.2))
      have := thX_rat_right hKP.base hCfg he' hT hT₁ hΦ hp (κ (e1 w)) (φ (κ (e1 w))) (hφ _) (hκ (e1 w)) (hmL _).2 g (t.1 * h)
      rw [show γ w.1 * t.1⁻¹ * (t.1 * h) = γ w.1 * h by group] at this
      exact this
    have hterm' : ∀ ξ g, termW B G.M' H H' e' om' Φ' γ (eT.symm ξ).1 g h =
        thX B G.M' H H' e' om' Φ' (mL ξ * g) (t.1 * h) := by
      intro ξ g
      rw [hterm, Equiv.apply_symm_apply]
    have hIξ : ∀ ξ, IntegrableOn (fun g => ‖thX B G.M' H H' e' om' Φ' (mL ξ * g) (t.1 * h)‖ * hf g ^ (s.re + (((b + 2 : ℕ) : ℝ) - 1) / 2)) 𝓓 G.M'.μ := by
      intro ξ
      have := hClaimI (eT.symm ξ).1
      simp only [hterm'] at this
      exact this
    have hSξ : Summable (fun ξ => ∫ g in 𝓓, ‖thX B G.M' H H' e' om' Φ' (mL ξ * g) (t.1 * h)‖ * hf g ^ (s.re + (((b + 2 : ℕ) : ℝ) - 1) / 2) ∂G.M'.μ) := by
      have := hClaimS.comp_injective (Subtype.val_injective.comp eT.symm.injective)
      simp only [Function.comp_def, hterm'] at this
      exact this
    have hJ := hL3 X om om' om₁ om₁' hT hT₁ Φ' hΦ hf hI hdec 𝓓 h𝓓 s mL hmL (t.1 * h) hIξ hSξ
    have hJ' := (Equiv.hasSum_iff eT).mpr hJ
    convert hJ' using 2 with w
    simp only [Function.comp_apply, hterm]
  have hS' := (Equiv.hasSum_iff (Equiv.sigmaFiberEquiv r)).mpr hS
  have hsig := hS'.sigma (fun t => hfib t)
  rw [h1]
  simpa only [mul_assoc] using hsig.mul_left C₀

end GlobalTheory.ConeRearr

end
