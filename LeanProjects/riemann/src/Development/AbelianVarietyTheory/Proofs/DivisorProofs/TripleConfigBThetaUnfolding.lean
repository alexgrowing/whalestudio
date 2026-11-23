import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStabilizerExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationTripleCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleConfigBThetaIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralIdeleMajorantFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationAuxiliarySpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviLiftOfAdaptedPlaneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarFundamentalDomainParabolicIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawIdentityConfigBFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawIdentityConfigBSecondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawIdentityConfigBThirdStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped ENNReal Pointwise

noncomputable section
namespace GlobalTheory.ConeCover

theorem exists_cover_lintegral_lt_top : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)) (hC : CfgB B G G₁ H H') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (hT : IsTriple B G X om om') (hT₁ : IsTriple B G₁ X om₁ om₁') (V₂ : Spc F E a) (n₁ : ℕ) (X₁ : Spc F E n₁) (H₀ : Plane E a n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ G₁.W) (e₂ : Fn F a (a + (b + 2)) →ₗ[ℂ] Fn F n₁ (a + b)) (hV₂ : (reS G.V V₂).IsHerm σ B (a - G.p) G.p) (hH₀ : H₀.IsAdapted σ B (reS G.V V₂) X₁ j₀ j₁) (hM₂ : M₂.IsGood B.ψ) (hev : IsEv B G.M M₂ H₀.ι H'.ι (isoA H₀ H') e₂) (Φ : Fn F a (a + (b + 2))) (hΦ : Φ ∈ PolData B G.M) (h : UA σ G.W.J) (Q : Subgroup (UA σ G.V.J)) (hQ : ∀ q, q ∈ Q ↔ q ∈ ratU σ G.V.J ∧ mat q *ᵥ incV F H₀.x = incV F H₀.x), ∃ S : Set (UA σ G.V.J), (∀ g : UA σ G.V.J, ∃ q ∈ Q, q * g ∈ S) ∧ ∫⁻ g in S, ‖thetaSum F (e₂ (G.M.co.rho B.ψ (shiftA H₀ H' 1) (om (g, h) Φ)))‖ₑ ∂G.M.μ < ⊤ := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV₂ hH₀ hM₂ hev Φ hΦ h Q hQ
  haveI : BorelSpace (UA σ G.V.J) := ⟨rfl⟩
  haveI : G.M.μ.IsHaarMeasure := hT.geo.hM.haar

  have hQeq : ratU σ G.V.J ⊓ Subgroup.closure {g : UA σ G.V.J | mat g *ᵥ incV F H₀.x = incV F H₀.x} = Q := by
    have hcl : ∀ q ∈ Subgroup.closure {g : UA σ G.V.J | mat g *ᵥ incV F H₀.x = incV F H₀.x},
        mat q *ᵥ incV F H₀.x = incV F H₀.x := by
      intro q hq
      induction hq using Subgroup.closure_induction with
      | mem x hx => exact hx
      | one => show ((1 : Matrix (Fin a) (Fin a) (AE F E))) *ᵥ _ = _; exact Matrix.one_mulVec _
      | mul x y _ _ hx hy =>
          show ((x : GL (Fin a) (AE F E)) * (y : GL (Fin a) (AE F E)) : Matrix (Fin a) (Fin a) (AE F E)) *ᵥ _ = _
          rw [← Matrix.mulVec_mulVec]
          change mat x *ᵥ (mat y *ᵥ incV F H₀.x) = _
          rw [hy, hx]
      | inv x _ hx =>
          have e1 : mat x⁻¹ * mat x = 1 := by
            show (((x⁻¹ : UA σ G.V.J) : GL (Fin a) (AE F E)) : Matrix (Fin a) (Fin a) (AE F E)) *
              ((x : GL (Fin a) (AE F E)) : Matrix (Fin a) (Fin a) (AE F E)) = 1
            rw [Subgroup.coe_inv, Units.inv_mul]
          calc mat x⁻¹ *ᵥ incV F H₀.x = mat x⁻¹ *ᵥ (mat x *ᵥ incV F H₀.x) := by rw [hx]
            _ = incV F H₀.x := by rw [Matrix.mulVec_mulVec, e1, Matrix.one_mulVec]
    ext q
    rw [hQ q, Subgroup.mem_inf]
    exact and_congr_right fun _ => ⟨fun hq => hcl q hq, fun hq => Subgroup.subset_closure hq⟩
  obtain ⟨𝓓, h𝓓'⟩ := GlobalTheory.QDomV.exists_fundamentalDomain_ratStab F E σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ V₂
    n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV₂ hH₀ hM₂ hev
  have h𝓓 : IsFundamentalDomain Q 𝓓 G.M.μ := hQeq ▸ h𝓓'
  set Z : Set (UA σ G.V.J) := {g | ∀ q ∈ Q, q * g ∉ 𝓓} with hZdef
  have hZ : G.M.μ Z = 0 := by
    have hc := h𝓓.ae_covers
    rw [ae_iff] at hc
    refine measure_mono_null (fun g hg => ?_) hc
    simp only [Set.mem_setOf_eq, not_exists]
    intro q hq
    exact hg q.1 q.2 hq
  refine ⟨𝓓 ∪ Z, fun g => ?_, ?_⟩
  · by_cases hg : ∃ q ∈ Q, q * g ∈ 𝓓
    · obtain ⟨q, hq, hqg⟩ := hg
      exact ⟨q, hq, Or.inl hqg⟩
    · push_neg at hg
      exact ⟨1, Q.one_mem, Or.inr (by simpa only [one_mul, hZdef, Set.mem_setOf_eq] using hg)⟩
  set f : UA σ G.V.J → ℝ≥0∞ := fun g => ‖thetaSum F (e₂ (G.M.co.rho B.ψ (shiftA H₀ H' 1) (om (g, h) Φ)))‖ₑ with hfdef
  have hSD : ∫⁻ g in 𝓓 ∪ Z, f g ∂G.M.μ ≤ ∫⁻ g in 𝓓, f g ∂G.M.μ := by
    calc _ ≤ ∫⁻ g in 𝓓, f g ∂G.M.μ + ∫⁻ g in Z, f g ∂G.M.μ := lintegral_union_le _ _ _
      _ = _ := by rw [setLIntegral_measure_zero _ _ hZ, add_zero]

  obtain ⟨K, μK, μ, hK, hKc, hμK, hμ⟩ := GlobalTheory.T.theta_stabilizer_exists hKP.base F E σ B a G.V (a - G.p) G.p hT.base hT.geo.hV
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have hμKfin : μK Set.univ < ⊤ := isCompact_univ.measure_lt_top
  have hlev := fun l g₀ => GlobalTheory.T.exists_levi_lift_of_adapted_plane F E σ B a n₁ (reS G.V V₂) X₁ H₀ (a - G.p) G.p j₀ j₁ hT.base hV₂ hH₀ l g₀
  choose m0 hm0 using hlev
  obtain ⟨m, hm⟩ : ∃ m : (AE F E)ˣ → UA σ X₁.J → UA σ G.V.J, ∀ l g₀, IsLevi (W₁ := X₁) H₀ l g₀ (m l g₀) := ⟨m0, hm0⟩
  obtain ⟨C₁, hC₁, hfold⟩ := GlobalTheory.T.haar_fundamental_domain_parabolic_integral F E σ B a n₁ G.V V₂ X₁ H₀ (a - G.p) G.p j₀ j₁ hT.base hT.geo.hV hV₂ hH₀ G.M.μ M₂.μ M₂.dom
    inferInstance hM₂.haar hM₂.dom K μK μ hK hμK hμ m hm Q hQ
  have hmeas : AEMeasurable f G.M.μ :=
    (GlobalTheory.ConeMeasV.coneTerm_aestronglyMeasurable hKP F E σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV₂ hH₀ hM₂ hev Φ hΦ h).enorm
  have hD := hfold 𝓓 h𝓓 f hmeas
    (fun q hq g => GlobalTheory.T.triple_config_b_theta_integral hKP F E σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV₂ hH₀ hM₂ hev Φ hΦ h Q hQ q hq g)
    (fun u hu g => GlobalTheory.T.seesaw_identity_config_b_first hKP F E σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV₂ hH₀ hM₂ hev Φ hΦ h u hu g)

  obtain ⟨om₂, χX, χW, r, s', r', s'', hP, hW, hlaw⟩ :=
    GlobalTheory.T.seesaw_identity_config_b_second hKP F E σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV₂ hH₀ hM₂ hev Φ hΦ h
  obtain ⟨U, hU, hN⟩ := GlobalTheory.T.seesaw_identity_config_b_third hKP F E σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV₂ hH₀ hM₂ hev Φ hΦ h
    om₂ χX χW r s' r' s'' hP hW K hK
  have hab : b + 10 ≤ a := by have := hT.geo.eBig; have := hC.eq; omega
  set s : ℝ := ((a : ℝ) - b - 2) / 2 with hs_def
  have hs : 1 < s := by
    have : (b : ℝ) + 10 ≤ a := by exact_mod_cast hab
    rw [hs_def]; linarith
  obtain ⟨N, hN'⟩ := GlobalTheory.TateConv.majorant_inv_lintegral_lt_top F E μ hμ s hs U hU
  obtain ⟨C, hCt, hCb⟩ := hN N
  have key : ∀ (k : K) (l : (AE F E)ˣ), ∫⁻ g₀ in M₂.dom, f (m l g₀ * k.1) * ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - (a : ℝ))) ∂M₂.μ ≤
      C * (GlobalTheory.XTermMaj.maj F E N U ((l⁻¹ : (AE F E)ˣ) : AE F E) * ENNReal.ofReal ((absE F E l : ℝ) ^ (-s))) := by
    intro k l
    have hA : 0 < (absE F E l : ℝ) := by
      have h1 : absE F E l * absE F E l⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      have h2 : absE F E l ≠ 0 := fun h0 => by simp [h0] at h1
      exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr h2)
    have hpt : ∀ g₀, f (m l g₀ * k.1) * ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - (a : ℝ))) =
        ‖thetaSum F (om₂ (g₀, 1) (e₂ (G.M.co.rho B.ψ (shiftA H₀ H' l⁻¹) (om (k.1, h) Φ))))‖ₑ *
          ENNReal.ofReal ((absE F E l : ℝ) ^ (-s)) := by
      intro g₀
      rw [hfdef]
      simp only
      rw [hlaw l g₀ (m l g₀) (hm l g₀) k.1, mul_comm (ENNReal.ofReal _) ‖_‖ₑ, mul_assoc,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hA.le _), ← Real.rpow_add hA]
      congr 3
      rw [hs_def]; push_cast; ring
    calc _ = ∫⁻ g₀ in M₂.dom, ‖thetaSum F (om₂ (g₀, 1) (e₂ (G.M.co.rho B.ψ (shiftA H₀ H' l⁻¹) (om (k.1, h) Φ))))‖ₑ *
          ENNReal.ofReal ((absE F E l : ℝ) ^ (-s)) ∂M₂.μ := lintegral_congr fun g₀ => hpt g₀
      _ = (∫⁻ g₀ in M₂.dom, ‖thetaSum F (om₂ (g₀, 1) (e₂ (G.M.co.rho B.ψ (shiftA H₀ H' l⁻¹) (om (k.1, h) Φ))))‖ₑ ∂M₂.μ) *
          ENNReal.ofReal ((absE F E l : ℝ) ^ (-s)) := lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
      _ ≤ (C * GlobalTheory.XTermMaj.maj F E N U ((l⁻¹ : (AE F E)ˣ) : AE F E)) * ENNReal.ofReal ((absE F E l : ℝ) ^ (-s)) := by
          gcongr; exact hCb k.1 k.2 l⁻¹
      _ = _ := mul_assoc _ _ _
  have hI : ∫⁻ k, ∫⁻ l, ∫⁻ g₀ in M₂.dom, f (m l g₀ * k.1) * ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - (a : ℝ))) ∂M₂.μ ∂μ ∂μK < ⊤ := by
    calc _ ≤ ∫⁻ k : K, ∫⁻ l, C * (GlobalTheory.XTermMaj.maj F E N U ((l⁻¹ : (AE F E)ˣ) : AE F E) *
            ENNReal.ofReal ((absE F E l : ℝ) ^ (-s))) ∂μ ∂μK := lintegral_mono fun k => lintegral_mono fun l => key k l
      _ = ∫⁻ k : K, C * ∫⁻ l, GlobalTheory.XTermMaj.maj F E N U ((l⁻¹ : (AE F E)ˣ) : AE F E) *
            ENNReal.ofReal ((absE F E l : ℝ) ^ (-s)) ∂μ ∂μK := by
          congr 1; funext k; exact lintegral_const_mul' C _ hCt
      _ = (C * ∫⁻ l, GlobalTheory.XTermMaj.maj F E N U ((l⁻¹ : (AE F E)ˣ) : AE F E) *
            ENNReal.ofReal ((absE F E l : ℝ) ^ (-s)) ∂μ) * μK Set.univ := lintegral_const _
      _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top hCt.lt_top hN') hμKfin
  exact lt_of_le_of_lt (hSD.trans hD) (ENNReal.mul_lt_top hC₁.lt_top hI)

end GlobalTheory.ConeCover

end
