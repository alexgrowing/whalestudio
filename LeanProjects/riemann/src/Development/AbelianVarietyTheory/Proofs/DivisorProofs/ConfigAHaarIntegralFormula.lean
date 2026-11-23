import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAHaarUnfoldingMeasure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviMapContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingExistsDoublingConfigurationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingEigenIntertwinerTripleCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingEigenIntertwinerUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerCompactStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.XTermFubini

theorem mul_eq_one_of_covolume_identity (ν ν' P R Q T : ℂ) (hQ : Q ≠ 0) (hν : ν' = ν) (hR : R * Q = 1) :
    ν * P * T = P * Q * (ν' * R * T) := by
  subst hν
  have : R = Q⁻¹ := eq_inv_of_mul_eq_one_left hR
  subst this
  field_simp

end GlobalTheory.XTermFubini

namespace GlobalTheory.XTermFubini

set_option maxHeartbeats 400000 in

theorem fubini_xTerm : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure → ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Φ ∈ PolData B G.M, ∀ h,
      ∫ k, ∫ l, ∫ g₀ in G₁.M.dom, (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ ((b + 2 - a') / 2) *
          thetaSum F (om₁ (g₀, 1) (e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, h) Φ)))) ∂G₁.M.μ ∂μ ∂μK =
        ∫ g₀ in G₁.M.dom, ∫ k, ∫ l, (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ ((b + 2 - a') / 2) *
          thetaSum F (om₁ (g₀, 1) (e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, h) Φ)))) ∂μ ∂μK ∂G₁.M.μ := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hC K μK μ hK hμK hμ e he X om om' om₁ om₁' hT hT₁ Φ hΦ h
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI := GlobalTheory.IterBochner.isTopologicalRing_AE (F := F) (E := E)
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨eh⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := eh.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := eh.secondCountableTopology
  haveI : T2Space (AE F E) := eh.isEmbedding.t2Space
  haveI : LocallyCompactSpace (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : LocallyCompactSpace (AE F E)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E)ˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  obtain ⟨_, _, _, _⟩ := GlobalTheory.UnipCT.topFacts σ G₁.V.J
  obtain ⟨_, _, _, _⟩ := GlobalTheory.UnipCT.topFacts σ G.V.J
  haveI : BorelSpace (UA σ G₁.V.J) := ⟨rfl⟩
  haveI : BorelSpace (UA σ G.V.J) := ⟨rfl⟩
  haveI := hT₁.geo.hM.haar
  haveI hs0 : SigmaFinite μ := inferInstance
  haveI hs1 : SigmaFinite G₁.M.μ := inferInstance
  haveI : SFinite μ := @instSFiniteOfSigmaFinite _ _ _ hs0
  haveI : SFinite G₁.M.μ := @instSFiniteOfSigmaFinite _ _ _ hs1
  haveI : SFinite (G₁.M.μ.restrict G₁.M.dom) := inferInstance

  have hKc : IsCompact (K : Set (UA σ G.V.J)) :=
    GlobalTheory.T.stabilizer_compact hKP F E σ B (b + 2) G.V (b + 2 - G.p) G.p K hT.base hT.geo.hV hK
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  haveI hKfin : IsFiniteMeasure μK := inferInstance
  haveI : SFinite μK := @instSFiniteOfSigmaFinite _ _ _ (@IsFiniteMeasure.toSigmaFinite _ _ _ hKfin)

  haveI : μ.Regular := inferInstance
  haveI : μ.IsInvInvariant := Measure.IsHaarMeasure.isInvInvariant_of_regular μ

  obtain ⟨m, hm⟩ := GlobalTheory.T.levi_embedding_exists_doubling_configuration F E σ B b a' G G₁ H H' hC hT.base hT.geo hT₁.geo
  have hmc : Continuous fun p : (AE F E)ˣ × UA σ G₁.V.J => m p.1 p.2 :=
    GlobalTheory.LeviSectionCont.continuous_levi_section F E σ B b a' G G₁ H H' hC hT.base hT.geo hT₁.geo m hm
  set F₀ : UA σ G.V.J → ℂ := fun g => thetaSum F (e (G.M.co.rho B.ψ (shiftA H H' 1) (om (g, h) Φ))) with hF₀def
  have hF₀ : Continuous F₀ := GlobalTheory.T.doubling_eigen_intertwiner_triple_compatible F E σ B b a' G G₁ H H' hC e he X om om' om₁ om₁' hT hT₁ Φ hΦ h
  set c : ℝ := ((b + a' : ℕ) : ℝ) / 2 with hcdef
  have hc0 : 0 ≤ c := by positivity
  set w : (AE F E)ˣ → ℂ := fun l =>
    ((absE F E l : ℝ) : ℂ) ^ ((b + 2 - a') / 2) * (((absE F E l : ℝ) ^ c : ℝ) : ℂ) with hwdef
  have hpos : ∀ l : (AE F E)ˣ, 0 < (absE F E l : ℝ) := by
    intro l
    have h1 : absE F E l * absE F E l⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have : absE F E l ≠ 0 := left_ne_zero_of_mul_eq_one h1
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr this)
  have habs : ∀ l : (AE F E)ˣ, (absE F E l⁻¹ : ℝ) = (absE F E l : ℝ)⁻¹ := by
    intro l; rw [map_inv, NNReal.coe_inv]
  have key : ∀ (k : K) (l : (AE F E)ˣ) (g₀ : UA σ G₁.V.J),
      (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ ((b + 2 - a') / 2) *
        thetaSum F (om₁ (g₀, 1) (e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, h) Φ)))) =
      w l * F₀ (m l⁻¹ g₀ * k.1) := by
    intro k l g₀
    have hlaw := GlobalTheory.T.doubling_eigen_intertwiner_unramified hKP F E σ B b a' G G₁ H H' hC e he X om om' om₁ om₁' hT hT₁ Φ hΦ h l⁻¹ g₀ (m l⁻¹ g₀)
      (hm _ _) k.1
    rw [inv_inv] at hlaw
    have hν : ((X.ν l⁻¹ : Circle) : ℂ)⁻¹ = (X.ν l : ℂ) := by rw [map_inv, Circle.coe_inv, inv_inv]
    have hne : ((absE F E l : ℝ) ^ c : ℝ) ≠ 0 := (Real.rpow_pos_of_pos (hpos l) c).ne'
    have hne' : (((absE F E l : ℝ) ^ c : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hne
    have hR : ((((absE F E l⁻¹ : ℝ) ^ (((b + a' : ℕ) : ℝ) / 2) : ℝ)) : ℂ) * (((absE F E l : ℝ) ^ c : ℝ) : ℂ) = 1 := by
      rw [habs l, Real.inv_rpow (hpos l).le, ← Complex.ofReal_mul, inv_mul_cancel₀ hne, Complex.ofReal_one]
    rw [show F₀ (m l⁻¹ g₀ * k.1) = _ from hlaw]
    exact mul_eq_one_of_covolume_identity _ _ _ _ _ _ hne' hν hR
  simp only [key]

  set φ : K → (AE F E)ˣ → UA σ G₁.V.J → ℂ := fun k l g₀ => w l * F₀ (m l⁻¹ g₀ * k.1) with hφdef
  set ν₀ := G₁.M.μ.restrict G₁.M.dom with hν₀
  show ∫ k, ∫ l, ∫ g₀, φ k l g₀ ∂ν₀ ∂μ ∂μK = ∫ g₀, ∫ k, ∫ l, φ k l g₀ ∂μ ∂μK ∂ν₀
  have hA : Continuous fun l : (AE F E)ˣ => (absE F E l : ℝ) :=
    NNReal.continuous_coe.comp GlobalTheory.Doubling.continuous_absE
  have hwc : Continuous w :=
    ((Complex.continuous_ofReal.comp hA).pow _).mul
      (Complex.continuous_ofReal.comp (hA.rpow_const fun _ => Or.inr hc0))
  have hφc : Continuous fun p : K × (AE F E)ˣ × UA σ G₁.V.J => φ p.1 p.2.1 p.2.2 := by
    have hm' : Continuous fun p : K × (AE F E)ˣ × UA σ G₁.V.J => m p.2.1⁻¹ p.2.2 :=
      hmc.comp ((continuous_inv.comp (continuous_fst.comp continuous_snd)).prodMk (continuous_snd.comp continuous_snd))
    exact (hwc.comp (continuous_fst.comp continuous_snd)).mul
      (hF₀.comp (hm'.mul (continuous_subtype_val.comp continuous_fst)))
  have hφm : Measurable fun p : K × (AE F E)ˣ × UA σ G₁.V.J => φ p.1 p.2.1 p.2.2 := hφc.measurable

  set e0 : ℕ := (b + 2 - a') / 2 with he0
  have hexp : (e0 : ℝ) + c = -(1 - ((b + 2 : ℕ) : ℝ)) := by
    have hnat : 2 * e0 + (b + a') = 2 * (b + 1) := by
      obtain ⟨r, hr⟩ := hT₁.geo.even
      have := hT₁.geo.lt
      omega
    have hr : (2 : ℝ) * (e0 : ℝ) + ((b + a' : ℕ) : ℝ) = 2 * ((b : ℝ) + 1) := by exact_mod_cast hnat
    rw [hcdef]; push_cast at hr ⊢; linarith
  have hw : ∀ l : (AE F E)ˣ, ‖w l‖ₑ = ENNReal.ofReal ((absE F E l⁻¹ : ℝ) ^ (1 - ((b + 2 : ℕ) : ℝ))) := by
    intro l
    have hAl := hpos l
    have e1 : w l = ((((absE F E l : ℝ) ^ e0 * (absE F E l : ℝ) ^ c : ℝ)) : ℂ) := by
      rw [hwdef]; push_cast; rfl
    rw [e1, ← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg (by positivity), habs l,
      Real.inv_rpow hAl.le, ← Real.rpow_neg hAl.le, ← Real.rpow_natCast, ← Real.rpow_add hAl, hexp]
  have hconv := GlobalTheory.T.doubling_configuration_levi_integral hKP F E σ B b a' G G₁ H H' hC K μK μ hK hμK hμ m hm e he X om om' om₁ om₁' hT hT₁ Φ hΦ h
  have hfin : ∫⁻ k, ∫⁻ l, ∫⁻ g₀, ‖φ k l g₀‖ₑ ∂ν₀ ∂μ ∂μK < ⊤ := by
    refine lt_of_eq_of_lt ?_ hconv
    refine lintegral_congr fun k => ?_
    rw [← lintegral_inv_eq_self (μ := μ) (fun l => ∫⁻ g₀ in G₁.M.dom, ‖F₀ (m l g₀ * k.1)‖ₑ *
      ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - ((b + 2 : ℕ) : ℝ))) ∂G₁.M.μ)]
    refine lintegral_congr fun l => lintegral_congr fun g₀ => ?_
    simp only [hφdef]
    rw [enorm_mul, mul_comm, hw l]
  have I1 : Integrable (fun p : K × ((AE F E)ˣ × UA σ G₁.V.J) => φ p.1 p.2.1 p.2.2) (μK.prod (μ.prod ν₀)) := by
    refine ⟨hφm.aestronglyMeasurable, ?_⟩
    show ∫⁻ p, ‖φ p.1 p.2.1 p.2.2‖ₑ ∂(μK.prod (μ.prod ν₀)) < ⊤
    rw [lintegral_prod _ hφm.enorm.aemeasurable]
    refine lt_of_eq_of_lt (lintegral_congr fun k => ?_) hfin
    exact lintegral_prod (fun q : (AE F E)ˣ × UA σ G₁.V.J => ‖φ k q.1 q.2‖ₑ)
      ((hφm.comp measurable_prodMk_left).enorm.aemeasurable)
  clear_value φ
  have hsw : Measurable fun q : (K × UA σ G₁.V.J) × (AE F E)ˣ => ((q.1.1, q.2, q.1.2) : K × (AE F E)ˣ × UA σ G₁.V.J) :=
    measurable_fst.fst.prodMk (measurable_snd.prodMk measurable_fst.snd)
  have hm2 : Measurable fun q : (K × UA σ G₁.V.J) × (AE F E)ˣ => φ q.1.1 q.2 q.1.2 := hφm.comp hsw
  have hmx : Measurable fun x : K × UA σ G₁.V.J => ∫⁻ l, ‖φ x.1 l x.2‖ₑ ∂μ :=
    Measurable.lintegral_prod_right' (f := fun q : (K × UA σ G₁.V.J) × (AE F E)ˣ => ‖φ q.1.1 q.2 q.1.2‖ₑ) hm2.enorm
  have L1 : ∫⁻ q, ‖φ q.1.1 q.2 q.1.2‖ₑ ∂((μK.prod ν₀).prod μ) =
      ∫⁻ x : K × UA σ G₁.V.J, ∫⁻ l, ‖φ x.1 l x.2‖ₑ ∂μ ∂(μK.prod ν₀) :=
    lintegral_prod (fun q : (K × UA σ G₁.V.J) × (AE F E)ˣ => ‖φ q.1.1 q.2 q.1.2‖ₑ) hm2.enorm.aemeasurable
  have L2 : ∫⁻ x : K × UA σ G₁.V.J, ∫⁻ l, ‖φ x.1 l x.2‖ₑ ∂μ ∂(μK.prod ν₀) =
      ∫⁻ k, ∫⁻ g₀, ∫⁻ l, ‖φ k l g₀‖ₑ ∂μ ∂ν₀ ∂μK :=
    lintegral_prod (fun x : K × UA σ G₁.V.J => ∫⁻ l, ‖φ x.1 l x.2‖ₑ ∂μ) hmx.aemeasurable
  have L3 : ∀ k : K, ∫⁻ g₀, ∫⁻ l, ‖φ k l g₀‖ₑ ∂μ ∂ν₀ = ∫⁻ l, ∫⁻ g₀, ‖φ k l g₀‖ₑ ∂ν₀ ∂μ := fun k =>
    lintegral_lintegral_swap (f := fun g₀ l => ‖φ k l g₀‖ₑ)
      ((hφm.comp (measurable_const.prodMk (measurable_snd.prodMk measurable_fst) :
        Measurable fun p : UA σ G₁.V.J × (AE F E)ˣ => ((k, p.2, p.1) : K × (AE F E)ˣ × UA σ G₁.V.J))).enorm.aemeasurable)
  have I2 : Integrable (fun q : (K × UA σ G₁.V.J) × (AE F E)ˣ => φ q.1.1 q.2 q.1.2) ((μK.prod ν₀).prod μ) := by
    refine ⟨hm2.aestronglyMeasurable, ?_⟩
    have : ∫⁻ q, ‖φ q.1.1 q.2 q.1.2‖ₑ ∂((μK.prod ν₀).prod μ) < ⊤ := by
      rw [L1, L2]
      exact lt_of_eq_of_lt (lintegral_congr L3) hfin
    exact this
  have A : ∀ᵐ k ∂μK, ∫ l, ∫ g₀, φ k l g₀ ∂ν₀ ∂μ = ∫ g₀, ∫ l, φ k l g₀ ∂μ ∂ν₀ := by
    filter_upwards [I1.prod_right_ae] with k hk
    exact integral_integral_swap hk
  exact (integral_congr_ae A).trans
    (integral_integral_swap (f := fun k g₀ => ∫ l, φ k l g₀ ∂μ) I2.integral_prod_left)

end GlobalTheory.XTermFubini
