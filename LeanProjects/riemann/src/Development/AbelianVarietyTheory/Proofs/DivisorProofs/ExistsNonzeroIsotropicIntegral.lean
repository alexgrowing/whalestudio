import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEvaluationZeroConeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSecondVariableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneEvaluationConstantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilConvergenceOfKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodSchrodingerModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharactersRestrictionEta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentBoundedHeightReductionStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.CTIntegrate

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem lcsc_UA (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    LocallyCompactSpace (UA σ J) ∧ SecondCountableTopology (UA σ J) := by
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → AE F E))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (GL (Fin n) (AE F E)) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AE F E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin n) (AE F E)) := Units.isEmbedding_embedProduct.secondCountableTopology
  have hcA : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have hc : IsClosed (UG (cA σ) (incM F J) : Set (GL (Fin n) (AE F E))) := by
    have hv : Continuous fun g : GL (Fin n) (AE F E) => (g : Matrix (Fin n) (Fin n) (AE F E)) := Units.continuous_val
    exact isClosed_eq (((hv.matrix_transpose.matrix_mul continuous_const).matrix_mul (hv.matrix_map hcA))) continuous_const
  exact ⟨hc.isClosedEmbedding_subtypeVal.locallyCompactSpace, hc.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology⟩

set_option synthInstance.maxHeartbeats 400000 in

theorem fubini_big : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), ∀ (μ : Measure (unip σ G.W H')) (𝓕 : Set (unip σ G.W H')), μ.IsHaarMeasure →
      IsFundamentalDomain ((ratU σ G.W.J).subgroupOf (unip σ G.W H')) 𝓕 μ → μ 𝓕 = 1 → ∀ h : UA σ G.W.J,
      Integrable (fun g => ∫ u in 𝓕, theta om Φ g (u.1 * h) ∂μ) (G.M.μ.restrict G.M.dom) ∧
      ∫ u in 𝓕, G.M.I om Φ (u.1 * h) ∂μ = ∫ g in G.M.dom, ∫ u in 𝓕, theta om Φ g (u.1 * h) ∂μ ∂G.M.μ := by
  intro hK F E _ _ _ _ _ σ B b a' G G₁ H H' hC X om om' hT Φ hΦs μ 𝓕 hμ hF h1 h
  haveI : BorelSpace (UA σ G.V.J) := ⟨rfl⟩
  haveI : BorelSpace (UA σ G.W.J) := ⟨rfl⟩
  obtain ⟨lc1, sc1⟩ := lcsc_UA σ G.V.J
  obtain ⟨lc2, sc2⟩ := lcsc_UA σ G.W.J
  haveI := lc1; haveI := sc1; haveI := lc2; haveI := sc2
  have hP := GlobalTheory.ThK.Inhab.pairV hT
  have hcond : b + 2 + a' + 2 * min (b + 2 - G.p) G.p < 2 * (b + 2) := by
    have e1 := hT.geo.eBig
    have e2 := hC.q0
    omega
  obtain ⟨hW, -⟩ := GlobalTheory.T.weil_convergence_of_kernel hK F E σ B _ _ G.V G.W G.M _ _ om _ _ _ _ hP (Or.inl hcond)
  obtain ⟨hconv, C, k, hbd⟩ := hW Φ hΦs
  obtain ⟨hth, -⟩ := GlobalTheory.T.theta_basic_properties hK.base F E σ B _ _ G.V G.W G.M _ _ om _ _ _ _ hP
  obtain ⟨hcont, hinv, -⟩ := hth Φ hΦs
  obtain ⟨R, hR⟩ := GlobalTheory.T.unipotent_bounded_height_reduction F E σ B _ _ G.W G₁.W H' 0 (b + 1) _ _ hT.base hT.geo.hW hC.hH'
  haveI : (G.M.μ).IsHaarMeasure := hT.geo.hM.haar
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 (by rw [h1]; exact ENNReal.one_ne_top)
  haveI : SigmaCompactSpace (UA σ G.V.J) := inferInstance
  haveI : SigmaFinite G.M.μ := inferInstance
  haveI hs1 : SFinite (G.M.μ.restrict G.M.dom) := inferInstance
  haveI hs2 : SFinite (μ.restrict 𝓕) := inferInstance
  have hfc : Continuous (fun p : UA σ G.V.J × unip σ G.W H' => theta om Φ p.1 (p.2.1 * h)) :=
    hcont.comp (continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).mul continuous_const))
  have hfm := hfc.stronglyMeasurable
  have hC0 : 0 ≤ C := by
    have h0 := (integral_nonneg (μ := G.M.μ.restrict G.M.dom) fun g => norm_nonneg (theta om Φ g 1)).trans (hbd 1)
    have hpos : (0 : ℝ) < (ht (1 : UA σ G.W.J) : ℝ) ^ k :=
      pow_pos (lt_of_lt_of_le zero_lt_one (by exact_mod_cast one_le_heightGL F _)) k
    exact nonneg_of_mul_nonneg_left h0 hpos
  have hbound : ∀ u : unip σ G.W H', ∫ g in G.M.dom, ‖theta om Φ g (u.1 * h)‖ ∂G.M.μ ≤ C * ((R : ℝ) * ht h) ^ k := by
    intro u
    obtain ⟨γ, hγ, hγR⟩ := hR u.1 u.2
    have e : ∀ g, theta om Φ g (u.1 * h) = theta om Φ g ((γ * u.1) * h) := by
      intro g
      have := hinv 1 (one_mem _) γ hγ.1 g (u.1 * h)
      rw [one_mul] at this
      rw [mul_assoc, this]
    simp_rw [e]
    refine (hbd _).trans (mul_le_mul_of_nonneg_left ?_ hC0)
    refine pow_le_pow_left₀ (by positivity) ?_ k
    have := heightGL_mul_le F (γ * u.1).1 h.1
    calc (ht ((γ * u.1) * h) : ℝ) ≤ (ht (γ * u.1) : ℝ) * ht h := by exact_mod_cast this
      _ ≤ R * ht h := mul_le_mul_of_nonneg_right (by exact_mod_cast hγR) (by positivity)
  have hint : Integrable (Function.uncurry fun g (u : unip σ G.W H') => theta om Φ g (u.1 * h))
      ((G.M.μ.restrict G.M.dom).prod (μ.restrict 𝓕)) := by
    refine (integrable_prod_iff' hfm.aestronglyMeasurable).2 ⟨Eventually.of_forall fun u => hconv (u.1 * h), ?_⟩
    refine Integrable.mono' (integrable_const (C * ((R : ℝ) * ht h) ^ k)) ?_ (Eventually.of_forall fun u => ?_)
    · exact (hfm.norm.integral_prod_left (μ := G.M.μ.restrict G.M.dom)).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact hbound u
  refine ⟨hint.integral_prod_left, ?_⟩
  show ∫ u in 𝓕, ∫ g in G.M.dom, theta om Φ g (u.1 * h) ∂G.M.μ ∂μ = _
  exact (integral_integral_swap hint).symm

end GlobalTheory.ThK.CTIntegrate

noncomputable section

namespace GlobalTheory.ThK.CTIntegrate

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem polData_le_schA {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {B : Base F E} {M : Model σ X W}
    (hM : M.IsGood B.ψ) : PolData B M ≤ schA F (Fin n × Fin d) := by
  refine Submodule.span_le.2 ?_
  rintro Φ ⟨f, -, φ, hSB, hv, rfl⟩
  exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB (hv.and hM.std |>.mono fun v h => h.1.trans h.2)

theorem isLevi_one {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} (H' : Plane E d d₁) :
    IsLevi (σ := σ) (W := W) (W₁ := W₁) H' 1 1 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [mat]

end GlobalTheory.ThK.CTIntegrate

open GlobalTheory.ThK.CTIntegrate in

theorem GlobalTheory.ThK.ctBig_integrate : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∃ C₁ : ℂ, C₁ ≠ 0 ∧ ∀ γ : {x : Fin (b + 2) → E // x ≠ 0 ∧ form σ G.V.J x x = 0} → UA σ G.V.J,
      (∀ x, γ x ∈ ratU σ G.V.J ∧ mat (γ x) *ᵥ incV F x.1 = incV F H.x) →
      ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
      ∀ Φ ∈ PolData B G.M, ∃ A₀ : UA σ G.W.J → ℂ, HasLaw G₁.W H' X.β (((b + 2 : ℕ) : ℝ) / 2) A₀ ∧
        IsCT H' (G.M.I om Φ) (fun h => C₁ * ∫ g in G.M.dom, ∑' x, thetaSum F (e (G.M.co.rho B.ψ (shiftA H H' 1) (om (γ x * g, h) Φ))) ∂G.M.μ + A₀ h) := by
  classical
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hc e he
  by_cases hex : ∃ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W)
      (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' ∧ IsTriple B G₁ X om₁ om₁'
  swap
  · refine ⟨1, one_ne_zero, ?_⟩
    intro γ hγ X om om' om₁ om₁' hT hT₁
    exact absurd ⟨X, om, om', om₁, om₁', hT, hT₁⟩ hex
  obtain ⟨X₀, o₀, o₀', o₁, o₁', hT₀, hT₀₁⟩ := hex
  obtain ⟨M₁, hM₁⟩ := GlobalTheory.T.exists_good_schrodinger_model F E σ B hT₀.base (b + 2) (b + a') G.V G₁.W _ _ _ _ hT₀.geo.hV hT₀₁.geo.hW
  let M₂ : Model σ G.V G₁.W := ⟨M₁.co, M₁.vac, G.M.μ, G.M.dom⟩
  have hM₂ : M₂.IsGood B.ψ := ⟨hM₁.rat, hM₁.vac, hM₁.std, hT₀.geo.hM.haar, hT₀.geo.hM.dom⟩
  obtain ⟨e₀, he₀⟩ := ((GlobalTheory.T.theta_evaluation_zero_cone hKP.base).1 F E σ B (b + 2) (b + 2 + a') G.V G.W G.M _ _ o₀ _ _ _ _
    (Inhab.pairV hT₀) (b + a') G.V G₁.W H' 0 (b + 1) M₂ rfl hc.hH' hM₂).1
  obtain ⟨C₀, -, -, hK⟩ := GlobalTheory.T.adapted_plane_evaluation_constant hKP F E σ B (b + 2) (b + 2 + a') (b + a') G.V G.W G₁.W G.M M₂ H' 0 (b + 1)
    hc.hH' hM₂ e₀ he₀
  obtain ⟨C₁, hC₁, hK1⟩ := hK b G₁.V H 0 (b + 1) G₁.M hc.hH hT₀₁.geo.hM e he
  refine ⟨C₁, hC₁, ?_⟩
  intro γ hγ X om om' om₁ om₁' hT hT₁ Φ hΦ
  have hΦs : Φ ∈ schA F _ := polData_le_schA hT.geo.hM hΦ
  have hP := Inhab.pairV hT
  have hP₁ := Inhab.pairV hT₁
  obtain ⟨ω, hω⟩ := GlobalTheory.WeilExGen.exists_isWeil hKP.base F E σ B hT.base (b + 2) (b + a') G.V G₁.W _ _ _ _ hT.geo.hV hT₁.geo.hW M₂ hM₂
    X.β (X.β / X.α) hP.hX hP₁.hW hP.resX hP₁.resW
  have hP₂ : IsPair B M₂ X.β (X.β / X.α) ω (b + 2 - G.p) G.p (b + a' - (G₁.p + G₁.q)) (G₁.p + G₁.q) :=
    { base := hT.base, herm := hT.geo.hV, skew := hT₁.geo.hW, good := hM₂, hX := hP.hX, hW := hP₁.hW,
      resX := hP.resX, resW := hP₁.resW, weil := hω }
  have hmix := GlobalTheory.T.adapted_plane_second_variable hKP.base F E σ B (b + 2) (b + 2 + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hP (b + a')
    G₁.W H' 0 (b + 1) M₂ ω _ _ hc.hH' hP₂ e₀ he₀
  have hpres : ∀ x, om x Φ ∈ schA F _ := fun x => hT.weil.isUSplitting.pres x Φ hΦs
  have hT0 : ∀ g h, thetaSum F (e₀ (om (g, h) Φ)) = theta ω (e₀ (om (1, h) Φ)) g 1 := by
    intro g h
    have := hmix g 1 1 1 (isLevi_one H') 1 (one_mem _) (om (1, h) Φ) (hpres _)
    rw [one_mul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul] at this
    rw [this]
    simp [theta]
  refine ⟨fun h => C₀ * ∫ g in G.M.dom, thetaSum F (e₀ (om (g, h) Φ)) ∂G.M.μ, ?_, ?_⟩
  · intro t m hL h
    have key : ∀ g, thetaSum F (e₀ (om (g, m * h) Φ)) = ((X.β t : ℂ) * (((absE F E t : ℝ) ^ (((b + 2 : ℕ) : ℝ) / 2) : ℝ) : ℂ)) *
        thetaSum F (e₀ (om (g, h) Φ)) := by
      intro g
      have := hmix 1 t 1 m hL 1 (one_mem _) (om (g, h) Φ) (hpres _)
      rw [one_mul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul] at this
      rw [this, Prod.mk_one_one, map_one, Module.End.one_apply]
      simp only [thetaSum, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
      exact tsum_mul_left
    simp only [key, MeasureTheory.integral_const_mul]
    ring
  · intro μ 𝓕 hμ h𝓕 h1 h
    obtain ⟨hint, hswap⟩ := fubini_big hKP F E σ B b a' G G₁ H H' hc X om om' hT Φ hΦs μ 𝓕 hμ h𝓕 h1 h
    have hpt : ∀ g, ∫ u in 𝓕, theta om Φ g (u.1 * h) ∂μ = C₀ * thetaSum F (e₀ (om (g, h) Φ)) +
        C₁ * ∑' x, thetaSum F (e (G.M.co.rho B.ψ (shiftA H H' 1) (om (γ x * g, h) Φ))) := fun g =>
      ((hK1 γ hγ _ _ om _ _ _ _ hP Φ hΦs g).2 μ 𝓕 hμ h𝓕 h1 h).symm
    have hcond : b + a' + 2 * min (b + 2 - G.p) G.p < 2 * (b + 2) ∨ min (b + 2 - G.p) G.p = 0 := by
      left
      have h1 := hT.geo.eBig
      have h2 := hc.q0
      omega
    have hint0 : Integrable (fun g => C₀ * thetaSum F (e₀ (om (g, h) Φ))) (G.M.μ.restrict G.M.dom) := by
      have hcv := ((GlobalTheory.T.weil_convergence_of_kernel hKP F E σ B (b + 2) (b + a') G.V G₁.W M₂ _ _ ω _ _ _ _ hP₂ hcond).1 (e₀ (om (1, h) Φ))
        (he₀.maps _ (hpres (1, h)))).1 1
      simp only [hT0]
      exact hcv.const_mul C₀
    simp only [hpt] at hint
    have hint1 : Integrable (fun g => C₁ * ∑' x, thetaSum F (e (G.M.co.rho B.ψ (shiftA H H' 1) (om (γ x * g, h) Φ))))
        (G.M.μ.restrict G.M.dom) := by
      refine (hint.sub hint0).congr (Eventually.of_forall fun g => ?_)
      simp only [Pi.sub_apply, add_sub_cancel_left]
    show _ = ∫ u in 𝓕, G.M.I om Φ (u.1 * h) ∂μ
    rw [hswap]
    simp only [hpt]
    rw [integral_add hint0 hint1, integral_const_mul, integral_const_mul]
    ring
