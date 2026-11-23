import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSecondVariableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilConvergenceOfKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThKFirstV

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem polData_le_schA {σ : E →ₐ[F] E} {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}
    (hM : M.IsGood B.ψ) : PolData B M ≤ schA F (Fin n × Fin d) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, -, φ, hSB, hev, rfl⟩
  exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hev.and hM.std).mono fun v hv => hv.1.trans hv.2)

set_option synthInstance.maxHeartbeats 400000 in

theorem top_UA (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    IsTopologicalGroup (UA σ J) ∧ LocallyCompactSpace (UA σ J) ∧ SecondCountableTopology (UA σ J) := by
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
  exact ⟨inferInstance, hc.isClosedEmbedding_subtypeVal.locallyCompactSpace,
    hc.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology⟩

theorem haar_smul (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (μ μ₁ : Measure (UA σ J)) [μ.IsHaarMeasure]
    [μ₁.IsHaarMeasure] : ∃ c : ℝ≥0, c ≠ 0 ∧ μ = (c : ENNReal) • μ₁ := by
  obtain ⟨h1, h2, h3⟩ := top_UA σ J
  haveI := h1; haveI := h2; haveI := h3
  haveI : BorelSpace (UA σ J) := ⟨rfl⟩
  exact ⟨_, (Measure.haarScalarFactor_pos_of_isHaarMeasure μ μ₁).ne', Measure.isMulLeftInvariant_eq_smul μ μ₁⟩

theorem dom_change (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (μ : Measure (UA σ J)) [μ.IsHaarMeasure]
    {D D' : Set (UA σ J)} (hD : IsFundamentalDomain (ratU σ J) D μ) (hD' : IsFundamentalDomain (ratU σ J) D' μ)
    (f : UA σ J → ℂ) (hf : ∀ γ ∈ ratU σ J, ∀ g, f (γ * g) = f g) :
    (IntegrableOn f D μ ↔ IntegrableOn f D' μ) ∧ ∫ g in D, f g ∂μ = ∫ g in D', f g ∂μ := by
  obtain ⟨h1, -, -⟩ := top_UA σ J
  haveI := h1
  haveI : BorelSpace (UA σ J) := ⟨rfl⟩
  haveI := GlobalTheory.UnitaryVol.countable_ratU σ J
  haveI : MeasurableConstSMul (ratU σ J) (UA σ J) :=
    ⟨fun γ => (continuous_const.mul continuous_id : Continuous fun x : UA σ J => γ.1 * x).measurable⟩
  haveI : SMulInvariantMeasure (ratU σ J) (UA σ J) μ := ⟨fun γ A _ => measure_preimage_mul μ γ.1 A⟩
  have hf' : ∀ (γ : ratU σ J) x, f (γ • x) = f x := fun γ x => hf γ.1 γ.2 x
  exact ⟨hD.integrableOn_iff hD' hf', hD.setIntegral_eq hD' hf'⟩

end GlobalTheory.ThKFirstV

namespace GlobalTheory.ThKFirstV

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem firstV : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b)
    (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' → ∀ e, IsEv B G.M G₁.M 1 H'.ι (iso0 a H') e →
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
      ∀ Φ ∈ PolData B G.M, ∀ h, IntegrableOn (fun g => thetaSum F (e (om (g, h) Φ))) G.M.dom G.M.μ ∧
        ∫ g in G.M.dom, thetaSum F (e (om (g, h) Φ)) ∂G.M.μ = κ * G₁.M.I om₁ (e (om (1, h) Φ)) 1 := by
  intro hK F E _ _ _ _ _ σ B a b G G₁ H H' hC e he
  obtain ⟨p₁, q₁, V₁, V₁', W₁, M₁, M₁'⟩ := G₁
  obtain ⟨hV, hp, -, -, hH'⟩ := hC
  dsimp only at hV hp hH' he ⊢
  subst hV hp
  by_cases hh : G.M.μ.IsHaarMeasure ∧ M₁.μ.IsHaarMeasure
  swap
  · exact ⟨1, one_ne_zero, fun X om om' om₁ om₁' hT hT₁ => (hh ⟨hT.geo.hM.haar, hT₁.geo.hM.haar⟩).elim⟩
  obtain ⟨hh1, hh2⟩ := hh
  obtain ⟨c, hc0, hμ⟩ := haar_smul σ G.V.J G.M.μ M₁.μ
  refine ⟨(c : ℂ), by exact_mod_cast hc0, fun X om om' om₁ om₁' hT hT₁ Φ hΦ h => ?_⟩
  have hP := (Check.isPair_of_isTriple hT).1
  have hP₁ := (Check.isPair_of_isTriple hT₁).1
  have hΦs : Φ ∈ schA F _ := polData_le_schA hT.geo.hM hΦ
  have hΨ : om (1, h) Φ ∈ schA F _ := (IsUWeilPair.isUSplitting hP.weil).pres (1, h) Φ hΦs
  have heΨ : e (om (1, h) Φ) ∈ schA F _ := he.maps _ hΨ

  have hmix : ∀ g, thetaSum F (e (om (g, h) Φ)) = theta om₁ (e (om (1, h) Φ)) g 1 := by
    intro g
    have h1 := GlobalTheory.T.adapted_plane_second_variable hK.base F E σ B a (a + (b + 2)) G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hP (a + b) W₁ H' a
      (a + b + 1) M₁ om₁ _ _ hH' hP₁ e he g 1 1 1 (Check.isLevi_one H') 1 (one_mem _) (om (1, h) Φ) hΨ
    have h2 : om (g, h) Φ = om (g, 1 * 1) (om (1, h) Φ) := by
      rw [← Module.End.mul_apply, ← map_mul]
      simp
    rw [h2, h1]
    simp [theta]
  simp_rw [hmix]

  let M₂ : Model σ G.V W₁ := ⟨M₁.co, M₁.vac, G.M.μ, G.M.dom⟩
  have hP₂ : IsPair B M₂ X.β (X.β / X.α) om₁ (a - G.p) G.p (a + b - (G.p + q₁)) (G.p + q₁) :=
    ⟨hP₁.base, hP₁.herm, hP₁.skew, ⟨hP₁.good.rat, hP₁.good.vac, hP₁.good.std, hP.good.haar, hP.good.dom⟩, hP₁.hX, hP₁.hW,
      hP₁.resX, hP₁.resW, hP₁.weil⟩
  obtain ⟨hW, -⟩ := GlobalTheory.T.weil_convergence_of_kernel hK F E σ B a (a + b) G.V W₁ M₂ X.β (X.β / X.α) om₁ _ _ _ _ hP₂
    (Or.inl (Check.conv_range hT₁.geo))
  have hint : IntegrableOn (fun g => theta om₁ (e (om (1, h) Φ)) g 1) G.M.dom G.M.μ := (hW _ heΨ).1 1
  refine ⟨hint, ?_⟩

  obtain ⟨hth, -⟩ := GlobalTheory.T.theta_basic_properties hK.base F E σ B a (a + b) G.V W₁ M₁ X.β (X.β / X.α) om₁ _ _ _ _ hP₁
  obtain ⟨-, hinv, -⟩ := hth _ heΨ
  have hf : ∀ γ ∈ ratU σ G.V.J, ∀ g, theta om₁ (e (om (1, h) Φ)) (γ * g) 1 = theta om₁ (e (om (1, h) Φ)) g 1 :=
    fun γ hγ g => by simpa using hinv γ hγ 1 (one_mem _) g 1

  have hD₁ : IsFundamentalDomain (ratU σ G.V.J) M₁.dom G.M.μ := by
    have := hT₁.geo.hM.dom
    refine this.mono ?_
    rw [hμ]
    exact Measure.AbsolutelyContinuous.rfl.smul_left _
  rw [(dom_change σ G.V.J G.M.μ hT.geo.hM.dom hD₁ _ hf).2, hμ, Measure.restrict_smul, integral_smul_measure]
  show _ = (c : ℂ) * ∫ g in M₁.dom, theta om₁ (e (om (1, h) Φ)) g 1 ∂M₁.μ
  rw [ENNReal.coe_toReal, Complex.real_smul]

end GlobalTheory.ThKFirstV
