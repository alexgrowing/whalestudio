import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftLeftInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteTopologyRationalUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfMemSpanImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFundamentalDomainMulRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaArchimedean
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareIntegrabilityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilConvergenceOfKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftInvariantThetaStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct Topology

noncomputable section

namespace GlobalTheory.ThKL2

open MeasureTheory
open scoped ComplexConjugate

theorem l2form : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∃ Bf : GlobalTheory.ThK.Fn F a (a + a') → GlobalTheory.ThK.Fn F a (a + a') → ℂ,
    (∀ Φ ∈ GlobalTheory.ThK.PolData B G.M, ∀ Ψ ∈ GlobalTheory.ThK.PolData B G.M, ∀ Θ ∈ GlobalTheory.ThK.PolData B G.M, Bf (Φ + Ψ) Θ = Bf Φ Θ + Bf Ψ Θ) ∧
    (∀ c : ℂ, ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M, ∀ Ψ ∈ GlobalTheory.ThK.PolData B G.M, Bf (c • Φ) Ψ = c * Bf Φ Ψ) ∧
    (∀ Φ ∈ GlobalTheory.ThK.PolData B G.M, ∀ Ψ ∈ GlobalTheory.ThK.PolData B G.M, Bf Ψ Φ = starRingEnd ℂ (Bf Φ Ψ)) ∧
    (∀ Φ ∈ GlobalTheory.ThK.PolData B G.M, 0 ≤ (Bf Φ Φ).re) ∧
    (∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, ∀ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.W (GlobalTheory.AdelicU.evFin F v), ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M, ∀ Ψ ∈ GlobalTheory.ThK.PolData B G.M,
      Bf (om (1, h) Φ) (om (1, h) Ψ) = Bf Φ Ψ) ∧
    (∀ Φ ∈ GlobalTheory.ThK.PolData B G.M, Bf Φ Φ = 0 ↔ G.M.I om Φ = 0) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' hT
  obtain ⟨i1, i2, i3, i4⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ (a + a') G.W.J
  haveI := i1; haveI := i2; haveI := i3; haveI := i4
  haveI := GlobalTheory.RatUDiscrete.discreteTopology_ratU F E σ (a + a') G.W.J
  haveI : BorelSpace (UA σ G.W.J) := ⟨rfl⟩
  haveI : Countable (ratU σ G.W.J) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨𝓕, h𝓕⟩ := GlobalTheory.FundDomDiscrete.exists_isFundamentalDomain (ratU σ G.W.J) (Measure.haar)
  set μ : Measure (UA σ G.W.J) := Measure.haar with hμdef
  have hμ : μ.IsHaarMeasure := inferInstance
  haveI : μ.IsMulRightInvariant := GlobalTheory.ThetaCplV.isMulRightInvariant_skew hT.base.cm B G.W hT.geo.hW μ
  set D := PolData B G.M with hD
  have hP := GlobalTheory.ThK.Inhab.pairV hT

  have hdim : a + a' + 2 * min (a - G.p) G.p < 2 * a ∨ min (a - G.p) G.p = 0 := by
    left
    have h1 := hT.geo.eBig
    have h2 : min (a - G.p) G.p ≤ G.p := min_le_right _ _
    omega
  have wc := (GlobalTheory.T.weil_convergence_of_kernel hKP F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hP hdim).1
  have pres : ∀ x, ∀ Φ ∈ schA F (Fin a × Fin (a + a')), om x Φ ∈ schA F (Fin a × Fin (a + a')) := fun x Φ hΦ =>
    (IsUWeilPair.isUSplitting hP.weil).pres x Φ hΦ
  have hDS : D ≤ schA F (Fin a × Fin (a + a')) := GlobalTheory.ThKRatInv.polData_le_schA B G.M hT.geo.hM
  have lin : ∀ Φ ∈ D, ∀ Ψ ∈ D, ∀ c : ℂ, G.M.I om (Φ + c • Ψ) = G.M.I om Φ + c • G.M.I om Ψ := by
    intro Φ hΦ Ψ hΨ c
    funext h
    have i1 := (wc Φ (hDS hΦ)).1 h
    have i2 := (wc Ψ (hDS hΨ)).1 h
    have e : ∀ g, theta om (Φ + c • Ψ) g h = theta om Φ g h + c * theta om Ψ g h := fun g => by
      simp only [theta, map_add, map_smul]
      rw [thetaSum_add F (pres _ Φ (hDS hΦ)) ((schA F _).smul_mem c (pres _ Ψ (hDS hΨ))), thetaSum_smul]
    simp only [Model.I, e, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_add i1 (i2.const_mul c), integral_const_mul]
  have sq := (GlobalTheory.T.square_integrability hKP F E σ B a a' G X om om' hT μ 𝓕 hμ h𝓕).1
  have cont := GlobalTheory.T.continuous_left_invariant_theta hKP F E σ B a a' G X om om' hT
  let Bf : Fn F a (a + a') → Fn F a (a + a') → ℂ := fun Φ Ψ => ∫ x in 𝓕, G.M.I om Φ x * conj (G.M.I om Ψ x) ∂μ
  have hint : ∀ Φ ∈ D, ∀ Ψ ∈ D,
      Integrable (fun x => G.M.I om Φ x * conj (G.M.I om Ψ x)) (μ.restrict 𝓕) := by
    intro Φ hΦ Ψ hΨ
    have e : (fun x => G.M.I om Φ x * conj (G.M.I om Ψ x)) = fun x =>
        (((‖G.M.I om (Φ + (1 : ℂ) • Ψ) x‖ ^ 2 : ℝ) : ℂ) - ((‖G.M.I om (Φ + (-1 : ℂ) • Ψ) x‖ ^ 2 : ℝ) : ℂ)
          + Complex.I * ((‖G.M.I om (Φ + Complex.I • Ψ) x‖ ^ 2 : ℝ) : ℂ)
          - Complex.I * ((‖G.M.I om (Φ + (-Complex.I) • Ψ) x‖ ^ 2 : ℝ) : ℂ)) / 4 := by
      funext x
      rw [lin Φ hΦ Ψ hΨ 1, lin Φ hΦ Ψ hΨ (-1), lin Φ hΦ Ψ hΨ Complex.I, lin Φ hΦ Ψ hΨ (-Complex.I)]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul]
      exact GlobalTheory.ThetaFacCompl.mul_conj_polar _ _
    rw [e]
    have hi : ∀ c : ℂ, Integrable (fun x => ((‖G.M.I om (Φ + c • Ψ) x‖ ^ 2 : ℝ) : ℂ)) (μ.restrict 𝓕) :=
      fun c => Integrable.ofReal (sq _ (D.add_mem hΦ (D.smul_mem c hΨ)))
    exact ((((hi 1).sub (hi (-1))).add ((hi Complex.I).const_mul Complex.I)).sub
      ((hi (-Complex.I)).const_mul Complex.I)).div_const 4
  have I0 : G.M.I om 0 = 0 := by simpa using lin 0 D.zero_mem 0 D.zero_mem 1
  have hself : ∀ Φ, Bf Φ Φ = ((∫ x in 𝓕, ‖G.M.I om Φ x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    intro Φ
    simp only [Bf]
    rw [← integral_complex_ofReal]
    congr 1
    funext x
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  refine ⟨Bf, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Φ hΦ Ψ hΨ Θ hΘ
    have e := lin Φ hΦ Ψ hΨ 1
    rw [one_smul, one_smul] at e
    simp only [Bf, e, Pi.add_apply, add_mul]
    exact integral_add (hint Φ hΦ Θ hΘ) (hint Ψ hΨ Θ hΘ)
  · intro c Φ hΦ Ψ hΨ
    have e := lin 0 D.zero_mem Φ hΦ c
    rw [zero_add, I0, zero_add] at e
    simp only [Bf, e, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul c _
  · intro Φ _ Ψ _
    simp only [Bf]
    rw [← integral_conj]
    congr 1
    funext x
    simp [map_mul, mul_comm]
  · intro Φ _
    rw [hself, Complex.ofReal_re]
    exact integral_nonneg fun x => sq_nonneg _
  · intro v h _ Φ hΦ Ψ hΨ
    have hleft : ∀ γ ∈ ratU σ G.W.J, ∀ x,
        G.M.I om Φ (γ * x) * conj (G.M.I om Ψ (γ * x)) = G.M.I om Φ x * conj (G.M.I om Ψ x) := by
      intro γ hγ x
      rw [(cont Φ hΦ).2 γ hγ, (cont Ψ hΨ).2 γ hγ]
    simp only [Bf, GlobalTheory.ThetaFacCompl.I_transl]
    exact GlobalTheory.ThetaCplV.setIntegral_mul_right h𝓕 (fun x => G.M.I om Φ x * conj (G.M.I om Ψ x)) hleft h
  · intro Φ hΦ
    constructor
    · intro h0
      rw [hself] at h0
      have h0' : ∫ x in 𝓕, ‖G.M.I om Φ x‖ ^ 2 ∂μ = 0 := by exact_mod_cast h0
      have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) (sq Φ hΦ)).1 h0'
      apply GlobalTheory.ThetaFacCompl.eq_zero_of_ae_restrict_fd σ G.W.J μ 𝓕 hμ h𝓕 _ (cont Φ hΦ).1 (cont Φ hΦ).2
      filter_upwards [hae] with x hx
      simpa using hx
    · intro h0
      simp [Bf, h0]

end GlobalTheory.ThKL2

end
