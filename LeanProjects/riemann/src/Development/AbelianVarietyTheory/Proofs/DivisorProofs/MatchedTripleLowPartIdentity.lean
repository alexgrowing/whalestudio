import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeSocleOverOfSimple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearUpdate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfMemSpanImage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareIntegrabilityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopologyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteTopologyRationalUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaLocalGlobalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaArchimedeanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaExistsDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaFinitePlacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedThetaDescentNonvanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormInvariantQuotientDefiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactOrbitSmoothVectorFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactSubgroupUnitaryPointsSupportedAtPlaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedLocalEvalWeilStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct Topology

noncomputable section

namespace GlobalTheory.ThKExSimpleW

open MeasureTheory
open scoped ComplexConjugate

theorem exsimple : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ N, GlobalTheory.ThetaFac.IsMaxTh B om' (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) N → (∀ Ψ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), G.M'.I om' Ψ = 0 → Ψ ∈ N) → ∀ v : Pl F, ∃ S : Submodule ℂ (GlobalTheory.ThK.Fn F a' (a + a')), S ≤ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) ∧ GlobalTheory.ThKLocSS.IsSimpleOver (GlobalTheory.ThKLocSS.opsAt om' v) N S := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM N hmax hker v
  set D := GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁ with hDdef
  obtain ⟨i1, i2, i3, i4⟩ := GlobalTheory.T.unitary_adelic_group_topology F E σ (a + a') G.W.J
  haveI := i1; haveI := i2; haveI := i3; haveI := i4
  haveI := GlobalTheory.T.discreteTopology_rational_unitary F E σ (a + a') G.W.J
  haveI : BorelSpace (UA σ G.W.J) := ⟨rfl⟩
  obtain ⟨𝓕, h𝓕⟩ := GlobalTheory.FundDomDiscrete.exists_isFundamentalDomain (ratU σ G.W.J) (Measure.haar)
  set μ : Measure (UA σ G.W.J) := Measure.haar with hμdef
  have hμ : μ.IsHaarMeasure := inferInstance
  have lin := GlobalTheory.T.matched_pair_theta_local_global hK F E σ B a a' G X om om' R Rf hM
  have sq := (GlobalTheory.T.square_integrability hK F E σ B a a' G X om om' hM.triple μ 𝓕 hμ h𝓕).2
  have I0 : G.M'.I om' 0 = 0 := by simpa using lin 0 D.zero_mem 0 D.zero_mem 1
  have Iadd : ∀ x ∈ D, ∀ y ∈ D, G.M'.I om' (x + y) = G.M'.I om' x + G.M'.I om' y := by
    intro x hx y hy; simpa using lin x hx y hy 1
  have Ismul : ∀ c : ℂ, ∀ x ∈ D, G.M'.I om' (c • x) = c • G.M'.I om' x := by
    intro c x hx; simpa [I0] using lin 0 D.zero_mem x hx c
  let Bf : GlobalTheory.ThK.Fn F a' (a + a') → GlobalTheory.ThK.Fn F a' (a + a') → ℂ :=
    fun Φ Ψ => ∫ x in 𝓕, G.M'.I om' Φ x * conj (G.M'.I om' Ψ x) ∂μ
  have hint : ∀ Φ ∈ D, ∀ Ψ ∈ D,
      Integrable (fun x => G.M'.I om' Φ x * conj (G.M'.I om' Ψ x)) (μ.restrict 𝓕) := by
    intro Φ hΦ Ψ hΨ
    have e : (fun x => G.M'.I om' Φ x * conj (G.M'.I om' Ψ x)) = fun x =>
        (((‖G.M'.I om' (Φ + (1 : ℂ) • Ψ) x‖ ^ 2 : ℝ) : ℂ) - ((‖G.M'.I om' (Φ + (-1 : ℂ) • Ψ) x‖ ^ 2 : ℝ) : ℂ)
          + Complex.I * ((‖G.M'.I om' (Φ + Complex.I • Ψ) x‖ ^ 2 : ℝ) : ℂ)
          - Complex.I * ((‖G.M'.I om' (Φ + (-Complex.I) • Ψ) x‖ ^ 2 : ℝ) : ℂ)) / 4 := by
      funext x
      rw [lin Φ hΦ Ψ hΨ 1, lin Φ hΦ Ψ hΨ (-1), lin Φ hΦ Ψ hΨ Complex.I, lin Φ hΦ Ψ hΨ (-Complex.I)]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul]
      exact GlobalTheory.ThetaFacCompl.mul_conj_polar _ _
    rw [e]
    have hi : ∀ c : ℂ, Integrable (fun x => ((‖G.M'.I om' (Φ + c • Ψ) x‖ ^ 2 : ℝ) : ℂ)) (μ.restrict 𝓕) :=
      fun c => Integrable.ofReal (sq _ (D.add_mem hΦ (D.smul_mem c hΨ)))
    exact ((((hi 1).sub (hi (-1))).add ((hi Complex.I).const_mul Complex.I)).sub
      ((hi (-Complex.I)).const_mul Complex.I)).div_const 4
  have hself : ∀ Φ, Bf Φ Φ = ((∫ x in 𝓕, ‖G.M'.I om' Φ x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    intro Φ
    simp only [Bf]
    rw [← integral_complex_ofReal]
    congr 1
    funext x
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hadd : ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, Bf (x + y) z = Bf x z + Bf y z := by
    intro x hx y hy z hz
    simp only [Bf, Iadd x hx y hy, Pi.add_apply, add_mul]
    exact integral_add (hint x hx z hz) (hint y hy z hz)
  have hsmul : ∀ c : ℂ, ∀ x ∈ D, ∀ y ∈ D, Bf (c • x) y = c * Bf x y := by
    intro c x hx y _
    simp only [Bf, Ismul c x hx, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul c _
  have hherm : ∀ x ∈ D, ∀ y ∈ D, Bf y x = starRingEnd ℂ (Bf x y) := by
    intro x _ y _
    simp only [Bf]
    rw [← integral_conj]
    congr 1
    funext t
    simp [map_mul, mul_comm]
  have hpos : ∀ x ∈ D, 0 ≤ (Bf x x).re := by
    intro x _
    rw [hself, Complex.ofReal_re]
    exact integral_nonneg fun t => sq_nonneg _
  have hzero : ∀ x ∈ D, Bf x x = 0 → G.M'.I om' x = 0 := by
    intro x hx h0
    apply GlobalTheory.T.matched_pair_theta_archimedean hK F E σ B a a' G X om om' R Rf hM μ 𝓕 hμ h𝓕 x hx
    rw [hself] at h0
    have h0' : ∫ t in 𝓕, ‖G.M'.I om' x t‖ ^ 2 ∂μ = 0 := by exact_mod_cast h0
    have hae := (integral_eq_zero_iff_of_nonneg (fun t => sq_nonneg _) (sq x hx)).1 h0'
    filter_upwards [hae] with t ht
    simpa using ht
  have hstab := GlobalTheory.T.matched_pair_theta_exists_data hK F E σ B a a' G X om om' R Rf hM
  have rinv := GlobalTheory.T.matched_pair_theta_finite_places hK F E σ B a a' G X om om' R Rf hM μ 𝓕 hμ h𝓕
  let ρ : UAtSub σ G.W (evFin F v) →* Module.End ℂ (GlobalTheory.ThK.Fn F a' (a + a')) :=
    (om'.comp (MonoidHom.inr _ _)).comp (UAtSub σ G.W (evFin F v)).subtype
  have hρapp : ∀ g : UAtSub σ G.W (evFin F v), ρ g = om' (1, g.1) := fun g => rfl
  have hinv2 : ∀ x, σ (σ x) = x := GlobalTheory.ThK.Inhab.conj_conj hM.triple.base.cm
  have hD : ∀ g : UAtSub σ G.W (evFin F v), ∀ x ∈ D, ρ g x ∈ D := fun g x hx =>
    hstab.1 v g.1 g.2 x hx
  have hinvB : ∀ g : UAtSub σ G.W (evFin F v), ∀ x ∈ D, ∀ y ∈ D, Bf (ρ g x) (ρ g y) = Bf x y := by
    intro g x hx y hy
    have e1 : G.M'.I om' (ρ g x) = fun t => G.M'.I om' x (t * g.1) :=
      funext fun t => GlobalTheory.ThetaFacCompl.I_transl _ _ _ _ _
    have e2 : G.M'.I om' (ρ g y) = fun t => G.M'.I om' y (t * g.1) :=
      funext fun t => GlobalTheory.ThetaFacCompl.I_transl _ _ _ _ _
    simp only [Bf]
    rw [e1, e2]
    exact rinv x hx y hy g.1

  have hsm : ∀ Φ ∈ D, ∃ U ∈ 𝓝 (1 : UA σ G.W.J), ∀ h ∈ U, h ∈ UAt σ G.W (evFin F v) → om' (1, h) Φ = Φ := by
    intro Φ hΦ
    obtain ⟨L, hL, P, hPΦ, -, -, -, hPfix, -⟩ :=
      GlobalTheory.T.matched_theta_descent_nonvanishing hK F E σ B a a' G X om om' R Rf hM μ 𝓕 hμ h𝓕 ⟨Φ, hΦ⟩
    obtain ⟨U, hUo, hU1, hUL⟩ := hL.2
    refine ⟨U, hUo.mem_nhds hU1, fun h hh hv => ?_⟩
    have hfin : h ∈ GlobalTheory.ThKAdm.FinPt σ G.W := by
      intro u hu
      apply hv u
      show evalV F v (sndA F u) = 0
      have e : sndA F u = u.2 := rfl
      have hu' : u.2 = 0 := hu
      rw [e, hu', map_zero]
    have := hPfix ⟨Φ, hΦ⟩ h (hUL ⟨hh, hfin⟩)
    rw [hPΦ] at this
    exact this
  let 𝒦 : Set (Subgroup (UAtSub σ G.W (evFin F v))) := {K | ∃ K' : Subgroup (UA σ G.W.J),
    K = K'.comap (UAtSub σ G.W (evFin F v)).subtype ∧ (∀ g ∈ K', g ∈ UAt σ G.W (evFin F v)) ∧
    IsCompact (K' : Set (UA σ G.W.J)) ∧ (∃ O : Set (UA σ G.W.J), IsOpen O ∧ (1 : UA σ G.W.J) ∈ O ∧
      ∀ g ∈ O, g ∈ UAt σ G.W (evFin F v) → g ∈ K')}
  obtain ⟨S, hSD, hS⟩ := GlobalTheory.T.hermitian_form_invariant_quotient_definite ρ 𝒦 Bf D N hD hmax.le hmax.ne
    (fun g x hx => hmax.stab.fin v g.1 g.2 x hx) hadd hsmul hherm hpos hinvB
    (fun x hx h0 => hker x hx (hzero x hx h0))
    (by
      intro x hx
      obtain ⟨U, hU, hUx⟩ := hsm x hx
      obtain ⟨K', hK'1, hK'2, hK'3, hK'4⟩ := GlobalTheory.T.exists_compactSubgroup_unitaryPoints_supportedAtPlace hinv2 G.W v U hU
      refine ⟨K'.comap (UAtSub σ G.W (evFin F v)).subtype, ⟨K', rfl, hK'1, hK'2, hK'3⟩, fun k hk => ?_⟩
      exact hUx k.1 (hK'4 hk) k.2)
    (by
      rintro K ⟨K', rfl, hK'1, hK'2, -⟩ x hx
      obtain ⟨U, hU, hUx⟩ := hsm x hx
      have := GlobalTheory.T.compact_orbit_smooth_vector_finite (om'.comp (MonoidHom.inr _ _)) K' hK'2 x ⟨U, hU, fun h hh hk => hUx h hh (hK'1 h hk)⟩
      refine this.subset ?_
      rintro y ⟨k, hk, rfl⟩
      exact ⟨k.1, hk, rfl⟩)
    (by
      rintro K ⟨K', rfl, hK'1, hK'2, hK'3⟩ x hx
      obtain ⟨s, hsD, hs⟩ := GlobalTheory.T.matched_local_eval_weil hK F E σ B a a' G X om om' R Rf hM v K' hK'1 hK'2 hK'3 x hx
      refine ⟨s, hsD, fun y hy hfix => ?_⟩
      obtain ⟨z, hz, hIz⟩ := hs y hy (fun k hk => hfix ⟨k, hK'1 k hk⟩ hk)
      refine ⟨z, hz, ?_⟩
      simp only [Bf, hIz, Pi.zero_apply, zero_mul, integral_zero])
  refine ⟨S, hSD, ?_⟩
  have hT' : Set.range ρ = GlobalTheory.ThKLocSS.opsAt om' v := by
    ext T
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g.1, g.2, rfl⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, hh⟩, rfl⟩
  rwa [← hT']

end GlobalTheory.ThKExSimpleW

end
