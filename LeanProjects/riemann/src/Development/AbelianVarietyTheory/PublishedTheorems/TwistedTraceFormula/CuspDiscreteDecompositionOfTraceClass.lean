import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsClosedEmbeddingOfLocallyCompact
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonarchimedeanGroupOfIsCompactIsOpen
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMapInfFinEquivEqProd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompOfIsTraceClass

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.Cusp GlobalTheory.AutMult GlobalTheory.DiscreteSum GlobalTheory.Orb GlobalTheory.AdelicU GlobalTheory.SplitWeil
open scoped Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

namespace Published

def CuspTraceClass : Prop :=
  ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant],
    ∀ f ∈ CcGA V, IsTraceClass (RcuspOp V μ f)

def CuspDiscreteDecomposition : Prop :=
  ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], IsDiscreteSum (Rcusp V μ)

end Published

namespace CuspSpectrum

section General

theorem isDiscreteSum_of_repOp {G K : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] {ρ : G →* (K →L[ℂ] K)} (hρ : IsUnitaryRep ρ)
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (h : ∀ v ≠ 0, ∃ f : G → ℂ, Continuous f ∧ HasCompactSupport f ∧
      IsCompactOperator (repOp ρ μ f) ∧ repOp ρ μ f v ≠ 0) : IsDiscreteSum ρ :=
  EnoughCompact.isDiscreteSum hρ fun v hv =>
    let ⟨_, h1, h2, h3, h4⟩ := h v hv
    ⟨_, h3, fun S hS x => (DFunLike.congr_fun (hρ.comp_repOp hρ h1 h2 S hS.2) x).symm, h4⟩

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem exists_isCompact_isOpen {N : Set (GFin σ J)} (hN : N ∈ 𝓝 1) :
    ∃ U : Set (GFin σ J), IsOpen U ∧ IsCompact U ∧ 1 ∈ U ∧ U ⊆ N := by
  have := GlobalTheory.Doubling.totallyDisconnectedSpace_GFin σ J
  obtain ⟨K, hK, hKN, hc⟩ := local_compact_nhds hN
  obtain ⟨U, hU, h1, hUK⟩ := loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.1 hK
  exact ⟨U, hU.2, hc.of_isClosed_subset hU.1 hUK, h1, hUK.trans hKN⟩

theorem exists_bump_ccAd (h : IsCMExt F E σ) {N : Set (GAd σ J)} (hN : N ∈ 𝓝 1) :
    ∃ φ : GAd σ J → ℝ, (fun g => (φ g : ℂ)) ∈ CcAd σ J ∧ 0 ≤ φ ∧ φ 1 = 1 ∧ Function.support φ ⊆ N := by
  classical
  have h1 : (infFinEquiv σ J).symm ⁻¹' N ∈ 𝓝 ((1, 1) : GInf σ J × GFin σ J) :=
    (map_continuous (infFinEquiv σ J).symm).continuousAt.preimage_mem_nhds
      ((map_one (infFinEquiv σ J).symm).symm ▸ hN :)
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.1 h1
  obtain ⟨a, ha, a1, a0, hs⟩ := exists_bump (SmoothFactor.isEmbedding_infMat J h).isInducing hA
  obtain ⟨U, ho, hc, hU, hUB⟩ := exists_isCompact_isOpen hB
  refine ⟨fun g => a (projInf σ J g) * U.indicator 1 (projFin σ J g), ?_,
    fun g => mul_nonneg (a0 _).1 (indicator_nonneg (fun _ _ => zero_le_one) _), by simp [a1, hU], fun g hg => ?_⟩
  · convert infFin_mem_ccAd ((SmoothFactor.ccInf_eq σ J).ge ha) (indicator_mem_SB ho hc) using 1
    funext g
    by_cases hg : projFin σ J g ∈ U <;> simp [infFin, hg]
  · rw [← (infFinEquiv σ J).symm_apply_apply g]
    exact hAB ⟨hs (subset_tsupport _ (left_ne_zero_of_mul hg)),
      hUB (mem_of_indicator_ne_zero (right_ne_zero_of_mul hg))⟩

theorem mem_span_conv (hDM : Published.DixmierMalliavinFactorisation) (h : IsCMExt F E σ) (μ : Measure (GAd σ J))
    [μ.IsHaarMeasure] : CcAd σ J ≤ Submodule.span ℂ {f | ∃ g ∈ CcAd σ J, ∃ g' ∈ CcAd σ J, f = conv μ g g'} := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, ha, b, hb, rfl⟩
  obtain ⟨μa, μf, _, _, e⟩ := exists_map_infFinEquiv_eq_prod μ
  obtain ⟨m, g, g', hg, rfl⟩ := SmoothFactor.exists_sum_conv_ccInf J hDM h μa univ_mem ha
  obtain ⟨K, hK, hKb⟩ := exists_biinvariant hb
  obtain ⟨U, ho, hc, hU, hUK⟩ := exists_isCompact_isOpen (hK.mem_nhds K.one_mem)
  have h0 : (μf.real U : ℂ) ≠ 0 := by
    exact_mod_cast ENNReal.toReal_ne_zero.2 ⟨(ho.measure_pos _ ⟨1, hU⟩).ne', hc.measure_ne_top⟩
  have h1 : conv μf (U.indicator 1) b = (μf.real U : ℂ) • b := by
    funext y
    have : ∀ x, U.indicator (1 : GFin σ J → ℂ) x * b (x⁻¹ * y) = U.indicator (fun _ => b y) x := fun x => by
      by_cases hx : x ∈ U
      · simp [hx, (hKb _ (K.inv_mem (hUK hx)) y).1]
      · simp [hx]
    rw [conv, integral_congr_ae (.of_forall this), integral_indicator_const _ ho.measurableSet]
    simp
  have h2 : infFin σ J (∑ i, conv μa (g i) (g' i)) b =
      ∑ i, (μf.real U : ℂ)⁻¹ • conv μ (infFin σ J (g i) (U.indicator 1)) (infFin σ J (g' i) b) := by
    funext x
    simp [conv_infFin e, h1, infFin, Finset.sum_mul, mul_left_comm _ (μf.real U : ℂ), h0]
  rw [h2]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span
    ⟨_, infFin_mem_ccAd (hg i).1 (indicator_mem_SB ho hc), _, infFin_mem_ccAd (hg i).2.1 hb, rfl⟩)

end General

variable {D : D7} {V : HSp D} {μ : Measure (GA D V)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

theorem isRepOp_RcuspOp {f : GA D V → ℂ} (hf : f ∈ CcGA V) : IsRepOp (Rcusp V μ) μ f (RcuspOp V μ f) :=
  (isUnitaryRep_Rcusp V μ).isRepOp (continuous_of_mem_ccAd hf).1 (continuous_of_mem_ccAd hf).2

theorem exists_RcuspOp_ne_zero {v : L2cusp V μ} (hv : v ≠ 0) : ∃ f ∈ CcGA V, RcuspOp V μ f v ≠ 0 := by
  obtain ⟨N, hN, h⟩ := exists_nhds_repOp_ne_zero μ (isUnitaryRep_Rcusp V μ) hv
  obtain ⟨φ, hφ, h0, h1, hs⟩ := exists_bump_ccAd (isCMExt_host D) hN
  have hc := continuous_of_mem_ccAd hφ
  exact ⟨_, hφ, h φ (Complex.continuous_re.comp hc.1) (hc.2.comp_left (g := Complex.re) rfl) h0
    (h1 ▸ one_ne_zero) hs⟩

theorem isDiscreteSum_of_compact (h : ∀ f ∈ CcGA V, IsCompactOperator (RcuspOp V μ f)) : IsDiscreteSum (Rcusp V μ) := by
  refine isDiscreteSum_of_repOp (isUnitaryRep_Rcusp V μ) μ fun v hv => ?_
  obtain ⟨f, hf, h0⟩ := exists_RcuspOp_ne_zero hv
  exact ⟨f, (continuous_of_mem_ccAd hf).1, (continuous_of_mem_ccAd hf).2, h f hf, h0⟩

theorem isTraceClass_of_isHilbertSchmidt (hDM : Published.DixmierMalliavinFactorisation)
    (h : ∀ f ∈ CcGA V, IsHilbertSchmidt (RcuspOp V μ f)) {f : GA D V → ℂ} (hf : f ∈ CcGA V) :
    IsTraceClass (RcuspOp V μ f) := by
  have hu := isUnitaryRep_Rcusp V μ
  suffices f ∈ CcGA V ∧ IsTraceClass (RcuspOp V μ f) from this.2
  refine Submodule.span_induction (p := fun f _ => f ∈ CcGA V ∧ IsTraceClass (RcuspOp V μ f)) ?_ ?_ ?_ ?_
    (mem_span_conv hDM (isCMExt_host D) μ hf)
  · rintro _ ⟨g, hg, g', hg', rfl⟩
    have c := continuous_of_mem_ccAd hg
    have c' := continuous_of_mem_ccAd hg'
    refine ⟨conv_mem_ccAd μ hg hg', ?_⟩
    rw [show RcuspOp V μ (conv μ g g') = _ from (hu.repOp_convolution (μ := μ) c.1 c.2 c'.1 c'.2).repOp_eq]
    exact (h g hg).isTraceClass_comp (h g' hg')
  · refine ⟨zero_mem _, ?_⟩
    rw [RcuspOp, IsRepOp.repOp_eq (T := 0) fun v => by simp]
    exact isTraceClass_zero
  · rintro g g' - - ⟨hg, t⟩ ⟨hg', t'⟩
    have c := continuous_of_mem_ccAd hg
    have c' := continuous_of_mem_ccAd hg'
    exact ⟨add_mem hg hg', by rw [RcuspOp, hu.repOp_add c.1 c.2 c'.1 c'.2]; exact t.add t'⟩
  · rintro a g - ⟨hg, t⟩
    have c := continuous_of_mem_ccAd hg
    exact ⟨Submodule.smul_mem _ a hg, by rw [RcuspOp, hu.repOp_smul c.1 c.2 a]; exact t.smul a⟩

theorem L2cusp_le_L2disc (h : IsDiscreteSum (Rcusp V μ)) : L2cusp V μ ≤ L2discG V μ := fun F hF => by
  have hW := isSubrep_L2cusp V μ
  refine (h.disc_eq_top.ge.trans (disc_le (U := (L2discG V μ).comap (L2cusp V μ).subtype)
    ((isSubrep_disc (π := RG V μ)).1.preimage continuous_subtype_val) fun X hX => ?_) : ⊤ ≤ _)
    (Submodule.mem_top (x := ⟨F, hF⟩))
  refine Submodule.map_le_iff_le_comap.1 (IsIrredSubrep.le_disc ⟨hW.isSubrep_rep_iff.1 hX.1,
    fun e => hX.2.1 (Submodule.map_injective_of_injective (Submodule.injective_subtype _) (e.trans (Submodule.map_bot _).symm)), fun U hU hs => ?_⟩)
  have e : (U.comap (L2cusp V μ).subtype).map (L2cusp V μ).subtype = U :=
    Submodule.map_comap_eq_self (hU.trans (LinearMap.map_le_range))
  rcases hX.2.2 (U.comap (L2cusp V μ).subtype) ((Submodule.comap_mono hU).trans
    (Submodule.comap_map_eq_of_injective (Submodule.injective_subtype _) X).le)
    (hW.isSubrep_rep_iff.2 (e.symm ▸ hs)) with h0 | h0
  · exact .inl (by rw [← e, h0, Submodule.map_bot])
  · exact .inr (by rw [← e, h0])

theorem multIn_L2cusp_lt (h : IsDiscreteSum (Rcusp V μ)) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {π : GA D V →* (H →L[ℂ] H)} (hπ : IsIrrUnitary π) : multIn π (RG V μ) (L2cusp V μ) < Cardinal.aleph0 :=
  multIn_rep (π := π) (isSubrep_L2cusp V μ) ▸ h.2 ⟨H, π, hπ⟩

theorem traceIsDiagonal (hP : Published.CuspTraceClass) {f : GA D V → ℂ} (hf : f ∈ CcGA V)
    (h : IndefiniteRowSideFullHecke.TraceKernelDecomposition.MapsIntoCusp V μ (starFn f)) :
    IndefiniteRowSideFullHecke.TraceKernelDecomposition.TraceIsDiagonal (ν := autMeasure V μ) (RopG V μ f) (kernelQ (GQ V) f) :=
  have c := continuous_of_mem_ccAd hf
  TraceDiagonal.traceIsDiagonal_Rop c.1 c.2 (by
    change IsTraceClass (RopG V μ f)
    rw [TraceDiagonal.RopG_eq_comp c.1 c.2 h]
    exact (hP D V μ f hf).comp_comp _ _)

end CuspSpectrum

theorem Published.cuspDiscreteDecomposition_of_traceClass (h : Published.CuspTraceClass) : Published.CuspDiscreteDecomposition :=
  fun D V μ _ _ => CuspSpectrum.isDiscreteSum_of_compact fun f hf =>
    isCompactOperator_of_isHilbertSchmidt (h D V μ f hf).isHilbertSchmidt

end GlobalTheory

end
