import Mathlib
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.MetricStatements.ExistsFlagModelBaseMetric
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.RootOnFund
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsTwistedGeneratorsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameViaTwistedGeneratorsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptIsVectorBundleRankStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptBasesLinearIndependentSpanStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlkFProperStepInjectiveBlockDiagStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GMatIsGenericFlagStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DetFacGMatEqOneStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartYvEqAlgebraMapXbStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.YvEqSumMinorsGMatStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsNonzeroXbOfLeftInverseStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameChangeDeterminantStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameChangeRegularStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameMinorValuationStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameOrderBoundStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameUnitCriterionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameGenericRankStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameLeadingTermStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameDegreeFormulaStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptBaseChangeCompatibleStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameDivisorFormulaStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameHeightFormulaStatement

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

noncomputable section

theorem GlobalTheory.CompanionTheory.Ar.PB.FMX.flagModelExists : GlobalTheory.CompanionTheory.Ar.Top.Given → PB.FlagModelExists := by
  intro _ E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 nd d bW bO hv hd
  classical
  have hVB := GlobalTheory.T.hodgeCpt_isVectorBundle_rank E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐
  have hcc := GlobalTheory.T.hodgeCpt_bases_linearIndependent_span E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO
  have hg : ∀ s, ∃ (m n : ℕ) (φ : Fin n → Module.Dual Ω (EE 𝔐)), IsTwistGen 𝔐.ξ (seg x₀) (LL 𝔐 s) m φ := fun s =>
    GlobalTheory.T.exists_twisted_generators 𝔐.X Ω 𝔐.ξ (EE 𝔐) ((k : K₀) → J₀ k) (seg x₀) (LL 𝔐 s) _ (VV 𝔐 s) 𝔐.tie 𝔐.all (hVB s)
  choose m n φ hφ using hg
  have hB : ∀ s, ∃ B : Matrix (Fin (rk (CMType H) D.p D.q s)) (Fin (n s)) Ω, B * aOf 𝔐 bW bO φ s = 1 := fun s =>
    GlobalTheory.T.frame_via_twisted_generators 𝔐.X Ω 𝔐.ξ (EE 𝔐) _ (seg x₀) (LL 𝔐 s) _ (VV 𝔐 s) (m s) (n s) (φ s) (cc 𝔐 bW bO s) 𝔐.tie (hVB s)
      (hφ s) (hcc s).1 (hcc s).2
  have hF : FormsOK 𝔐 bW bO m φ := ⟨hVB, hcc, hφ, hB⟩
  have hx₀ : ∀ k, ∃ i, x₀ ⟨k, i⟩ ≠ 0 := by
    obtain ⟨c₀, hc₀⟩ := exists_inBlockChart 𝔐.tie ⟨genPt 𝔐.ξ, specializes_refl _⟩
    exact fun k => ⟨c₀ k, (hc₀ k).1⟩
  have ht := GlobalTheory.T.hodgeCpt_frame_change_determinant E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ hF
  have hP := GlobalTheory.T.blkF_properStep_injective_blockDiag (CMType H) D.p D.q Ω K₀
  have hmod : ModelOK (aOf 𝔐 bW bO φ) x₀ m :=
    ⟨hP.1, hP.2.1, GlobalTheory.T.exists_nonzero_xb_of_left_inverse _ _ _ Ω _ _ K₀ J₀ x₀ hx₀ hB,
      GlobalTheory.T.basePart_yv_eq_algebraMap_xb _ _ _ Ω _ _ K₀ J₀ x₀, hP.2.2, GlobalTheory.T.isGenericFlag_gMat _ _ _ Ω, GlobalTheory.T.yv_eq_sum_minors_gMat _ _ _ Ω _ _ K₀ J₀ x₀,
      GlobalTheory.T.hodgeCpt_frame_change_regular E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ hF ht⟩
  have hT := GlobalTheory.T.hodgeCpt_frame_minor_valuation E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ hF ht hmod
  obtain ⟨Z, ξ', f, htie, hall, hdom, hsm⟩ := GlobalTheory.T.hodgeCpt_frame_leading_term E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ hF
  have hnorm := GlobalTheory.T.hodgeCpt_frame_degree_formula E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ hF Z ξ' f htie hall hdom hsm
  obtain ⟨𝔐', e, j, -, hov, hR, hsp, hV⟩ := GlobalTheory.T.hodgeCpt_base_change_compatible E H D l Xo c Y S Ω _ (algebraMap Ω _) K₀ _ J₀ _ x₀ _ 𝔐 Z ξ' f hall htie hnorm hdom hsm
  obtain ⟨Fl, hdeg, hfl⟩ := GlobalTheory.T.hodgeCpt_frame_divisor_formula E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ d hF hd 𝔐' _ j hov hsp hV
  obtain ⟨xdeg, hroot, hdy⟩ := GlobalTheory.T.hodgeCpt_frame_height_formula E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ hF ht hmod 𝔐' _ j Fl hov hsp hV hfl
  let M := model (aOf 𝔐 bW bO φ) x₀ m hmod
  let 𝔐₁ : HodgeCpt Y S M.x := reTie 𝔐 (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀) ht
  let tie : FlagTie M 𝔐₁ :=
    { eW := bW, eO := bO, frameW := fun q F h h' τ => (hT q F h h' τ).1, frameO := fun q F h h' τ => (hT q F h h' τ).2 }
  have hκ : ∀ k : K₀, ∀ r, M.blk r ≠ some (.inl k) := fun k r h => by
    change blkF (CMType H) D.p D.q K₀ r = _ at h
    unfold blkF at h
    split_ifs at h
    simpa using h
  let κ : K₀ → NonPluckerBlocks M.blk := fun k => ⟨.inl k, hκ k⟩
  let v : (Σ k, J₀ k) → Σ k, baseIdx (idx (p := D.p) (q := D.q) J₀ n) M.blk k := fun r => ⟨κ r.1, r.2⟩
  refine ⟨K₀ ⊕ StepIx (CMType H) D.p D.q, inferInstance, idx J₀ n, inferInstance, GenField Ω (rk (CMType H) D.p D.q),
    inferInstance, yv (aOf 𝔐 bW bO φ) x₀, M, 𝔐₁, tie, κ, v, RingHom.id Ω, 𝟙 𝔐.X, AddMonoidHom.id 𝔐.Li, 𝔐', Fl, xdeg,
    fun _ => 1, ⟨?_, fun _ => rfl, Function.bijective_id, inferInstanceAs (IsIso (𝟙 𝔐.X)), ?_, rfl, ?_⟩,
    ⟨hd, GlobalTheory.T.hodgeCpt_frame_order_bound E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ nd hF ht hv, GlobalTheory.T.hodgeCpt_frame_generic_rank E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ ht⟩,
    GlobalTheory.T.hodgeCpt_frame_unit_criterion E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ nd hF hv, ?_, hdeg⟩
  · refine ⟨fun a b h => Sum.inl_injective (congrArg (fun k => k.1) h), ?_, fun _ => rfl, ?_⟩
    · rintro ⟨k, i⟩ ⟨k', i'⟩ h
      have h1 : k = k' := Sum.inl_injective (congrArg (fun r => r.1.1) h)
      subst h1
      have h2 : HEq i i' := (Sigma.mk.inj_iff.1 h).2
      rw [eq_of_heq h2]
    · rintro ⟨_, i⟩ ⟨k, rfl⟩
      exact ⟨⟨k, i⟩, rfl⟩
  · exact HodgeOver.refl 𝔐
  · exact BasesOver.refl bW bO
  · refine ⟨⟨e.hom ≫ f, j, hov, hR, hV, hfl.1, hfl.2⟩, hroot, hdy, fun τ i => ?_⟩
    have h1 : detFac D.p i (M.g τ) = 1 := GlobalTheory.T.detFac_gMat_eq_one (CMType H) D.p D.q Ω τ i
    have h2 : M.lam (τ, i) = 1 := rfl
    rw [h1, h2]
    rcases M.blk (τ, i) with _ | b <;> simp
