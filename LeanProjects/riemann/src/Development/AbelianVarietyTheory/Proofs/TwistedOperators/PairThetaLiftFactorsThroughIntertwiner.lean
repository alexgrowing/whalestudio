import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockVectorsOfThetaDatumInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonzeroFockVacuumOfNonzeroThetaFunction

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid GlobalTheory.Chain.RealIt GlobalTheory.Chain.IoLift
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix GlobalTheory.PointAtPlaceHom

namespace GlobalTheory.PairLift.RuleLift

variable {D : D7}

section Emb

variable {θ : InfFam D} {V : HSp D}

theorem bounded (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) {φ : GA D V → ℂ} (h : IsCuspGrow θ V φ) :
    ∃ B : ℝ, ∀ g, ‖φ g‖ ≤ B :=
  (GlobalTheory.Grow.rapidDec_of_unifModGrowth hP hθ h.1 h.2.1 h.2.2.2 h.2.2.1).bounded

theorem exists_embedding_skew (hP : GlobalTheory.Published.CuspRapidDecay) (θ : InfFam D) (V : HSp D) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) (hθ : IsInfFam θ) (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) :
    ∃ E : (GA D V → ℂ) →ₗ[ℂ] Lp ℂ 2 (μ.restrict 𝓕), (∀ φ, IsCuspGrow θ V φ → MemLp φ 2 (μ.restrict 𝓕) ∧
      (E φ = 0 → φ = 0)) ∧ ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ φ', IsCuspGrow θ V φ → IsCuspGrow θ V φ' →
        IsCuspGrow θ V (Rder θ V τ X φ) → IsCuspGrow θ V (Rder θ V τ X φ') →
          ⟪E (Rder θ V τ X φ), E φ'⟫_ℂ + ⟪E φ, E (Rder θ V τ X φ')⟫_ℂ = 0 := by
  obtain ⟨-, -, -, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have hfin := (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V μ 𝓕 hμ h𝓕).ne
  have : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 hfin
  have := (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V μ hμ).1
  obtain ⟨E, hE⟩ := GlobalTheory.Chain.CuspL2.exists_toLp_ext (μ.restrict 𝓕)
  have mem : ∀ φ, IsCuspGrow θ V φ → MemLp φ 2 (μ.restrict 𝓕) := fun φ h => by
    obtain ⟨B, hB⟩ := bounded hP hθ h
    exact MemLp.of_bound h.1.cont.measurable.aestronglyMeasurable B (.of_forall hB)
  refine ⟨E, fun φ h => ⟨mem φ h, fun h0 => ?_⟩, fun τ X hX φ φ' h h' hd hd' => ?_⟩
  · have h1 := hE φ (mem φ h)
    rw [h0] at h1
    have h2 : φ =ᵐ[μ.restrict 𝓕] 0 := h1.symm.trans (Lp.coeFn_zero _ _ _)
    have hm : MeasurableSet {g | φ g ≠ 0} := (isOpen_ne_fun h.1.cont continuous_const).measurableSet
    have h3 : μ {g | φ g ≠ 0} = 0 := by
      refine h𝓕.measure_zero_of_invariant _ (fun γ => ?_) ?_
      · ext g
        rw [Set.mem_smul_set_iff_inv_smul_mem]
        change φ (((γ⁻¹ : GQ V) : GA D V) * g) ≠ 0 ↔ φ g ≠ 0
        rw [h.1.left _ (γ⁻¹).2]
      · rw [← Measure.restrict_apply hm]
        exact h2
    exact (Continuous.ae_eq_iff_eq μ h.1.cont continuous_zero).1 h3
  · rw [GlobalTheory.Chain.CuspL2.inner_eq (hE _ (mem _ hd)) (hE _ (mem _ h')),
      GlobalTheory.Chain.CuspL2.inner_eq (hE _ (mem _ h)) (hE _ (mem _ hd'))]
    obtain ⟨c0, B0, hB0⟩ := GlobalTheory.Chain.CuspL2.conj_mul h.1.cont h'.1.cont (bounded hP hθ h) (bounded hP hθ h')
    obtain ⟨c1, B1, hB1⟩ := GlobalTheory.Chain.CuspL2.conj_mul hd.1.cont h'.1.cont (bounded hP hθ hd) (bounded hP hθ h')
    obtain ⟨c2, B2, hB2⟩ := GlobalTheory.Chain.CuspL2.conj_mul h.1.cont hd'.1.cont (bounded hP hθ h) (bounded hP hθ hd')
    rw [← integral_add (Integrable.of_bound c1.measurable.aestronglyMeasurable B1 (.of_forall hB1))
      (Integrable.of_bound c2.measurable.aestronglyMeasurable B2 (.of_forall hB2))]
    exact GlobalTheory.Mem.IntByParts.setIntegral_deriv_eq_zero (GQ V) μ h𝓕 hfin
      (Φ := fun g => (starRingEnd ℂ) (φ g) * φ' g)
      (fun γ hγ g => by simp only [h.1.left γ hγ, h'.1.left γ hγ]) c0 (c1.add c2) hB0
      (fun g => (norm_add_le _ _).trans (add_le_add (hB1 g) (hB2 g)))
      (GlobalTheory.Mem.Lift.oneP_zero (V := V) (τ := τ) (X := X) hθ)
      fun g t => (GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (GlobalTheory.Mem.Lift.hasDerivAt_Rder h.2.1 hX) g t).star.mul
        (GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (GlobalTheory.Mem.Lift.hasDerivAt_Rder h'.2.1 hX) g t)

end Emb

variable {V W : HSp D} {S S' : D.what₂.Tau → SPar}

theorem exists_local {X : ProvA} (hX : ChosenSeries X) (h5 : GlobalTheory.Published.HarishChandraModules)
    (hB : ModelsAreCoverSeries D) (M : DSModel V S) (M' : DSModel W S') (τ : D.what₂.Tau) {aS aT : ℚ}
    (hR : RulePar X (S τ) (S' τ) aS aT) :
    (kFin M τ ≤ M.sm τ ∧ kFin M' τ ≤ M'.sm τ) ∧ ∃ a a', IsKAct M τ a ∧ IsKAct M' τ a' ∧
      AbsIrr (fun X : lieAt V τ => a X) ∧ LocKer M M' τ aS aT a' := by
  obtain ⟨p, q, r, s, l₁, l₂, l₁', l₂', h1, h2, h1', h2', hR, hS, hS'⟩ := hR
  obtain ⟨⟨e, he⟩, m, hm, hU⟩ := hB.1 X V S M τ p q l₁ l₂ aT ⟨hR.pos, h1, h2, hR.par, hX _ _ _ hR.par, hS⟩
  obtain ⟨⟨e', he'⟩, m', hm', hU'⟩ := hB.2 X W S' M' τ r s l₁' l₂' aS ⟨hR.pos', h1', h2', hR.par', hX _ _ _ hR.par', hS'⟩
  obtain ⟨U, hU⟩ := hU e he
  obtain ⟨U', hU'⟩ := hU' e' he'
  obtain ⟨κ, hκ⟩ := PolyIso.exists_isPolyIso _ _ _ _ _ _ _ _ e e' he he'
  obtain ⟨s₁, a, ha⟩ := GlobalTheory.Chain.IoLift.kFin_smooth_isKAct D V S M τ _ _ _ _ _ _ _ hU
  obtain ⟨s₂, a', ha'⟩ := GlobalTheory.Chain.IoLift.kFin_smooth_isKAct D W S' M' τ _ _ _ _ _ _ _ hU'
  have i1 := GlobalTheory.SmallerSource.discrete_series_gk_admissible_irreducible X (h5.admQ5_of_harishChandraModules X) hR.pos (ofBlocks l₁ l₂ : Ix p q → ℚ)
  have i2 := GlobalTheory.SmallerSource.discrete_series_gk_admissible_irreducible X (h5.admQ5_of_harishChandraModules X) hR.pos' (ofBlocks l₁' l₂' : Ix r s → ℚ)
  refine ⟨⟨s₁, s₂⟩, a, a', ha, ha', GlobalTheory.KFinIrr.absIrr_kFin D V S M τ _ _ _ _ _ m U.toLinearEquiv a hU i1.2 i1.1 ha, ?_⟩
  exact GlobalTheory.Chain.IoLift.KerTransfer.locKer_of_coverKer D V W S S' M M' τ _ _ _ _ _ _ _ _ e e' m m' aS aT U U' κ a' hm' hU hU' hκ ha'
    (GlobalTheory.Chain.IoLift.CoverKernel.coverKer_of_down X _ _ _ _ _ _ hR.down i1.2 (GlobalTheory.Chain.IoLift.UImg.unitaryImage _ _ _ _)
      (GlobalTheory.Chain.IoLift.finiteSupport_of_admissible _ _ _ _ _ _ i2.1) GlobalTheory.Chain.IoLift.TensorFormProof.tensorForm)

variable {M : DSModel V S} {M' : DSModel W S'}

theorem exists_factor_kFin (hdec : GlobalTheory.Published.CuspRapidDecay) {θ : InfFam D} (hθ : IsInfFam θ)
    {aS aT : D.what₂.Tau → ℚ} {a : ∀ τ, Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ)}
    {a' : ∀ τ, Matrix (Fin W.rank) (Fin W.rank) ℂ → Module.End ℂ (kFin M' τ)} (ha : ∀ τ, IsKAct M τ (a τ))
    (hirr : ∀ τ, AbsIrr fun X : lieAt V τ => a τ X) (hker : ∀ τ, LocKer M M' τ (aS τ) (aT τ) (a' τ))
    (I : PolF D W.rank V.rank →ₗ[ℂ] KT M' →ₗ[ℂ] KT M) (B : PolF D W.rank V.rank →ₗ[ℂ] KT M' →ₗ[ℂ] (GA D V → ℂ))
    (h0 : I ≠ 0) (hIs : ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ y, I (srcOp M M' τ (aT τ) X φ) y = intersection_update_fsHerm_neg_one τ (a τ X) (I φ y))
    (hIt : ∀ τ, ∀ Y ∈ lieAt W τ, ∀ φ y, I (tgtOp M M' τ (aS τ) Y φ) y + I φ (intersection_update_fsHerm_neg_one τ (a' τ Y) y) = 0)
    (hBg : ∀ φ y, IsCuspGrow θ V (B φ y))
    (hBs : ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ y, B (srcOp M M' τ (aT τ) X φ) y = Rder θ V τ X (B φ y))
    (hBt : ∀ τ, ∀ Y ∈ lieAt W τ, ∀ φ (y : KVec M'), B (tgtOp M M' τ (aS τ) Y φ) (PiTensorProduct.tprod ℂ y) +
      B φ (intersection_update_fsHerm_neg_one τ (a' τ Y) (PiTensorProduct.tprod ℂ y)) = 0) :
    (∃ T : KT M →ₗ[ℂ] (GA D V → ℂ), ∀ φ y, T (I φ y) = B φ y) ∧ Submodule.span ℂ {x | ∃ φ y, I φ y = x} = ⊤ := by
  obtain ⟨μ, 𝓕, hμ, h𝓕⟩ := GlobalTheory.Ker.HypModel.exists_haar_fundDom D V
  obtain ⟨E, hE0, hE⟩ := GlobalTheory.PairLift.RuleLift.exists_embedding_skew hdec θ V μ 𝓕 hθ hμ h𝓕
  have s1 : ∀ τ X (p : D.what₂.Tau → LPol W.rank V.rank) x, glue (Function.update p τ (sOp M M' τ (aT τ) X x)) =
      srcOp M M' τ (aT τ) X (glue (Function.update p τ x)) := fun τ X p x => by
    rw [srcOp_glue, Function.update_idem, Function.update_self]
  have s2 : ∀ τ Y (p : D.what₂.Tau → LPol W.rank V.rank) x, glue (Function.update p τ (tOp M M' τ (aS τ) Y x)) =
      tgtOp M M' τ (aS τ) Y (glue (Function.update p τ x)) := fun τ X p x => by
    rw [tgtOp_glue, Function.update_idem, Function.update_self]
  have s3 : ∀ τ (A : Module.End ℂ (kFin M' τ)) (y : KVec M') z, PiTensorProduct.tprod ℂ (Function.update y τ (A z)) =
      intersection_update_fsHerm_neg_one τ A (PiTensorProduct.tprod ℂ (Function.update y τ z)) := fun τ A y z => by
    rw [position_tprod, Function.update_idem, Function.update_self]
  have pI : ∀ τ L, IsContr τ L → ∀ p y,
      IsLocPair M M' τ (aS τ) (aT τ) (a' τ) ((slice (multi I) τ p y).compr₂ L) := fun τ L hL p y => by
    refine ⟨fun X hX P P' z z' => ?_, fun Y hY P z => ?_⟩
    · have hL' := fun x => LinearMap.congr_fun (hL (a τ X)) x
      simp only [LinearMap.comp_apply] at hL'
      simp only [LinearMap.compr₂_apply, slice_apply, multi_apply, s1, hIs τ X hX, hL']
      exact (ha τ).skew X hX _ _
    · simp only [LinearMap.compr₂_apply, slice_apply, multi_apply, s2, s3]
      rw [← map_add, hIt τ Y hY, map_zero]
  have pB : ∀ τ p y, IsLocPair M M' τ (aS τ) (aT τ) (a' τ) ((slice (multi B) τ p y).compr₂ E) := fun τ p y => by
    refine ⟨fun X hX P P' z z' => ?_, fun Y hY P z => ?_⟩
    · simp only [LinearMap.compr₂_apply, slice_apply, multi_apply, s1, hBs τ X hX]
      exact hE τ X hX _ _ (hBg _ _) (hBg _ _) (hBs τ X hX _ _ ▸ hBg _ _) (hBs τ X hX _ _ ▸ hBg _ _)
    · simp only [LinearMap.compr₂_apply, slice_apply, multi_apply, s2, s3]
      rw [← map_add, hBt τ Y hY, map_zero]
  obtain ⟨⟨T, hT⟩, hs⟩ := exists_factor (fun τ (X : lieAt V τ) => sOp M M' τ (aT τ) X) _ hirr (multi I) (multi B)
    (by by_contra hn; exact h0 (span_multi I fun p y => by_contra fun h => hn ⟨p, y, h⟩))
    (fun τ X p y => by rw [multi_apply, multi_apply, ← srcOp_glue, hIs τ X X.2])
    fun τ L hL p y hne => ⟨fun L' hL' p' y' => hker τ _ _ _ _ (pI τ L hL p y) (pI τ L' hL' p' y') hne,
      fun p' y' n x z h => by
        refine (hE0 _ (GlobalTheory.Chain.CuspGrowSpace.isCuspGrow_of_mem_span D θ V _ (sum_mem fun i _ => Submodule.subset_span (hBg _ _)))).2 ?_
        rw [map_sum]
        exact hker τ _ _ _ _ (pI τ L hL p y) (pB τ p' y') hne n x z h⟩
  refine ⟨⟨T, fun φ y => ?_⟩, eq_top_iff.2 (hs ▸ Submodule.span_mono ?_)⟩
  · have := span_multi (I.compr₂ T - B) fun p y => sub_eq_zero.2 (hT p y)
    exact sub_eq_zero.1 (LinearMap.congr_fun₂ this φ y)
  · rintro _ ⟨p, y, rfl⟩
    exact ⟨_, _, rfl⟩

theorem exists_mult (hG : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.ExtExists D) (hdec : GlobalTheory.Published.CuspRapidDecay) {θ : InfFam D}
    (hθ : IsInfFam θ) (h : KSm M) (h' : KSm M')
    {aS aT : D.what₂.Tau → ℚ} {a : ∀ τ, Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ)}
    {a' : ∀ τ, Matrix (Fin W.rank) (Fin W.rank) ℂ → Module.End ℂ (kFin M' τ)} (ha : ∀ τ, IsKAct M τ (a τ))
    (ha' : ∀ τ, IsKAct M' τ (a' τ))
    (hirr : ∀ τ, AbsIrr fun X : lieAt V τ => a τ X) (hker : ∀ τ, LocKer M M' τ (aS τ) (aT τ) (a' τ))
    (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) (B : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] (GA D V → ℂ))
    {J : Set (GA D V)} {χ : GA D V → ℂ} (h0 : ∃ φ y, It φ (inclK h' y) ≠ 0)
    (hK : ∀ τ (φ : PolF D W.rank V.rank), ∀ k ∈ maxCpt M τ, ∃ φ' : PolF D W.rank V.rank,
      φ'.totalDegree ≤ φ.totalDegree ∧ ∀ v, inclT M (It φ' v) = actT M τ k (inclT M (It φ v)) ∧
        B φ' v = rTr V (atTau θ V τ k) (B φ v))
    (hIs : ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ v, DerT M τ X (It φ v) (It (srcOp M M' τ (aT τ) X φ) v))
    (hIt : ∀ τ, ∀ Y ∈ lieAt W τ, ∀ φ v v', DerT M' τ Y v v' → It (tgtOp M M' τ (aS τ) Y φ) v + It φ v' = 0)
    (hBg : ∀ φ v, IsCuspGrow θ V (B φ v))
    (hBs : ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ v, B (srcOp M M' τ (aT τ) X φ) v = Rder θ V τ X (B φ v))
    (hBt : ∀ τ, ∀ Y ∈ lieAt W τ, ∀ φ (v : M'.Vec) (w : M'.sm τ), (w : M'.H τ) = dRep (M'.rep τ) Y (v τ) →
      B (tgtOp M M' τ (aS τ) Y φ) (PiTensorProduct.tprod ℂ v) +
        B φ (PiTensorProduct.tprod ℂ (Function.update v τ w)) = 0)
    (hlev : ∀ φ v, ∀ k ∈ J, ∀ g, B φ v (g * k) = χ k * B φ v g) :
    ∃ u ∈ MultT θ M J χ, ∀ φ y, u (It φ (inclK h' y)) = B φ (inclK h' y) := by
  have inj := inclK_injective h
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ (LinearMap.ker_eq_bot.2 inj)
  let I := (It.compl₂ (inclK h')).compr₂ g
  have hI : ∀ φ y, inclK h (I φ y) = It φ (inclK h' y) := fun φ y => by
    obtain ⟨z, hz⟩ := mem_range_inclK h (It φ (inclK h' y)) fun τ =>
      ⟨(MvPolynomial.restrictTotalDegree _ ℂ φ.totalDegree).map (inclT M ∘ₗ It.flip (inclK h' y)), inferInstance,
        fun k hk => by
          obtain ⟨φ', h1, h2⟩ := hK τ φ k hk
          exact ⟨φ', (MvPolynomial.mem_restrictTotalDegree _ _ _).2 h1, (h2 _).1⟩⟩
    change inclK h (g (It φ (inclK h' y))) = _
    rw [← hz, ← LinearMap.comp_apply g, hg, LinearMap.id_apply]
  have hIs' : ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ y, I (srcOp M M' τ (aT τ) X φ) y = intersection_update_fsHerm_neg_one τ (a τ X) (I φ y) :=
    fun τ X hX φ y => inj (by
      rw [hI]
      exact derT_unique (hIs τ X hX φ _) (hI φ y ▸ (GlobalTheory.Chain.IoLift.FinTensor.kFinTensor D V S M τ h).2.1 _ (ha τ) X hX _))
  obtain ⟨⟨T, hT⟩, hs⟩ := GlobalTheory.PairLift.RuleLift.exists_factor_kFin hdec hθ ha hirr hker I (B.compl₂ (inclK h'))
    (fun e => by
      obtain ⟨φ, y, h0⟩ := h0
      exact h0 (by rw [← hI, e]; simp)) hIs'
    (fun τ Y hY φ y => inj (by
      rw [map_add, hI, hI, map_zero]
      exact hIt τ Y hY φ _ _ ((GlobalTheory.Chain.IoLift.FinTensor.kFinTensor D W S' M' τ h').2.1 _ (ha' τ) Y hY _)))
    (fun φ y => hBg _ _) (fun τ X hX φ y => hBs τ X hX _ _) fun τ Y hY φ y => by
      rw [LinearMap.compl₂_apply, LinearMap.compl₂_apply, position_tprod, inclK_update, inclK_tprod]
      exact hBt τ Y hY φ _ _ ((ha' τ).der Y hY _).deriv.symm
  simp only [LinearMap.compl₂_apply] at hT
  have hind : ∀ p : KT M → Prop, (∀ φ y, p (I φ y)) → (∀ x y, p x → p y → p (x + y)) → ∀ y, p y := by
    intro p h1 h3 y
    have hy : y ∈ Submodule.span ℂ {x | ∃ φ y, I φ y = x} := hs ▸ Submodule.mem_top
    suffices ∀ c : ℂ, p (c • y) by simpa using this 1
    induction hy using Submodule.span_induction with
    | mem _ h => obtain ⟨P, x, rfl⟩ := h; intro c; rw [← map_smul]; exact h1 _ _
    | zero => intro c; simpa using h1 0 0
    | add _ _ _ _ a b => intro c; rw [smul_add]; exact h3 _ _ (a c) (b c)
    | smul a _ _ h => intro c; rw [smul_smul]; exact h _
  have hg : ∀ x, IsCuspGrow θ V (T x) := fun x => GlobalTheory.Chain.CuspGrowSpace.isCuspGrow_of_mem_span D θ V _ (hind (fun x => T x ∈ _)
    (fun φ y => Submodule.subset_span (hT φ y ▸ hBg _ _)) (fun x y a b => by rw [map_add]; exact add_mem a b) x)
  obtain ⟨μ, 𝓕, hμ, h𝓕⟩ := GlobalTheory.Ker.HypModel.exists_haar_fundDom D V
  obtain ⟨E, hE0, -⟩ := GlobalTheory.PairLift.RuleLift.exists_embedding_skew hdec θ V μ 𝓕 hθ hμ h𝓕
  obtain ⟨U, ⟨hU, hUe⟩, -⟩ := hG θ hθ V S M J χ μ 𝓕 hμ h𝓕 (T.compMultilinearMap (PiTensorProduct.tprod ℂ))
    ⟨fun u => (hg _).1, fun u => (hg _).2.1, fun u => (hg _).2.2.1, fun u => (hE0 _ (hg _)).1, fun u => (hg _).2.2.2,
      fun u => hind (fun x => ∀ k ∈ J, ∀ g, T x (g * k) = χ k * T x g) (fun φ y => hT φ y ▸ hlev _ _)
        (fun x y a b k hk g => by simp only [map_add, Pi.add_apply, a k hk g, b k hk g, mul_add]) _,
      fun τ k hk u w hw => by
        obtain rfl : w = kOp M τ hk (u τ) := Subtype.ext hw
        rw [LinearMap.compMultilinearMap_apply, ← position_tprod]
        refine hind (fun x => T (intersection_update_fsHerm_neg_one τ (kOp M τ hk) x) = rTr V (atTau θ V τ k) (T x)) (fun φ y => ?_)
          (fun x y a b => by rw [map_add, map_add, map_add, a, b]; rfl) _
        obtain ⟨φ', -, h2⟩ := hK τ φ k hk
        rw [hT, ← (h2 _).2, ← hT]
        refine congrArg T (inj ((tensorLaw D V S M).inj ?_))
        rw [(GlobalTheory.Chain.IoLift.FinTensor.kFinTensor D V S M τ h).2.2, hI, hI, (h2 _).1],
      fun τ X hX u w hw => by
        obtain rfl : w = a τ X (u τ) := Subtype.ext (hw.trans ((ha τ).der X hX _).deriv)
        rw [LinearMap.compMultilinearMap_apply, ← position_tprod]
        refine hind (fun x => T (intersection_update_fsHerm_neg_one τ (a τ X) x) = Rder θ V τ X (T x)) (fun φ y => ?_)
          (fun x y a b => by
            rw [map_add, map_add, map_add, a, b, (GlobalTheory.Mem.AutSpace.linOnSm_Rder hX).add _ (hg _).2.1 _ (hg _).2.1]) _
        rw [← hIs' τ X hX, hT, hT, hBs τ X hX]⟩
  refine ⟨PiTensorProduct.lift U, ⟨U, Submodule.subset_span hU, rfl⟩, fun φ y => ?_⟩
  have e : PiTensorProduct.lift U ∘ₗ inclK h = T := PiTensorProduct.ext (MultilinearMap.ext fun u => by
    rw [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, inclK_tprod, PiTensorProduct.lift.tprod]
    exact hUe _ u fun _ => rfl)
  rw [← hI, ← hT, ← e, LinearMap.comp_apply]

theorem signBlockDeterminant_zpow_eq_of_agree {n : ℕ} (ε : Fin n → Bool) (w : Bool → ℚ) {x x₀ : Bool → ℤ} (hx : ∀ j, (x (ε j) : ℚ) = w (ε j))
    (hx₀ : ∀ j, (x₀ (ε j) : ℚ) = w (ε j)) (e : Bool) (g : Matrix (Fin n) (Fin n) ℂ) :
    signBlockDeterminant ε e g ^ x e = signBlockDeterminant ε e g ^ x₀ e := by
  by_cases hj : ∃ j, ε j = e
  · obtain ⟨j, rfl⟩ := hj
    have : x (ε j) = x₀ (ε j) := by exact_mod_cast (hx j).trans (hx₀ j).symm
    rw [this]
  · simp only [not_exists] at hj
    have : IsEmpty {a // ε a = e} := ⟨fun a => hj a.1 a.2⟩
    rw [signBlockDeterminant, Matrix.det_isEmpty, _root_.one_zpow, _root_.one_zpow]

theorem compact_transfer {V W : HSp D} {S S' : D.what₂.Tau → SPar} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {M : DSModel V S} {M' : DSModel W S'} {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {f f₀ : WO V W → ℂ}
    {τ : D.what₂.Tau} {aS aT : ℚ} (hinj : Function.Injective (ptOf ψ θ M M' f₀))
    (hc : CompactFock ψ θ M M' ω f τ aS aT) (hc₀ : CompactFock ψ θ M M' ω f₀ τ aS aT)
    {h : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hh : h ∈ Formalism.REAL.Kset (M.ε τ))
    {k : Matrix (Fin W.rank) (Fin W.rank) ℂ} (hk : k ∈ Formalism.REAL.Kset (M'.ε τ)) {φ φ' : PolF D W.rank V.rank}
    (e : ω (elt θ M τ h, elt θ M' τ k) (ptOf ψ θ M M' f₀ φ) = ptOf ψ θ M M' f₀ φ') :
    ω (elt θ M τ h, elt θ M' τ k) (ptOf ψ θ M M' f φ) = ptOf ψ θ M M' f φ' := by
  obtain ⟨x, y, hx, hy, hc⟩ := hc
  obtain ⟨x₀, y₀, hx₀, hy₀, hc₀⟩ := hc₀
  let pt : PolF D W.rank V.rank →ₗ[ℂ] (WO V W → ℂ) := pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f
  let pt₀ : PolF D W.rank V.rank →ₗ[ℂ] (WO V W → ℂ) := pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f₀
  have hp : ptOf ψ θ M M' f = pt := rfl
  have hp₀ : ptOf ψ θ M M' f₀ = pt₀ := rfl
  have e1 := hc₀ h hh k hk φ
  rw [e, hp₀, ← map_smul] at e1
  have e2 := hinj (show ptOf ψ θ M M' f₀ φ' = ptOf ψ θ M M' f₀ _ from e1)
  rw [hc h hh k hk φ, e2, hp, map_smul, signBlockDeterminant_zpow_eq_of_agree (M.ε τ) _ hx hx₀, signBlockDeterminant_zpow_eq_of_agree (M.ε τ) _ hx hx₀,
    signBlockDeterminant_zpow_eq_of_agree (M'.ε τ) _ hy hy₀, signBlockDeterminant_zpow_eq_of_agree (M'.ε τ) _ hy hy₀]

set_option maxHeartbeats 1000000 in

theorem pairLifts (D : D7) (X : ProvA) (hI : Inputs D X) (hC : CuspAll D X) : PairLifts D X := by
  intro S S' aS aT hR V W M M' θ ψ hθ ω hω f₀ It hf₀ hIt ν 𝓕 hν h𝓕 f hf F hF
  obtain ⟨χS, χT, hω', he⟩ := hω
  by_cases hf0 : f = 0
  · subst hf0
    have e : ∀ p, ptOf ψ θ M M' 0 p = 0 := fun p => GlobalTheory.Mem.VacReal.ptF_zero ψ θ (Fr.ofModel M) (Fr.ofModel M') p
    refine ⟨0, zero_mem _, fun p v g => ?_⟩
    simp only [e, thetaKO, map_zero, Pi.zero_apply, zero_mul, integral_zero, LinearMap.zero_apply]
    exact ⟨integrableOn_zero, trivial⟩
  have hvf : IsVacVec ψ θ M M' f := ⟨hf.1, hf0, hf.2⟩
  have key := fun τ => exists_local hI.chosen hI.hc hI.bridge M M' τ (hR τ)
  choose hs a a' ha ha' hirr hker using key
  have h : KSm M := fun τ => (hs τ).1
  have h' : KSm M' := fun τ => (hs τ).2
  have hv := fun τ => hI.vacChar V W _ _ M M' θ ψ χS χT ω f τ _ _ hθ hω' (he τ).1 (he τ).2 hvf
  have hv₀ := fun τ => hI.vacChar V W _ _ M M' θ ψ χS χT ω f₀ τ _ _ hθ hω' (he τ).1 (he τ).2 hf₀
  have hpt : ∀ P, IsThetaFunO ψ V W (ptOf ψ θ M M' f P) := fun P =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO hω'.std hθ _ _ _ _ hf.1 P
  have hinj₀ := GlobalTheory.FockInj.ptOf_injective D V W S S' ψ θ M M' f₀ hω'.std hθ hf₀
  have L := hI.laws V W θ ψ χS χT ω hθ hω' ν 𝓕 hν h𝓕
  have hcusp := hC S S' aS aT hR V W M M' θ ψ hθ ω ⟨χS, χT, hω', he⟩ ν 𝓕 hν h𝓕
  let pt : PolF D W.rank V.rank →ₗ[ℂ] (WO V W → ℂ) := pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f
  have hp : ptOf ψ θ M M' f = pt := rfl
  let pt₀ : PolF D W.rank V.rank →ₗ[ℂ] (WO V W → ℂ) := pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f₀
  have hp₀ : ptOf ψ θ M M' f₀ = pt₀ := rfl
  have hS : ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ z, HasDerivAt (fun t : ℝ => ω (oneP θ V τ X t, 1) (pt φ) z)
      (pt (srcOp M M' τ (aT τ) X φ) z) 0 := fun τ X hX φ z => by
    have := (hv τ).2.2.1 X hX φ z
    simpa [hp, srcOp, sub_eq_add_neg] using this
  have hT : ∀ τ, ∀ X ∈ lieAt W τ, ∀ φ z, HasDerivAt (fun t : ℝ => ω (1, oneP θ W τ X t) (pt φ) z)
      (pt (tgtOp M M' τ (aS τ) X φ) z) 0 := fun τ X hX φ z => (hv τ).2.2.2 X hX φ z
  have hS₀ : ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ z, HasDerivAt (fun t : ℝ => ω (oneP θ V τ X t, 1) (pt₀ φ) z)
      (pt₀ (srcOp M M' τ (aT τ) X φ) z) 0 := fun τ X hX φ z => by
    have := (hv₀ τ).2.2.1 X hX φ z
    simpa [hp₀, srcOp, sub_eq_add_neg] using this
  have hT₀ : ∀ τ, ∀ X ∈ lieAt W τ, ∀ φ z, HasDerivAt (fun t : ℝ => ω (1, oneP θ W τ X t) (pt₀ φ) z)
      (pt₀ (tgtOp M M' τ (aS τ) X φ) z) 0 := fun τ X hX φ z => (hv₀ τ).2.2.2 X hX φ z
  let C := MultT θ M' ∅ 1
  have hM : ∀ F : C, IsMultMap θ M' ∅ 1 (PiTensorProduct.lift.symm (F : SmT M' →ₗ[ℂ] (GA D W → ℂ))) := fun F =>
    (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT _ _ _ _ _).1 F.2)
  have hint : ∀ F : C, ∀ φ v g, IntegrableOn
      (fun h => thetaKO ω g h (pt φ) * (F : SmT M' →ₗ[ℂ] (GA D W → ℂ)) v h) 𝓕 ν := fun F φ v g => by
    induction v using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      have := (L.integ _ _ (hpt φ) ⟨(hM F).aut v, (hM F).cusp v⟩ g 1).const_mul r
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      beta_reduce
      rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm, rTr, mul_one]
      rfl
    | add x y hx hy => simp only [map_add, Pi.add_apply, mul_add]; exact hx.add hy
  obtain ⟨B, hB⟩ := exists_trilinear ν 𝓕 (fun g h => LinearMap.proj 0 ∘ₗ ω (g, h)) pt C hint
  replace hB : ∀ φ v F, B φ v F =
      GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.lift ω ν 𝓕 (pt φ) ((F : SmT M' →ₗ[ℂ] (GA D W → ℂ)) v) := hB
  have hshift : ∀ (κ : GA D V) s F, rTr V κ (GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.lift ω ν 𝓕 s F) =
      GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.lift ω ν 𝓕 (ω (κ, 1) s) F := fun κ s F => funext fun g => by
    unfold rTr GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.lift Lift.liftInt thetaKO
    congr 1; funext h
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  let Fc : C := ⟨F, hF⟩
  let BF : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] (GA D V → ℂ) := B.compr₂ (LinearMap.applyₗ Fc)
  have hBF : ∀ φ v, BF φ v = GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.lift ω ν 𝓕 (pt φ) (F v) := fun φ v => hB φ v Fc
  have hcl : ∀ v : M'.Vec, IsAutFunSm θ W (F (PiTensorProduct.tprod ℂ v)) ∧
      IsCuspFun W (F (PiTensorProduct.tprod ℂ v)) := fun v => ⟨(hM Fc).aut v, (hM Fc).cusp v⟩
  have hBg : ∀ φ v, IsCuspGrow θ V (BF φ v) := fun φ v => by
    refine GlobalTheory.Chain.CuspGrowSpace.isCuspGrow_of_mem_span D θ V _ ?_
    induction v using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      rw [map_smul]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      rw [hBF]
      exact ⟨L.aut _ _ (hpt φ) (hcl v), L.smooth _ _ (hpt φ) (hcl v), hcusp _ hF _ _ (hpt φ),
        L.growth _ _ (hpt φ) (hcl v)⟩
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
  let G : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] (SmT M × (GA D V → ℂ)) :=
    (LinearMap.prodEquiv ℂ).toLinearMap ∘ₗ It.prod BF
  have hGe : ∀ φ v, G φ v = (It φ v, BF φ v) := fun _ _ => rfl
  have hav := mem_span_of_average G h' fun τ φ v => by
    obtain ⟨n, φs, c, hc, hφ₀⟩ := GlobalTheory.Chain.IoLift.FockOrbit.fock_orbit_coefFam D V W _ _ M M' θ ψ ω f₀ τ _ _ hθ hinj₀
      (hv₀ τ).2.1 φ
    have hφ : ∀ k, ω (1, elt θ M' τ (Formalism.REAL.toMK k)) (ptOf ψ θ M M' f φ) =
        ptOf ψ θ M M' f (∑ i, c i k • φs i) := fun k => by
      have := compact_transfer hinj₀ (hv τ).2.1 (hv₀ τ).2.1 (h := 1) ⟨one_mem _, by rw [Matrix.one_mul, Matrix.mul_one]⟩
        k.2 (φ := φ) (by rw [GlobalTheory.Chain.IoLift.elt_one hθ]; exact hφ₀ k)
      rwa [GlobalTheory.Chain.IoLift.elt_one hθ] at this
    have hk := GlobalTheory.Chain.IoLift.kMean_mem_kFin_of_coefFam D W _ M' τ n c hc (v τ)
    refine ⟨n, φs, fun i => ⟨_, h' τ (hk i)⟩, hk, Prod.ext ?_ ?_⟩
    · rw [Prod.fst_sum]
      exact GlobalTheory.Chain.IoLift.it_eq_sum_kMean D V W _ _ M M' θ ω _ It hIt τ n c φ φs v _ hc.1 hφ₀ fun _ => rfl
    · rw [Prod.snd_sum]
      funext g
      simp only [hGe, hBF, Finset.sum_apply]
      refine GlobalTheory.Chain.IoLift.AvgLift.liftInt_eq_sum_average D V W _ M' θ ψ χS χT ω ν 𝓕 hθ hω' hν h𝓕 τ n c _ _ _ _ hc.1
        (hpt φ) (fun κ => ?_) (hcl v).1.toIsAutFun (fun i x => apply_kMean (hM Fc) τ (hc.1 i) v _ rfl x) g
        (hint Fc _ _ g) fun i => hint Fc _ _ g
      rw [hφ, hp]
      simp only [map_sum, map_smul]
  obtain ⟨u, hu, hue⟩ := GlobalTheory.PairLift.RuleLift.exists_mult hI.ext.1 hI.decay hθ h h' ha ha' hirr hker It BF
    (J := ∅) (χ := 1)
    (by
      by_contra hn
      refine hIt.ne (LinearMap.ext₂ fun φ v => ?_)
      refine (Submodule.span_le (p := LinearMap.ker (LinearMap.fst ℂ _ _))).2 ?_ (hav φ v)
      rintro _ ⟨φ, y, rfl⟩
      exact by_contra fun h => hn ⟨φ, y, h⟩)
    (fun τ φ κ hκ => by
      obtain ⟨x, y, -, -, hc⟩ := (hv₀ τ).2.1
      have this₀ := hc _ hκ 1 ⟨one_mem _, by rw [Matrix.one_mul, Matrix.mul_one]⟩ φ
      rw [hp₀, ← map_smul, ← hp₀] at this₀
      have this := compact_transfer hinj₀ (hv τ).2.1 (hv₀ τ).2.1 hκ ⟨one_mem _, by rw [Matrix.one_mul, Matrix.mul_one]⟩
        this₀
      have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
      rw [GlobalTheory.Chain.IoLift.elt_one hθ, hp₀, elt, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd,
        Matrix.nonsing_inv_mul_cancel_right _ _ hd] at this₀
      rw [GlobalTheory.Chain.IoLift.elt_one hθ, hp, elt, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd,
        Matrix.nonsing_inv_mul_cancel_right _ _ hd] at this
      exact ⟨_, (MvPolynomial.totalDegree_smul_le _ _).trans (SubstDeg.totalDegree_subst_le _ _ _ _ _ _ _ _ _), fun v =>
        ⟨hIt.eqK τ κ (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt_subset M τ hκ) φ _ this₀.symm v, by rw [hBF, hBF, hshift, this]⟩⟩)
    (fun τ X hX φ v => hIt.eqg τ X hX φ _ (hS₀ τ X hX φ) v)
    (fun τ Y hY φ v v' hd => hIt.invg τ Y hY φ _ v v' (hT₀ τ Y hY φ) hd) hBg
    (fun τ X hX φ v => by
      induction v using PiTensorProduct.induction_on with
      | smul_tprod r v =>
        rw [map_smul, map_smul, (GlobalTheory.Mem.AutSpace.linOnSm_Rder hX).smul, hBF, hBF,
          L.derS (pt φ) _ (hpt φ) (hcl v) τ X hX]
        congr 2
        exact funext fun z => (hS τ X hX φ z).deriv.symm
      | add x y hx hy =>
        rw [map_add, map_add, hx, hy, (GlobalTheory.Mem.AutSpace.linOnSm_Rder hX).add _ (hBg _ _).2.1 _ (hBg _ _).2.1])
    (fun τ Y hY φ v w hw => by
      have e1 := GlobalTheory.MultGelf.rder_apply (hM Fc) τ v hY (v τ) w hw
      rw [Function.update_eq_self] at e1
      have e2 : GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.dOmT θ ω τ Y (pt φ) = pt (tgtOp M M' τ (aS τ) Y φ) :=
        funext fun z => (hT τ Y hY φ z).deriv
      funext g
      have := L.derT_add (hpt φ) (hcl v) τ hY g
      rw [hp, e2, add_comm] at this
      rw [Pi.add_apply, hBF, hBF]
      exact (congrArg (fun A => _ + GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.lift ω ν 𝓕 (pt φ) A g) e1).symm.trans this)
    fun φ v κ hκ g => absurd hκ (Set.notMem_empty κ)
  have hall : ∀ φ v, u (It φ v) = BF φ v := fun φ v => sub_eq_zero.1 (by
    refine (Submodule.span_le (p := LinearMap.ker (u ∘ₗ LinearMap.fst ℂ _ _ - LinearMap.snd ℂ _ _))).2 ?_ (hav φ v)
    rintro _ ⟨φ, y, rfl⟩
    exact sub_eq_zero.2 (hue φ y))
  refine ⟨u, hu, fun p v g => ⟨hint Fc p v g, ?_⟩⟩
  rw [hall, hBF]
  rfl

end GlobalTheory.PairLift.RuleLift

end
