import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftCuspFormAutomorphicSmoothModerateGrowth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumFockFromSquareIntegrability
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaChainLiftsAreCuspFormsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaModelsAreCoverDiscreteSeriesOfHarishChandraStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GkMapCuspFormsExtendsToSmoothVectorsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaVacuumCharactersRealPlacesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealPlaceThetaObjectsTheoremARPartsStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical

namespace GlobalTheory.Chain.IoLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Embedding

open GlobalTheory.Chain.CuspL2

theorem bounded_of_rapid {D : D7} {θ : InfFam D} {V : HSp D} (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ)
    {φ : GA D V → ℂ} (h : IsCuspGrow θ V φ) : ∃ B : ℝ, ∀ g, ‖φ g‖ ≤ B :=
  (GlobalTheory.Grow.rapidDec_of_unifModGrowth hP hθ h.1 h.2.1 h.2.2.2 h.2.2.1).bounded

theorem exists_embedding_skew_of_rapid : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfFam D) (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), IsInfFam θ → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → ∃ E : (GA D V → ℂ) →ₗ[ℂ] Lp ℂ 2 (μ.restrict 𝓕), (∀ φ, IsCuspGrow θ V φ → MemLp φ 2 (μ.restrict 𝓕) ∧ (E φ = 0 → φ = 0)) ∧ ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ φ', IsCuspGrow θ V φ → IsCuspGrow θ V φ' → IsCuspGrow θ V (Rder θ V τ X φ) → IsCuspGrow θ V (Rder θ V τ X φ') → ⟪E (Rder θ V τ X φ), E φ'⟫_ℂ + ⟪E φ, E (Rder θ V τ X φ')⟫_ℂ = 0 := by
  intro hP D θ V μ 𝓕 hθ hμ h𝓕
  obtain ⟨-, -, -, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have hfin := (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V μ 𝓕 hμ h𝓕).ne
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 hfin
  haveI := (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V μ hμ).1
  obtain ⟨E, hE⟩ := exists_toLp_ext (μ.restrict 𝓕)
  have mem : ∀ φ, IsCuspGrow θ V φ → MemLp φ 2 (μ.restrict 𝓕) := fun φ h => by
    obtain ⟨B, hB⟩ := bounded_of_rapid hP hθ h
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
  · rw [inner_eq (hE _ (mem _ hd)) (hE _ (mem _ h')), inner_eq (hE _ (mem _ h)) (hE _ (mem _ hd'))]
    obtain ⟨c0, B0, hB0⟩ := conj_mul h.1.cont h'.1.cont (bounded_of_rapid hP hθ h) (bounded_of_rapid hP hθ h')
    obtain ⟨c1, B1, hB1⟩ := conj_mul hd.1.cont h'.1.cont (bounded_of_rapid hP hθ hd) (bounded_of_rapid hP hθ h')
    obtain ⟨c2, B2, hB2⟩ := conj_mul h.1.cont hd'.1.cont (bounded_of_rapid hP hθ h) (bounded_of_rapid hP hθ hd')
    rw [← integral_add (Integrable.of_bound c1.measurable.aestronglyMeasurable B1 (.of_forall hB1))
      (Integrable.of_bound c2.measurable.aestronglyMeasurable B2 (.of_forall hB2))]
    exact GlobalTheory.Mem.IntByParts.setIntegral_deriv_eq_zero (GQ V) μ h𝓕 hfin
      (Φ := fun g => (starRingEnd ℂ) (φ g) * φ' g)
      (fun γ hγ g => by simp only [h.1.left γ hγ, h'.1.left γ hγ]) c0 (c1.add c2) hB0
      (fun g => (norm_add_le _ _).trans (add_le_add (hB1 g) (hB2 g)))
      (GlobalTheory.Mem.Lift.oneP_zero (V := V) (τ := τ) (X := X) hθ)
      fun g t => (GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (GlobalTheory.Mem.Lift.hasDerivAt_Rder h.2.1 hX) g t).star.mul
        (GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (GlobalTheory.Mem.Lift.hasDerivAt_Rder h'.2.1 hX) g t)

end Embedding

open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix GlobalTheory.PointAtPlaceHom

section Factor

variable {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar} {M : DSModel V S} {M' : DSModel W S'}

theorem exists_factor_kFin_of_rapid (hdec : GlobalTheory.Published.CuspRapidDecay) {θ : InfFam D} (hθ : IsInfFam θ)
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
  obtain ⟨E, hE0, hE⟩ := exists_embedding_skew_of_rapid hdec D θ V μ 𝓕 hθ hμ h𝓕
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

theorem exists_mult_of_rapid (hG : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.ExtExists D) (hdec : GlobalTheory.Published.CuspRapidDecay) {θ : InfFam D}
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
  obtain ⟨⟨T, hT⟩, hs⟩ := exists_factor_kFin_of_rapid hdec hθ ha hirr hker I (B.compl₂ (inclK h'))
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
  obtain ⟨E, hE0, -⟩ := exists_embedding_skew_of_rapid hdec D θ V μ 𝓕 hθ hμ h𝓕
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

end Factor

set_option maxHeartbeats 1000000 in

theorem ioPair_of_rapid (D : D7) (X : ProvA) (hX : ChosenSeries X) (h3 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X) (hC : LiftCusp D)
    (hL : GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.LiftProps D) (hG : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.GKExtension D) (hF : GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.VacuumFock D)
    (hV : VacChar D) (hB : ModelsAreCoverSeries D) (hdec : GlobalTheory.Published.CuspRapidDecay)
    (h5 : GlobalTheory.Published.HarishChandraModules) : IoPair D := by
  intro k V W M M' θ ψ hθ hP ω f hst hf It hIt J χ hJ ν 𝓕 hν h𝓕 J' χ' C hCle
  have hcusp := hC k V W M M' θ ψ hθ hP ω hst ν 𝓕 hν h𝓕 J' χ'
  obtain ⟨χS, χT, hω, he⟩ := hst
  have key := fun τ => (hP τ).elim fun al h => h.elim fun be h => h.elim fun ga h => h.elim fun de h =>
    exists_local hX h3 h5 hB M M' τ h.1 (congrArg dualPar h.2.2.1) (congrArg dualPar h.2.2.2)
  choose hs a a' ha ha' hirr hker using key
  have h : KSm M := fun τ => (hs τ).1
  have h' : KSm M' := fun τ => (hs τ).2
  have hv := fun τ => hV V W _ _ M M' θ ψ χS χT ω f τ _ _ hθ hω (he τ).1 (he τ).2 hf
  have hfl := hF V W _ _ M M' ψ θ hω.std hθ f hf
  have hpt := hfl.1
  have hinj := hfl.2.2.2.2
  have L := hL V W θ ψ χS χT ω hθ hω ν 𝓕 hν h𝓕
  let pt : PolF D W.rank V.rank →ₗ[ℂ] (WO V W → ℂ) := pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f
  have hp : ptOf ψ θ M M' f = pt := rfl
  have hS : ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ z, HasDerivAt (fun t : ℝ => ω (oneP θ V τ X t, 1) (pt φ) z)
      (pt (srcOp M M' τ (expT D k τ) X φ) z) 0 := fun τ X hX φ z => by
    have := (hv τ).2.2.1 X hX φ z
    simpa [hp, srcOp, sub_eq_add_neg] using this
  have hT : ∀ τ, ∀ X ∈ lieAt W τ, ∀ φ z, HasDerivAt (fun t : ℝ => ω (1, oneP θ W τ X t) (pt φ) z)
      (pt (tgtOp M M' τ (expS D k τ) X φ) z) 0 := fun τ X hX φ z => (hv τ).2.2.2 X hX φ z
  have hM : ∀ F : C, IsMultMap θ M' J' χ' (PiTensorProduct.lift.symm (F : SmT M' →ₗ[ℂ] (GA D W → ℂ))) := fun F =>
    (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT _ _ _ _ _).1 (hCle F.2))
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
  refine ioExists_of_forall hint B hB (fun F => ?_) fun u hu h0 => ?_
  swap
  · obtain ⟨φ, v, hne⟩ : ∃ φ v, It φ v ≠ 0 := by
      by_contra hn
      exact hIt.ne (LinearMap.ext₂ fun φ v => by_contra fun h => hn ⟨φ, v, h⟩)
    exact GlobalTheory.Grid.Sep.multT_eq_zero hu hne (h0 φ v)
  let BF : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] (GA D V → ℂ) := B.compr₂ (LinearMap.applyₗ F)
  have hBF : ∀ φ v, BF φ v = GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.lift ω ν 𝓕 (pt φ) ((F : SmT M' →ₗ[ℂ] (GA D W → ℂ)) v) :=
    fun φ v => hB φ v F
  have hcl : ∀ v : M'.Vec, IsAutFunSm θ W ((F : SmT M' →ₗ[ℂ] (GA D W → ℂ)) (PiTensorProduct.tprod ℂ v)) ∧
      IsCuspFun W ((F : SmT M' →ₗ[ℂ] (GA D W → ℂ)) (PiTensorProduct.tprod ℂ v)) :=
    fun v => ⟨(hM F).aut v, (hM F).cusp v⟩
  have hBg : ∀ φ v, IsCuspGrow θ V (BF φ v) := fun φ v => by
    refine GlobalTheory.Chain.CuspGrowSpace.isCuspGrow_of_mem_span D θ V _ ?_
    induction v using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      rw [map_smul]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      rw [hBF]
      exact ⟨L.aut _ _ (hpt φ) (hcl v), L.smooth _ _ (hpt φ) (hcl v), hcusp _ (hCle F.2) _ _ (hpt φ),
        L.growth _ _ (hpt φ) (hcl v)⟩
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
  let G : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] (SmT M × (GA D V → ℂ)) :=
    (LinearMap.prodEquiv ℂ).toLinearMap ∘ₗ It.prod BF
  have hGe : ∀ φ v, G φ v = (It φ v, BF φ v) := fun _ _ => rfl
  have hav := mem_span_of_average G h' fun τ φ v => by
    obtain ⟨n, φs, c, hc, hφ⟩ := GlobalTheory.Chain.IoLift.FockOrbit.fock_orbit_coefFam D V W _ _ M M' θ ψ ω f τ _ _ hθ hinj (hv τ).2.1 φ
    have hk := GlobalTheory.Chain.IoLift.kMean_mem_kFin_of_coefFam D W _ M' τ n c hc (v τ)
    refine ⟨n, φs, fun i => ⟨_, h' τ (hk i)⟩, hk, Prod.ext ?_ ?_⟩
    · rw [Prod.fst_sum]
      exact GlobalTheory.Chain.IoLift.it_eq_sum_kMean D V W _ _ M M' θ ω _ It hIt τ n c φ φs v _ hc.1 hφ fun _ => rfl
    · rw [Prod.snd_sum]
      funext g
      simp only [hGe, hBF, Finset.sum_apply]
      refine GlobalTheory.Chain.IoLift.AvgLift.liftInt_eq_sum_average D V W _ M' θ ψ χS χT ω ν 𝓕 hθ hω hν h𝓕 τ n c _ _ _ _ hc.1 (hpt φ) (fun κ => ?_)
        (hcl v).1.toIsAutFun (fun i x => apply_kMean (hM F) τ (hc.1 i) v _ rfl x) g (hint F _ _ g) fun i => hint F _ _ g
      rw [hφ, hp]
      simp only [map_sum, map_smul]
  obtain ⟨u, hu, hue⟩ := exists_mult_of_rapid hG.1 hdec hθ h h' ha ha' hirr hker It BF (J := J) (χ := χ)
    (by
      by_contra hn
      refine hIt.ne (LinearMap.ext₂ fun φ v => ?_)
      refine (Submodule.span_le (p := LinearMap.ker (LinearMap.fst ℂ _ _))).2 ?_ (hav φ v)
      rintro _ ⟨φ, y, rfl⟩
      exact by_contra fun h => hn ⟨φ, y, h⟩)
    (fun τ φ κ hκ => by
      obtain ⟨x, y, -, -, hc⟩ := (hv τ).2.1
      have := hc _ hκ 1 ⟨one_mem _, by simp⟩ φ
      have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
      rw [elt_one hθ, hp, ← map_smul, elt, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd,
        Matrix.nonsing_inv_mul_cancel_right _ _ hd] at this
      exact ⟨_, (MvPolynomial.totalDegree_smul_le _ _).trans (SubstDeg.totalDegree_subst_le _ _ _ _ _ _ _ _ _), fun v =>
        ⟨hIt.eqK τ κ (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt_subset M τ hκ) φ _ this.symm v, by rw [hBF, hBF, hshift, this]⟩⟩)
    (fun τ X hX φ v => hIt.eqg τ X hX φ _ (hS τ X hX φ) v)
    (fun τ Y hY φ v v' hd => hIt.invg τ Y hY φ _ v v' (hT τ Y hY φ) hd) hBg
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
      have e1 := GlobalTheory.MultGelf.rder_apply (hM F) τ v hY (v τ) w hw
      rw [Function.update_eq_self] at e1
      have e2 : GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.dOmT θ ω τ Y (pt φ) = pt (tgtOp M M' τ (expS D k τ) Y φ) :=
        funext fun z => (hT τ Y hY φ z).deriv
      funext g
      have := L.derT_add (hpt φ) (hcl v) τ hY g
      rw [hp, e2, add_comm] at this
      rw [Pi.add_apply, hBF, hBF]
      exact (congrArg (fun A => _ + GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.lift ω ν 𝓕 (pt φ) A g) e1).symm.trans this)
    fun φ v κ hκ g => by
      have e : ω (κ, 1) (pt φ) = pt (χ κ • φ) := by
        rw [map_smul]
        exact GlobalTheory.FiniteFock.om_pureTensorO_of_finite ψ θ V W χS χT ω hθ hω _ _ _ _ f hpt κ (hJ κ hκ).1 1 (one_mem _) _
          (hJ κ hκ).2 φ
      have e2 : BF (χ κ • φ) v g = χ κ * BF φ v g := by rw [map_smul]; rfl
      rw [← e2, hBF, hBF, ← e, ← hshift]
      rfl
  refine ⟨u, hu, fun φ v => sub_eq_zero.1 ?_⟩
  refine (Submodule.span_le (p := LinearMap.ker (u ∘ₗ LinearMap.fst ℂ _ _ - LinearMap.snd ℂ _ _))).2 ?_ (hav φ v)
  rintro _ ⟨φ, y, rfl⟩
  exact sub_eq_zero.2 (hue φ y)

theorem ioPair_onObjects : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules →
    GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ D : D7, GlobalTheory.Chain.IoPair D := by
  intro hD hH hC hW D
  obtain ⟨X, hX, -, -, -, -, h3, -⟩ := GlobalTheory.T.exists_provA_discreteSeries_archimedeanRallis hD hH
  exact ioPair_of_rapid D X hX h3 (GlobalTheory.T.thetaChainLifts_areCuspForms hD hH hC D) (GlobalTheory.Chain.LiftReg.liftProps_obj hC D)
    (GlobalTheory.T.gkMapCuspForms_extends_to_smoothVectors hH hW D) (GlobalTheory.VacuumFockLaws.vacuumFock_onObjects D) (GlobalTheory.T.thetaVacuumCharacters_realPlaces D) (GlobalTheory.T.thetaModels_are_coverDiscreteSeries_of_harishChandra hD hH D) hC hH

end GlobalTheory.Chain.IoLift

end
