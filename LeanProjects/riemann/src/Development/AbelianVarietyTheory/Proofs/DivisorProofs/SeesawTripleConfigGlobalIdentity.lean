import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerGlobalEval
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBLocalEigenTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocOpInfMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialFockDenseArchimedeanSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleFormConvergentThetaIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineGoodModelAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleRingInfiniteFiniteSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPlaceComponentAdeleConjugationEqComplexConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfAtOfPiInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAtEvIPiInfEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdeleWithArchimedeanComponents
import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBDefs
import Development.AutomorphicArithmetic.DivisorFrames.ExistsConvolutionNonvanishingWeight
import Development.AutomorphicArithmetic.DivisorFrames.SchwartzIntegralDominated
import Development.AutomorphicArithmetic.DivisorFrames.ModelEmbeddingGoodCompat
import Development.AutomorphicArithmetic.DivisorFrames.AdaptedPlaneHermitianRestrict
import Development.AutomorphicArithmetic.DivisorFrames.ArchimedeanIdelesPlaneCompat
import Development.AutomorphicArithmetic.DivisorFrames.IdeleIntegralCharacterNonzero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.ConeBArch

open GlobalTheory.ConeArchB GlobalTheory.ConeSoB GlobalTheory.XTermDecay GlobalTheory.HeisSchA GlobalTheory.DiffDecay GlobalTheory.EvZeroInf GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {B : Base F E} {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
  {M : Model σ X W} {M₁ : Model σ X₁ W₁} {χX χW : Chr F E} {om : Rep σ X W}

private theorem orb_cont (hP : GlobalTheory.FunPr.Hypotheses₂) (hB : B.IsGood σ) (hM : M.IsGood B.ψ) (hW : M.IsWeil B.ψ χX χW om)
    (K : Subgroup (UA σ X.J)) [CompactSpace (KAt K (evI F))] (f : SInf F (Fin n × Fin d)) :
    Continuous fun k : KAt K (evI F) => locOpInf (om (k.1, 1)) f := by
  have hSB : ∀ v, M.vac v ∈ SB _ := fun v => (hM.vac v).1
  have hpure : pure f M.vac ∈ schA F _ := GlobalTheory.TensUniq.pure_mem_schA f _ hSB hM.std
  obtain ⟨c, hc⟩ := exists_finPart_ne_zero M.vac (fun v => (hM.vac v).2.1) hM.std
  refine continuous_of_weak _ (g := fun y => ∏ᶠ v, M.vac v fun i => evalV F v (y i)) (c := c)
    (hc (fun i => mk 0 (c i)) fun _ => rfl) fun l hl => ?_
  have hw : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (incM F W.J) M.co χX χW om := hW
  refine ((hw.2.2 l hl _ hpure).comp
    (continuous_subtype_val.prodMk continuous_const : Continuous fun k : KAt K (evI F) => (k.1, (1 : UA σ W.J)))).congr
    fun k => congrArg l ?_
  exact acts_locOpInf (GlobalTheory.ArchLocalityX.acts_arch_left hP F E σ _ _ _ _ M B.ψ _ _ om hB.cm hB.std hW k.1 k.2.2 f)
    _ ⟨fun x z hz => finPart_add _ x z hz, hpure⟩

private theorem shift_cont (hB : B.IsGood σ) (hM : M.IsGood B.ψ) (A : Matrix (Fin n) (Fin d) (AE F E)) {T : Type}
    [TopologicalSpace T] {f : T → SInf F (Fin n × Fin d)} (hf : Continuous f) {z : T → AE F E} (hz : Continuous z) :
    Continuous fun t => locOpInf (M.co.rho B.ψ (partInf F (cA σ (z t) • A))) (f t) := by
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  simp only [(locOpInf_rho_eq hB.std hM _ _).2]
  refine continuous_archOp hf ?_
  let L := M.co.e.toLinearMap ∘ₗ (realAd F 1 • ((LinearMap.toSpanSingleton (AE F E) _ A).restrictScalars (AF F) ∘ₗ
    (cA σ).toLinearMap))
  have hL : Continuous fun t => M.co.e (partInf F (cA σ (z t) • A)) :=
    (IsModuleTopology.continuous_of_linearMap L).comp hz
  exact (continuous_pi fun i => continuous_qA.comp ((continuous_apply i).comp hL.fst)).prodMk
    (continuous_pi fun i => continuous_qA.comp ((continuous_apply i).comp hL.snd))

private theorem exists_clm_om (hP : GlobalTheory.FunPr.Hypotheses₂) (hB : B.IsGood σ) (hM : M.IsGood B.ψ) (hW : M.IsWeil B.ψ χX χW om)
    {k : UA σ X.J} (hk : k ∈ UAt σ X (evI F)) (T : SInf F (Fin n × Fin d) →L[ℂ] ℂ) :
    ∃ T' : SInf F (Fin n × Fin d) →L[ℂ] ℂ, ∀ f, T' f = T (locOpInf (om (k, 1)) f) := by
  have hs := IsUWeilPair.isUSplitting hW
  obtain ⟨l, hl, hlf⟩ := GlobalTheory.ArchJointCont.exists_adm F T
  let g₀ := GlobalTheory.ArchLocality.intInd (F := F) (Fin n × Fin d)
  have hg₀ : g₀ ∈ SB _ := GlobalTheory.ArchLocality.intInd_mem _
  have hg₀0 : g₀ 0 = 1 := by
    simp only [g₀, GlobalTheory.ArchLocality.intInd]
    rw [Set.indicator_of_mem (show (0 : Fin n × Fin d → IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) ∈ Set.pi Set.univ
      fun _ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) from
        fun i _ => zero_mem (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F))]
    rfl
  let r₀ : (Fin n × Fin d → AF F) → ℂ := fun x => g₀ fun i => (x i).2
  have hrr₀ : ∀ x z, At (evI F) z → r₀ (x + z) = r₀ x := by
    intro x z hz
    refine congrArg g₀ (funext fun i => ?_)
    show (x i).2 + (z i).2 = (x i).2
    rw [GlobalTheory.ArchLocality.snd_eq_zero_of_at hz i, add_zero]
  have hR₀ : ∀ f : SInf F (Fin n × Fin d), Rest (evI F) ⇑f r₀ := fun f =>
    ⟨hrr₀, Submodule.subset_span ⟨f, g₀, hg₀, rfl⟩⟩
  obtain ⟨T', hT'⟩ := hs.adm (k, 1) l hl g₀ hg₀
  refine ⟨T', fun f => ?_⟩
  have e1 : om (k, 1) (pureA F ⇑f g₀) = pureA F ⇑(locOpInf (om (k, 1)) f) g₀ :=
    acts_locOpInf (GlobalTheory.ArchLocalityX.acts_arch_left hP F E σ _ _ _ _ M B.ψ _ _ om hB.cm hB.std hW k hk f) r₀ (hR₀ f)
  have e2 := hT' f
  rw [LinearMap.comp_apply, e1, hlf, hg₀0, one_mul] at e2
  exact e2.symm

private theorem om_rho {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (hW : M.IsWeil ψ χX χW om) {g : UA σ X.J}
    (hex : ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (g, 1)) f f₁)
    (u : Matrix (Fin n) (Fin d) (AE F E)) (f : SInf F (Fin n × Fin d)) :
    locOpInf (M.co.rho ψ (partInf F (mat g * u))) (locOpInf (om (g, 1)) f) =
      locOpInf (om (g, 1)) (locOpInf (M.co.rho ψ (partInf F u)) f) := by
  have hS := IsUWeilPair.isUSplitting hW
  have hact : actAB (cA σ) ((g, 1) : UA σ X.J × UA σ W.J) (partInf F u) = partInf F (mat g * u) := by
    change mat g * (partInf F u) * (mat (1 : UA σ W.J))ᵀ = _
    have h1 : mat (1 : UA σ W.J) = 1 := rfl
    rw [h1, Matrix.transpose_one, Matrix.mul_one, partInf, partInf, Matrix.mul_smul]
  obtain ⟨r, h0, hr⟩ := exists_rest_inf F (Fin n × Fin d)
  refine DFunLike.coe_injective (eq_of_tens_inf h0 (hr f).1 ?_)
  have h2 := hS.impl (g, 1) (partInf F u) _ (hr f).2
  rw [hact, (locOpInf_rho M.co hψ u f).1 r (hr _), acts_locOpInf (hex _) r (hr _), acts_locOpInf (hex _) r (hr _),
    (locOpInf_rho M.co hψ _ _).1 r (hr _)] at h2
  exact h2.symm

private theorem partInf_congr (hcm : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {z z' : AE F E}
    (h : ∀ w, piInf (τ w) z = piInf (τ w) z') (A : Matrix (Fin n) (Fin d) (AE F E)) :
    partInf F (cA σ z • A) = partInf F (cA σ z' • A) := by
  have h0 : partInf F (z - z') = 0 := by
    refine GlobalTheory.ArchInj.eq_zero_of_at_of_piInf F E σ hcm τ _ (at_partInf _) fun w => ?_
    rw [partInf, piInf, RingHom.comp_apply, compInf_smul]
    have h1 : evInf F w (realAd F 1) = 1 := by
      have h1 : (realAd F 1).1 = 1 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by
        rw [map_one]; exact evI_realAd_one)
      exact congrFun h1 w
    rw [h1, one_smul, map_sub, map_sub, sub_eq_zero]
    exact h w
  rw [partInf, smul_sub, sub_eq_zero] at h0
  rw [partInf, partInf, ← smul_assoc, ← smul_assoc, ← map_smul, ← map_smul, h0]

private theorem compact_KAt (hP : GlobalTheory.FunPr.Hypotheses₂) (hB : B.IsGood σ) {r s : ℕ} (hX : X.IsHerm σ B r s)
    {K : Subgroup (UA σ X.J)} (hK : IsStab B K) : CompactSpace (KAt K (evI F)) := by
  have hKc : IsCompact (K : Set (UA σ X.J)) := by
    obtain ⟨K', _, _, hK', hc, -, -⟩ := GlobalTheory.StabHaar.stabEx hP F E σ B _ X _ _ hB hX
    rwa [show K = K' from Subgroup.ext fun g => (hK g).trans (hK' g).symm]
  exact isCompact_iff_compactSpace.1 (isCompact_KAt hKc _)

private theorem secondCountable_UA (X : Spc F E n) : SecondCountableTopology (UA σ X.J) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  obtain ⟨eh⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : SecondCountableTopology (AE F E) := eh.secondCountableTopology
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AE F E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E))ˣ :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  infer_instance

variable {H : Plane E n n₁} {H' : Plane E d d₁} {r s i₀ i₁ j₀ j₁ : ℕ} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁}
  {ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁)}
  {ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ}

private theorem ev_vac (hM : M.IsGood B.ψ) (hL : IsLocPart M M₁ e ei ev) (f : SInf F (Fin n × Fin d)) :
    e (pure f M.vac) = pure (ei f) M₁.vac := by
  rw [hL.2.2 f _ (fun v => (hM.vac v).1) (Eventually.of_forall fun _ => rfl)]
  exact congrArg _ (funext fun v => (hL.2.1 v).1)

private theorem exists_L (hP : GlobalTheory.FunPr.Hypotheses₂) (hB : B.IsGood σ) (hX : X.IsHerm σ B r s)
    (hH : H.IsAdapted σ B X X₁ i₀ i₁) (hH' : H'.IsAdapted σ B W W₁ j₀ j₁) (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ)
    (hW : M.IsWeil B.ψ χX χW om) (he : IsEv B M M₁ H.ι H'.ι (isoB H H') e) (hL : IsLocPart M M₁ e ei ev)
    {K : Subgroup (UA σ X.J)} (hK : IsStab B K) {μK : Measure (KAt K (evI F))} {μ : Measure (idelesAt E (evI F))}
    (hμK : IsNormK K (evI F) μK) (hμ : μ.IsHaarMeasure) {ν : Chr F E} (hν : Continuous ν) {z : ℕ} (hz : 1 ≤ z)
    (hS : ∀ f, ∃ g : SInf F (Fin n₁ × Fin d₁), ⇑g = coneInfFun B M om ei K μK μ (shiftB σ H H') ν z f)
    (l : SInf F (Fin n₁ × Fin d₁) →L[ℂ] ℂ) :
    ∃ L : SInf F (Fin n × Fin d) →L[ℂ] ℂ, ∀ f, l (coneInf B M om ei K μK μ (shiftB σ H H') ν z f) = L f ∧
      L f = ∫ k, ∫ y, l (coneInfInt B M om ei (shiftB σ H H') ν z f k.1 y.1) ∂μ ∂μK := by
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evI F)
  haveI hfin : IsFiniteMeasure μK := ⟨by rw [hμK.2]; exact ENNReal.one_lt_top⟩
  haveI : SFinite μK := @MeasureTheory.instSFiniteOfSigmaFinite _ _ μK (@MeasureTheory.IsFiniteMeasure.toSigmaFinite _ _ μK hfin)
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  haveI := secondCountable_UA (σ := σ) X
  haveI := compact_KAt hP hB hX hK
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  have hI : ∀ f, Continuous fun q : KAt K (evI F) × idelesAt E (evI F) =>
      coneInfInt B M om ei (shiftB σ H H') ν z f q.1.1 q.2.1 := fun f => by
    have hl : Continuous fun q : KAt K (evI F) × idelesAt E (evI F) => q.2.1 := continuous_subtype_val.comp continuous_snd
    exact (((continuous_subtype_val.comp hν).comp hl).mul ((Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp
      (GlobalTheory.Doubling.continuous_absE.comp hl))).pow z)).smul (ei.continuous.comp
        (shift_cont hB hM _ ((orb_cont hP hB hM hW K f).comp continuous_fst) (Units.continuous_val.comp hl)))
  obtain ⟨N, hN⟩ := GlobalTheory.T.integrable_ideles_power_decay F E σ B hB μ hμ z hz
  have hb : ∀ f (a m : ℕ), ∃ w : KAt K (evI F) × idelesAt E (evI F) → ℝ, Integrable w (μK.prod μ) ∧
      ∀ q : KAt K (evI F) × idelesAt E (evI F),
        SchwartzMap.seminorm ℂ a m (coneInfInt B M om ei (shiftB σ H H') ν z f q.1.1 q.2.1) ≤ w q := fun f a m => by
    have hΦc := orb_cont hP hB hM hW K f
    obtain ⟨C, hCb⟩ := shift_decay hB hX hH hH' hM hM₁ he (ev_vac hM hL) _
      (fun p hp => by
        obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (hp.comp hΦc).continuousOn
        exact ⟨C, fun t => (le_abs_self _).trans (hC t trivial)⟩)
      (SchwartzMap.seminorm ℂ a m) ((schwartz_withSeminorms ℂ _ ℂ).continuous_seminorm (a, m)) N
    refine ⟨_, (integrable_const (μ := μK) C).mul_prod hN, fun q => ?_⟩
    have h1 := hCb q.1 q.2.1
    rw [coneInfInt, map_smul_eq_mul, norm_mul, Circle.norm_coe, one_mul, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, NNReal.abs_eq, mul_div_left_comm]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have hP1 : ∀ f, Integrable (fun q : KAt K (evI F) × idelesAt E (evI F) =>
      l (coneInfInt B M om ei (shiftB σ H H') ν z f q.1.1 q.2.1)) (μK.prod μ) ∧
      l (coneInf B M om ei K μK μ (shiftB σ H H') ν z f) =
        ∫ q : KAt K (evI F) × idelesAt E (evI F), l (coneInfInt B M om ei (shiftB σ H H') ν z f q.1.1 q.2.1) ∂(μK.prod μ) := by
    intro f
    refine UpperTheory.schwartz_integral_dominated (μK.prod μ) _ (hI f) (hb f) _ (fun y => ?_) l
    rw [coe_coneInf (hS f), integral_prod]
    · rfl
    · obtain ⟨w, hw, hwb⟩ := hb f 0 0
      exact hw.mono' (continuous_eval (hI f) continuous_const).aestronglyMeasurable
        (Eventually.of_forall fun q => (SchwartzMap.norm_le_seminorm ℂ _ y).trans (hwb q))
  have hT : ∀ q : KAt K (evI F) × idelesAt E (evI F), ∃ T : SInf F (Fin n × Fin d) →L[ℂ] ℂ,
      ∀ f, T f = l (coneInfInt B M om ei (shiftB σ H H') ν z f q.1.1 q.2.1) := fun q => by
    let A : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d) :=
      ⟨archOp (archW (M.co.e (partInf F (shiftB σ H H' q.2.1)))), continuous_archOp continuous_id continuous_const⟩
    obtain ⟨T, hT⟩ := exists_clm_om hP hB hM hW q.1.2.2
      (l.comp (((ν q.2.1 : ℂ) * ((absE F E q.2.1 : ℝ) : ℂ) ^ z) • ei.comp A))
    refine ⟨T, fun f => ?_⟩
    rw [hT, coneInfInt, (locOpInf_rho_eq hB.std hM _ _).2]
    rfl
  choose T hT using hT
  haveI := GlobalTheory.T.schwartzMap_barrelledSpace' (Fin n × Fin d → mixedEmbedding.mixedSpace F)
  obtain ⟨L, hLf⟩ := GlobalTheory.ThetaIntAdm.exists_clm_integral (μK.prod μ) T fun f => by
    simpa only [hT] using (hP1 f).1
  refine ⟨L, fun f => ?_⟩
  simp only [hLf, hT]
  exact ⟨(hP1 f).2, integral_prod _ (hP1 f).1⟩

open FreeSingleHomotopyEquivDiscreteChains.UpperTheory.Dv.ConeB

private theorem exists_solve {m : ℕ} {J θ : Matrix (Fin m) (Fin m) ℂ} (h : IsCartan J θ) (v : Fin m → ℂ) :
    ∃ u : Fin m → ℂ, J *ᵥ star u = v := by
  have hinj : Function.Injective J.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hne
    have := h.2.2 (star x) (fun h0 => hne (by simpa using congrArg star h0))
    rw [star_star, show J *ᵥ x = 0 from hx, dotProduct_zero] at this
    simp at this
  obtain ⟨x, hx⟩ := LinearMap.injective_iff_surjective.1 hinj v
  exact ⟨star x, by rw [star_star]; exact hx⟩

private theorem loc_one (f : SInf F (Fin n × Fin d)) : locOpInf (om (1, 1)) f = f :=
  locOpInf_eq fun r _ => by rw [show ((1, 1) : UA σ X.J × UA σ W.J) = 1 from rfl, map_one]; rfl

private theorem loc_rho_zero (ψ : AddChar (AF F) ℂ) (f : SInf F (Fin n × Fin d)) : locOpInf (M.co.rho ψ 0) f = f :=
  locOpInf_eq fun r _ => by
    funext x
    simp [Darboux.rho, schr]

private def eta (B : Base F E) (H : Plane E n n₁) (k : UA σ X.J) : Fin n × InfinitePlace F → ℂ :=
  fun p => piInf (B.emb p.2) ((mat k⁻¹ *ᵥ incV F H.x) p.1)

private theorem eta_cont : Continuous (eta (σ := σ) (X := X) B H) := by
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  have hm : Continuous fun g : UA σ X.J => mat g := Units.continuous_val.comp continuous_subtype_val
  refine continuous_pi fun p => (GlobalTheory.Grow.continuous_infEmb_compInf F p.2 (B.emb p.2)).comp ?_
  exact (continuous_apply p.1).comp ((hm.comp continuous_inv).matrix_mulVec continuous_const)

private theorem piInf_inc (w : InfinitePlace F) (τ : EmbOver E w) (x : E) : piInf τ (inclR (F := F) (AF F) x) = τ.1 x := by
  change InfinitePlace.Completion.extensionEmbedding w ((1 : AF F).1 w) * τ.1 x = _
  rw [show (1 : AF F).1 w = 1 from rfl, map_one, one_mul]

private theorem eta_ne (hH : H.IsAdapted σ B X X₁ i₀ i₁) (k : UA σ X.J) (w : InfinitePlace F) :
    ∃ i, eta B H k (i, w) ≠ 0 := by
  by_contra h
  push Not at h
  have hx : H.x = 0 := by
    funext i
    have h1 : mat k *ᵥ (mat k⁻¹ *ᵥ incV F H.x) = incV F H.x := by
      rw [Matrix.mulVec_mulVec, ← GlobalTheory.StabHaar.mat_mul, mul_inv_cancel, GlobalTheory.StabHaar.mat_one, Matrix.one_mulVec]
    have h2 := congrArg (piInf (B.emb w)) (congrFun h1 i)
    rw [Matrix.mulVec, dotProduct, map_sum, Finset.sum_eq_zero fun j _ => by
      rw [map_mul, show piInf (B.emb w) ((mat k⁻¹ *ᵥ incV F H.x) j) = 0 from h j, mul_zero]] at h2
    rw [incV, piInf_inc] at h2
    exact (map_eq_zero _).1 h2.symm
  have := hH.xy
  rw [hx, form, zero_dotProduct] at this
  exact zero_ne_one this

private theorem exists_u (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (v : Fin n × InfinitePlace F → ℂ) :
    ∃ u : Fin n → AE F E, ∀ (k : UA σ X.J) w, piInf (B.emb w) ((mat k⁻¹ *ᵥ incV F H.x) ⬝ᵥ (incM F X.J *ᵥ fun i => cA σ (u i))) =
      pr v (eta B H k) w := by
  choose U hU using fun w => exists_solve (hX.cartan w) fun i => v (i, w)
  choose u _ hu using fun i => GlobalTheory.ThK.exists_at_evI_piInf_eq F E σ hB.cm B.emb fun w => U w i
  refine ⟨u, fun k w => ?_⟩
  rw [dotProduct, map_sum, pr]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, mul_comm, ← congrFun (hU w) i]
  congr 1
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, incM, Matrix.map_apply, piInf_inc,
    GlobalTheory.RealPlaceConj.piInf_cA_eq_star F E σ hB.cm, hu, Pi.star_apply]

private def phi (B : Base F E) (M : Model σ X W) (om : Rep σ X W) (H : Plane E n n₁) (H' : Plane E d d₁)
    (L : SInf F (Fin n × Fin d) →L[ℂ] ℂ) (f : SInf F (Fin n × Fin d)) (k : UA σ X.J) (z : AE F E) : ℂ :=
  L (locOpInf (M.co.rho B.ψ (partInf F (cA σ z • Matrix.vecMulVec (incV F H.y) (incV F H'.x)))) (locOpInf (om (k, 1)) f))

private theorem phi_congr (hB : B.IsGood σ) (L : SInf F (Fin n × Fin d) →L[ℂ] ℂ) (f : SInf F (Fin n × Fin d))
    (k : UA σ X.J) {z z' : AE F E} (h : ∀ w, piInf (B.emb w) z = piInf (B.emb w) z') :
    phi B M om H H' L f k z = phi B M om H H' L f k z' := by
  rw [phi, phi, partInf_congr hB.cm B.emb h]

private theorem phi_decay (hP : GlobalTheory.FunPr.Hypotheses₂) (hB : B.IsGood σ) (hX : X.IsHerm σ B r s)
    (hH : H.IsAdapted σ B X X₁ i₀ i₁) (hH' : H'.IsAdapted σ B W W₁ j₀ j₁) (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ)
    (hW : M.IsWeil B.ψ χX χW om) (he : IsEv B M M₁ H.ι H'.ι (isoB H H') e) (hL : IsLocPart M M₁ e ei ev)
    (K : Subgroup (UA σ X.J)) [CompactSpace (KAt K (evI F))] (l : SInf F (Fin n₁ × Fin d₁) →L[ℂ] ℂ)
    (f : SInf F (Fin n × Fin d)) {j : (InfinitePlace F → ℂ) → AE F E} (hj : Continuous j)
    (hjw : ∀ c w, piInf (B.emb w) (j c) = c w) (N : ℕ) :
    ∃ C : ℝ, ∀ (k : KAt K (evI F)) c, ‖phi B M om H H' (l.comp ei) f k.1 (j c)‖ ≤ C / (1 + ‖c‖) ^ N := by
  have hΦc := orb_cont hP hB hM hW K f
  obtain ⟨C, hC⟩ := shift_decay hB hX hH hH' hM hM₁ he (ev_vac hM hL) _
    (fun p hp => by
      obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (hp.comp hΦc).continuousOn
      exact ⟨C, fun t => (le_abs_self _).trans (hC t trivial)⟩)
    ((normSeminorm ℂ ℂ).comp l.toLinearMap) (continuous_norm.comp l.continuous) N
  refine ⟨|C|, fun k c => ?_⟩
  have hc : Continuous fun c => phi B M om H H' (l.comp ei) f k.1 (j c) :=
    (l.comp ei).continuous.comp (shift_cont hB hM _ continuous_const hj)
  have hcl : IsClosed {c : InfinitePlace F → ℂ | ‖phi B M om H H' (l.comp ei) f k.1 (j c)‖ ≤ |C| / (1 + ‖c‖) ^ N} :=
    isClosed_le hc.norm (continuous_const.div ((continuous_const.add continuous_norm).pow N) fun c => by positivity)
  refine closure_minimal (s := {c : InfinitePlace F → ℂ | ∀ w, c w ≠ 0}) (fun c hc0 => ?_) hcl (dense_ne_zero c)
  obtain ⟨t, -, ht⟩ := GlobalTheory.ThK.exists_unit_at_evI_piInf_eq σ B.emb c hB.cm hc0
  change ‖phi B M om H H' (l.comp ei) f k.1 (j c)‖ ≤ _
  rw [phi_congr hB _ _ _ (z' := t) fun w => (hjw c w).trans (ht w).symm]
  refine (hC k t).trans ?_
  simp only [ht]
  have h1 : ‖c‖ ≤ ∑ w, ‖c w‖ := (pi_norm_le_iff_of_nonneg (by positivity)).2 fun w =>
    Finset.single_le_sum (f := fun w => ‖c w‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ w)
  gcongr
  exact le_abs_self C

private theorem phi_levi (hP : GlobalTheory.FunPr.Hypotheses₂) (hB : B.IsGood σ) (hW : M.IsWeil B.ψ χX χW om)
    (L : SInf F (Fin n × Fin d) →L[ℂ] ℂ) (f : SInf F (Fin n × Fin d)) {k : UA σ X.J} (hk : k ∈ UAt σ X (evI F))
    {t : (AE F E)ˣ} {g₀ : UA σ X₁.J} (hlev : IsLevi (W₁ := X₁) H t g₀ k) {c : ℂ}
    (hc : ∀ g, L (locOpInf (om (k, 1)) g) = c * L g) (z : AE F E) :
    phi B M om H H' L f k z = c * phi B M om H H' L f 1 (t * z) := by
  have hex := GlobalTheory.ArchLocalityX.acts_arch_left hP F E σ _ _ _ _ M B.ψ _ _ om hB.cm hB.std hW k hk
  have h1 : mat k * (cA σ (t * z) • Matrix.vecMulVec (incV F H.y) (incV F H'.x)) =
      cA σ z • Matrix.vecMulVec (incV F H.y) (incV F H'.x) := by
    rw [Matrix.mul_smul, Matrix.mul_vecMulVec, hlev.2.1, Matrix.smul_vecMulVec, smul_smul, ← map_mul,
      mul_comm (t : AE F E), mul_assoc, Units.mul_inv, mul_one]
  rw [phi, phi, ← h1, om_rho hB.std hW hex, hc, loc_one]

private theorem hasExp_nu {a a' : ℕ} {Xc : Chars F E} (h : Xc.IsGood B a a') :
    HasExp B.emb Xc.ν fun w => B.mα w - B.mβ w := fun z hz => by
  have h0 : ∀ w, piInf (B.emb w) z / (‖piInf (B.emb w) z‖ : ℂ) ≠ 0 := fun w => by
    have : piInf (B.emb w) z ≠ 0 := (z.isUnit.map (piInf (B.emb w))).ne_zero
    exact div_ne_zero this (by exact_mod_cast norm_ne_zero_iff.2 this)
  rw [Chars.ν, MonoidHom.div_apply, Circle.coe_div, h.expα z hz, h.expβ z hz, ← Finset.prod_div_distrib]
  exact Finset.prod_congr rfl fun w _ => (zpow_sub₀ (h0 w) _ _).symm

private theorem phi_equiv (hP : GlobalTheory.FunPr.Hypotheses₂) (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) {r₁ s₁ : ℕ}
    (hX₁ : X₁.IsHerm σ B r₁ s₁) (hH : H.IsAdapted σ B X X₁ i₀ i₁) (hW : M.IsWeil B.ψ χX χW om)
    (L : SInf F (Fin n × Fin d) →L[ℂ] ℂ) {ν : Chr F E} {κ : InfinitePlace F → ℤ} (hexp : HasExp B.emb ν κ) (x : ℝ) (ε : ℕ)
    (hlaw : ∀ t g₀ g, IsLevi (W₁ := X₁) H t g₀ g → g ∈ UAt σ X (evI F) → g₀ ∈ UAt σ X₁ (evI F) → ∀ f,
      L (locOpInf (om (g, 1)) f) = fac ν x t * L f)
    (f : SInf F (Fin n × Fin d)) {j : (InfinitePlace F → ℂ) → AE F E} (hjw : ∀ c w, piInf (B.emb w) (j c) = c w)
    {k : UA σ X.J} (hk : k ∈ KInf σ X B.emb) (t : InfinitePlace F → ℂ) (ht : ∀ w, t w ≠ 0)
    (hsc : sc t (eta B H k) = eta B H (1 : UA σ X.J)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ c, phi B M om H H' L f k (j c) = ρ * wt κ ε t * phi B M om H H' L f 1 (j (t * c)) := by
  obtain ⟨τ, hτ, hτw⟩ := GlobalTheory.ThK.exists_unit_at_evI_piInf_eq σ B.emb t hB.cm ht
  obtain ⟨g₀, hg₀, hlev⟩ := UpperTheory.archimedean_ideles_plane_compat F E σ B _ _ _ _ _ _ _ _ X X₁ H hB hX hX₁ hH k hk τ hτ fun i w => by
    have h1 := congrFun hsc (i, w)
    simp only [sc, eta, inv_one, GlobalTheory.StabHaar.mat_one, Matrix.one_mulVec] at h1
    rw [hτw, h1]
  have habs : (absE F E τ : ℝ) = nm t := by
    rw [GlobalTheory.ArchIdeleDecay.absE_of_mem_arch hB.cm B.emb hτ]
    simp only [hτw, nm]
  have hwt : wt κ ε t = (ν τ : ℂ) * (nm t : ℂ) ^ ε := by
    rw [hexp τ hτ]
    simp only [hτw, wt, nm, Finset.prod_mul_distrib, pow_mul, Complex.ofReal_prod, Complex.ofReal_pow, Finset.prod_pow]
  have hn := nm_pos ht
  refine ⟨nm t ^ x / nm t ^ ε, by positivity, fun c => ?_⟩
  rw [phi_levi hP hB hW _ f hk.1 hlev (hlaw τ g₀ k hlev hk.1 hg₀),
    phi_congr hB _ _ _ (z' := j (t * c)) (fun w => by rw [map_mul, hτw, hjw, hjw]; rfl), hwt, fac, habs]
  have hn' : (nm t : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Complex.ofReal_div, Complex.ofReal_pow]
  congr 1
  field_simp

private theorem phi_one_zero (hB : B.IsGood σ) (L : SInf F (Fin n × Fin d) →L[ℂ] ℂ) (f : SInf F (Fin n × Fin d))
    {z : AE F E} (hz : ∀ w, piInf (B.emb w) z = 0) : phi B M om H H' L f 1 z = L f := by
  rw [phi_congr hB _ _ _ (z' := 0) (fun w => by rw [hz, map_zero]), phi, map_zero, zero_smul, partInf, smul_zero,
    loc_rho_zero, loc_one]

private theorem phi_cont (hB : B.IsGood σ) (hM : M.IsGood B.ψ) (L : SInf F (Fin n × Fin d) →L[ℂ] ℂ)
    (f : SInf F (Fin n × Fin d)) (k : UA σ X.J) {T : Type} [TopologicalSpace T] {z : T → AE F E} (hz : Continuous z) :
    Continuous fun t => phi B M om H H' L f k (z t) :=
  L.continuous.comp (shift_cont hB hM _ continuous_const hz)

private theorem exists_ne_zero (hP : GlobalTheory.FunPr.Hypotheses₂) (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) {r₁ s₁ : ℕ}
    (hX₁ : X₁.IsHerm σ B r₁ s₁) (hH : H.IsAdapted σ B X X₁ i₀ i₁) (hH' : H'.IsAdapted σ B W W₁ j₀ j₁)
    (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ) (hW : M.IsWeil B.ψ χX χW om) (he : IsEv B M M₁ H.ι H'.ι (isoB H H') e)
    (hL : IsLocPart M M₁ e ei ev) {K : Subgroup (UA σ X.J)} (hK : IsStab B K) {μK : Measure (KAt K (evI F))}
    {μ : Measure (idelesAt E (evI F))} (hμK : IsNormK K (evI F) μK) (hμ : μ.IsHaarMeasure)
    {ν : Chr F E} {κ : InfinitePlace F → ℤ} (hexp : HasExp B.emb ν κ) (x : ℝ) (ε : ℕ) (hκ : ∀ w, 2 * (ε : ℤ) < κ w)
    (l : SInf F (Fin n₁ × Fin d₁) →L[ℂ] ℂ) (hl : l ≠ 0)
    (hlaw : ∀ t g₀ g, IsLevi (W₁ := X₁) H t g₀ g → g ∈ UAt σ X (evI F) → g₀ ∈ UAt σ X₁ (evI F) → ∀ f,
      (l.comp ei) (locOpInf (om (g, 1)) f) = fac ν x t * (l.comp ei) f) :
    ∃ f, ∫ k, ∫ y, l (coneInfInt B M om ei (shiftB σ H H') ν (ε + 1) f k.1 y.1) ∂μ ∂μK ≠ 0 := by
  haveI hop : μK.IsOpenPosMeasure := hμK.1.toIsOpenPosMeasure
  haveI hfin : IsFiniteMeasure μK := ⟨by rw [hμK.2]; exact ENNReal.one_lt_top⟩
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  haveI := secondCountable_UA (σ := σ) X
  haveI := compact_KAt hP hB hX hK
  obtain ⟨j, hj, hjw⟩ : ∃ j : (InfinitePlace F → ℂ) → AE F E, Continuous j ∧ ∀ c w, piInf (B.emb w) (j c) = c w := by
    obtain ⟨Φ, -, hΦ1, -, -, -, hj, -⟩ := GlobalTheory.T.adele_ring_infinite_finite_split F E σ B hB.cm
    exact ⟨_, hj, fun c w => by rw [← hΦ1, RingEquiv.apply_symm_apply]⟩
  obtain ⟨f₀, hf₀⟩ := UpperTheory.model_embedding_good_compat F E σ B _ _ _ _ _ _ _ _ M M₁ _ _ _ hB.std hM hM₁ e he ei ev hL l hl
  have hφc : Continuous (Function.uncurry fun (k : KAt K (evI F)) c => phi B M om H H' (l.comp ei) f₀ k.1 (j c)) :=
    (l.comp ei).continuous.comp
      (shift_cont hB hM _ ((orb_cont hP hB hM hW K f₀).comp continuous_fst) (hj.comp continuous_snd))
  obtain ⟨v, hv⟩ := UpperTheory.exists_convolution_nonvanishing_weight μK κ ε hκ
    (fun k => eta B H k.1) (eta_cont.comp continuous_subtype_val) (fun k w => eta_ne hH k.1 w) _ hφc
    (phi_decay hP hB hX hH hH' hM hM₁ hW he hL K l f₀ hj hjw) 1
    (fun h => hf₀ ((phi_one_zero hB (l.comp ei) f₀ (hjw 0)).symm.trans (congrFun h 0)))
    (fun k t ht hsc => phi_equiv hP hB hX hX₁ hH hW _ hexp x ε hlaw f₀ hjw ((mem_KAt_inf hK).1 k.2) t ht hsc)
  obtain ⟨u, hu⟩ := exists_u (H := H) hB hX v
  obtain ⟨c, hc0, hc⟩ := UpperTheory.idele_integral_character_nonzero F E σ B hB.cm μ hμ ν _ hexp ε
  refine ⟨locOpInf (M.co.rho B.ψ (partInf F (Matrix.vecMulVec u (incV F H'.x)))) f₀, fun key => ?_⟩
  refine mul_ne_zero hc0 hv (Eq.trans ?_ key)
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  beta_reduce
  rw [← hc (fun s => phi B M om H H' (l.comp ei) f₀ k.1 (j (s + pr v (eta B H k.1))))
    (phi_cont hB hM _ f₀ k.1 (z := fun s => j (s + pr v (eta B H k.1))) (hj.comp (continuous_add_const _)))]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  beta_reduce
  rw [coneInfInt, map_smul, smul_eq_mul, shiftB, UpperTheory.adapted_plane_hermitian_restrict hP F E σ B _ _ _ _ _ _ _ _ _ _ X W X₁ W₁ M M₁ H H'
    _ _ om hB hX hH hH' hM hM₁ hW e he ei ev hL k.1 k.2.2]
  exact congrArg _ (phi_congr hB (l.comp ei) f₀ k.1 fun w => by rw [hjw, map_add, hu]; rfl)

end GlobalTheory.ConeBArch

end

open GlobalTheory.ConeBArch FreeSingleHomotopyEquivDiscreteChains.UpperTheory.Dv.ConeB GlobalTheory.ThK.LemF in
theorem _root_.GlobalTheory.T.seesaw_triple_config_global_identity : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    CfgB B G G₁ H H' → IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b)))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F v) → ℂ),
    ei ≠ 0 → (∀ v, ev v (G.M'.vac v) = G₁.M'.vac v ∧ (SB _).map (ev v) = SB _) →
    (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) → e' (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ K : Subgroup (UA σ G.V'.J), IsStab B K →
    ∀ (μKi : Measure (KAt K (evI F))) (μi : Measure (idelesAt E (evI F))), IsNormK K (evI F) μKi → μi.IsHaarMeasure →
    ∀ l : SInf F (Fin b × Fin (a + b)) →L[ℂ] ℂ,
    (∀ k ∈ UAt σ G₁.V' (evI F), ∀ f f' : SInf F (Fin b × Fin (a + b)), Acts (evI F) (om₁' (k, 1)) f f' → l f' = l f) →
    l ≠ 0 → ∃ f ∈ G.M'.Pol B.ψ B.emb, l (coneInf B G.M' om' ei K μKi μi (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) f) ≠ 0 := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' X om om' om₁ om₁' hC hT hT₁ e' he ei ev hei hev hloc K hK μK μ hμK hμ l hinv hl
  have hP := hKP.base
  have hB := hT.base
  have hM := hT.geo.hM'
  have hM₁ := hT₁.geo.hM'
  have hL : IsLocPart G.M' G₁.M' e' ei ev := ⟨hei, hev, hloc⟩
  have hν : Continuous X.ν := hT.chars.heckeα.1.div' hT.chars.heckeβ.1
  set ε := (a - (b + 2)) / 2 with hε
  obtain ⟨L, hLf⟩ := exists_L hP hB hT.geo.hV' hC.hH hC.hH' hM hM₁ hT.weil' he hL hK hμK hμ hν (z := ε + 1) (by omega)
    (GlobalTheory.ConeArchB.coneInfFun_schwartz hP B G G₁ H H' hC e' he K hK X om om' om₁ om₁' hT hT₁ ei ev hei hev hloc μK μ hμK hμ) l
  by_contra hne
  push Not at hne
  have hL0 : ∀ f, L f = 0 := fun f => by
    have hD := GlobalTheory.T.polynomialFock_dense_archimedeanSchwartz F E σ B _ _ G.V' G.W G.M' _ _ om' _ _ _ _ (GlobalTheory.ThK.Inhab.pairV' hT)
    exact closure_minimal (s := (G.M'.Pol B.ψ B.emb : Set _)) (t := {f | L f = 0}) (fun g hg => (hLf g).1.symm.trans (hne g hg))
      (isClosed_eq L.continuous continuous_const) (hD f)
  obtain ⟨f, hf⟩ := exists_ne_zero hP hB hT.geo.hV' hT₁.geo.hV' hC.hH hC.hH' hM hM₁ hT.weil' he hL hK hμK hμ
    (hasExp_nu hT.chars) (((a + (b + 2) : ℕ) : ℝ) / 2) ε (fun w => by have := hT.geo.kappa w; push_cast at this ⊢; omega) l hl
    fun t g₀ g hlev hg hg₀ f => by
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
        (GlobalTheory.ThK.EvLawBLeft.infLaw hP F E σ B a b G G₁ H H' hC e' he ei ev hL X om om' om₁ om₁' hT hT₁).2 t g₀ g hlev hg hg₀,
        map_smul, smul_eq_mul, hinv g₀ hg₀ _ _ (acts_locOpInf (GlobalTheory.ArchLocalityX.acts_arch_left hP F E σ _ _ _ _ G₁.M' B.ψ _ _
          om₁' hB.cm hB.std hT₁.weil' g₀ hg₀ _))]
  exact hf ((hLf f).2.symm.trans (hL0 f))
