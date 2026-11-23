import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaSumAdmissibility
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaDistributionNonzeroAdmissible
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaDistributionHeisenbergInvariant
import GroundTheory.GlobalFields.Adele.Compact
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsFurtherExtra

open Matrix NumberField IsDedekindDomain GlobalTheory.WeilM MeasureTheory
open scoped TensorProduct Pointwise Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.ThetaAvg

theorem eq_zero_of_orth {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] (S : Set C(K, ℂ)) (h1 : 1 ∈ S)
    (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) (hstar : ∀ a ∈ S, star a ∈ S)
    (hsep : ∀ x y : K, x ≠ y → ∃ a ∈ S, a x ≠ a y) (f : C(K, ℂ)) (hf : ∀ a ∈ S, ∫ x, a x * f x ∂μ = 0) : f = 0 :=
  _root_.UpperTheory.Reformulated.B.Qo7.eq_zero_of_orth μ S h1 hmul hstar hsep f hf

def IsPer {G : Type} [AddCommGroup G] [TopologicalSpace G] (Γ : AddSubgroup G) (f : G → ℂ) : Prop :=
  Continuous f ∧ ∀ γ ∈ Γ, ∀ x, f (x + γ) = f x

theorem exists_mean {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] (Γ : AddSubgroup G)
    (hΓ : IsClosed (Γ : Set G)) {D : Set G} (hD : IsCompact D) (hDΓ : ∀ x, ∃ γ ∈ Γ, x - γ ∈ D) :
    ∃ M : (G → ℂ) →ₗ[ℂ] ℂ,
      (∀ f, IsPer Γ f → ∀ B : ℝ, (∀ x ∈ D, ‖f x‖ ≤ B) → ‖M f‖ ≤ B) ∧
      (∀ f, IsPer Γ f → ∀ y, M (fun x => f (x + y)) = M f) ∧
      (∀ σ : G →+ G, Continuous σ → Function.Surjective σ → (∀ γ ∈ Γ, σ γ ∈ Γ) →
        ∀ f, IsPer Γ f → M (fun x => f (σ x)) = M f) ∧
      ∀ S : Set (G → ℂ), (∀ a ∈ S, IsPer Γ a) → 1 ∈ S → (∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) → (∀ a ∈ S, star a ∈ S) →
        (∀ x y, (∀ a ∈ S, a x = a y) → -x + y ∈ Γ) → ∀ f, IsPer Γ f → (∀ a ∈ S, M (a * f) = 0) → f = 0 := by
  haveI : CompactSpace (G ⧸ Γ) := ⟨by
    convert hD.image (QuotientAddGroup.continuous_mk (N := Γ))
    refine (Set.eq_univ_of_forall fun q => ?_).symm
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      obtain ⟨γ, hγ, hx⟩ := hDΓ x
      exact ⟨x - γ, hx, QuotientAddGroup.eq.mpr (by simpa using hγ)⟩⟩
  letI : MeasurableSpace (G ⧸ Γ) := borel _
  haveI : BorelSpace (G ⧸ Γ) := ⟨rfl⟩
  let μ : Measure (G ⧸ Γ) := Measure.addHaarMeasure ⊤
  have hμ : μ Set.univ = 1 := by simpa using Measure.addHaarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (G ⧸ Γ)))
  haveI : IsProbabilityMeasure μ := ⟨hμ⟩
  have hint : ∀ h : C(G ⧸ Γ, ℂ), Integrable h μ := fun h =>
    h.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let I : C(G ⧸ Γ, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun h => ∫ x, h x ∂μ
      map_add' := fun a b => by
        rw [← integral_add (hint a) (hint b)]
        simp
      map_smul' := fun c a => by
        simp [integral_const_mul] }
  let π : C(G ⧸ Γ, ℂ) →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun h x => h (x : G ⧸ Γ)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hπ : Function.Injective π := fun a b h => by
    ext q
    induction q using QuotientAddGroup.induction_on with
    | H x => exact congrFun h x
  obtain ⟨r, hr⟩ := π.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hπ)
  have hM : ∀ h : C(G ⧸ Γ, ℂ), (I ∘ₗ r) (fun x => h (x : G ⧸ Γ)) = ∫ x, h x ∂μ := fun h =>
    congrArg I (LinearMap.congr_fun hr h)
  have hlift : ∀ f, IsPer Γ f → ∃ h : C(G ⧸ Γ, ℂ), f = fun x : G => h (x : G ⧸ Γ) := fun f hf => by
    have hw : ∀ a b : G, (QuotientAddGroup.leftRel Γ) a b → f a = f b := fun a b hab => by
      rw [QuotientAddGroup.leftRel_apply] at hab
      rw [← hf.2 _ hab a, add_neg_cancel_left]
    exact ⟨⟨Quotient.lift f hw, hf.1.quotient_lift hw⟩, rfl⟩
  refine ⟨I ∘ₗ r, fun f hf B hB => ?_, fun f hf y => ?_, fun σ hσ hs hσΓ f hf => ?_,
    fun S hS h1 hmul hstar hsep f hf h0 => ?_⟩
  · have hB' : ∀ x, ‖f x‖ ≤ B := fun x => by
      obtain ⟨γ, hγ, hx⟩ := hDΓ x
      have := hB _ hx
      rwa [← hf.2 γ hγ, sub_add_cancel] at this
    obtain ⟨h, rfl⟩ := hlift f hf
    rw [hM]
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := h) (C := B)
      (Filter.Eventually.of_forall fun q => by
        induction q using QuotientAddGroup.induction_on with
        | H x => exact hB' x)
    simpa using this
  · obtain ⟨h, rfl⟩ := hlift f hf
    rw [hM, ← integral_add_right_eq_self (μ := μ) h (y : G ⧸ Γ)]
    exact hM (h.comp ⟨fun q => q + (y : G ⧸ Γ), by fun_prop⟩)
  · obtain ⟨h, rfl⟩ := hlift f hf
    let τ : G ⧸ Γ →+ G ⧸ Γ := QuotientAddGroup.map Γ Γ σ hσΓ
    have hτ : Continuous τ :=
      (QuotientAddGroup.isQuotientMap_mk Γ).continuous_iff.mpr (QuotientAddGroup.continuous_mk.comp hσ)
    have hτs : Function.Surjective τ := fun q => by
      induction q using QuotientAddGroup.induction_on with
      | H x =>
        obtain ⟨z, rfl⟩ := hs x
        exact ⟨z, rfl⟩
    have hp : MeasurePreserving τ μ μ := AddMonoidHom.measurePreserving hτ hτs rfl
    rw [hM]
    refine (hM (h.comp ⟨τ, hτ⟩)).trans ?_
    conv_rhs => rw [← hp.map_eq]
    rw [integral_map hτ.measurable.aemeasurable h.continuous.aestronglyMeasurable]
    rfl
  · obtain ⟨h, rfl⟩ := hlift f hf
    have := eq_zero_of_orth μ (π ⁻¹' S) h1 (fun a ha b hb => hmul _ ha _ hb) (fun a ha => hstar _ ha) ?_ h ?_
    · rw [this]; rfl
    · intro p q hpq
      induction p using QuotientAddGroup.induction_on with
      | H x =>
      induction q using QuotientAddGroup.induction_on with
      | H y =>
        by_contra hc
        push Not at hc
        refine hpq (QuotientAddGroup.eq.mpr (hsep x y fun a ha => ?_))
        obtain ⟨a', rfl⟩ := hlift a (hS a ha)
        exact hc a' ha
    · intro a ha
      exact (hM (a * h)).symm.trans (h0 _ ha)

theorem exists_SB_one {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [T2Space X]
    {h : X → ℂ} (hh : h ∈ SB X) (h0 : h 0 = 1) {K : Set X} (hK : IsCompact K) : ∃ g ∈ SB X, ∀ x ∈ K, g x = 1 := by
  have hU : IsClopen (h ⁻¹' {1}) := hh.1.isClopen_fiber 1
  have hUc : IsCompact (h ⁻¹' {1}) := hh.2.isCompact.of_isClosed_subset hU.1 fun x hx =>
    subset_tsupport _ (by rw [Function.mem_support, show h x = 1 from hx]; exact one_ne_zero)
  have hc : IsCompact (K + h ⁻¹' {1}) := hK.add hUc
  have hV : IsClopen (K + h ⁻¹' {1}) := ⟨hc.isClosed, hU.2.add_left⟩
  refine ⟨(K + h ⁻¹' {1}).indicator 1, ⟨(LocallyConstant.indicator (1 : LocallyConstant X ℂ) hV).isLocallyConstant,
    HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩, fun x hx => ?_⟩
  exact Set.indicator_of_mem (show x ∈ K + h ⁻¹' {1} from ⟨x, hx, 0, h0, add_zero x⟩) _

section Est

variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem continuous_toMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

omit [Fintype κ] in
theorem continuous_infPart : Continuous fun (x : κ → AdeleRing (𝓞 F) F) (i : κ) =>
    InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 :=
  continuous_pi fun i => (continuous_toMixed F).comp (continuous_fst.comp (continuous_apply i))

omit [Fintype κ] in
theorem continuous_finPart : Continuous fun (x : κ → AdeleRing (𝓞 F) F) (i : κ) => (x i).2 :=
  continuous_pi fun i => continuous_snd.comp (continuous_apply i)

theorem exists_majorant {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F))
    {D : Set (κ → AdeleRing (𝓞 F) F)} (hD : IsCompact D) :
    ∃ (s : Finset (ℕ × ℕ)) (u : (κ → F) → ℝ), Summable u ∧ (∀ ξ, 0 ≤ u ξ) ∧
      ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, ∀ x ∈ D, ∀ ξ : κ → F,
        ‖pureA F f g ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) + x)‖ ≤
          u ξ * (s.sup (schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)) f := by
  have hK : IsCompact (tsupport g + -((fun (x : κ → AdeleRing (𝓞 F) F) (i : κ) => (x i).2) '' D)) :=
    hg.2.isCompact.add (hD.image (continuous_finPart F)).neg
  obtain ⟨g', hg', h1⟩ := exists_SB_one (ThetaAdm.indicator_mem_SB F (κ := κ))
    (Set.indicator_of_mem (Set.mem_univ_pi.mpr fun i => SetLike.mem_coe.mpr (zero_mem _)) _) hK
  obtain ⟨k, hk⟩ := ThetaAdm.summable_weight F hg'
  obtain ⟨R, hR⟩ := hD.exists_bound_of_continuousOn (continuous_infPart F (κ := κ)).continuousOn
  obtain ⟨C, hC⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨Finset.Iic (k, 0), _, hk.mul_left (2 ^ k * (1 + |R|) ^ k * C), fun ξ => by positivity, fun f x hx ξ => ?_⟩
  set p := ((Finset.Iic (k, 0)).sup (schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)) f
  have hp : 0 ≤ p := apply_nonneg _ _
  set a : κ → mixedEmbedding.mixedSpace F := fun i => mixedEmbedding F (ξ i)
  set b : κ → mixedEmbedding.mixedSpace F := fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1
  set c : κ → FiniteAdeleRing (𝓞 F) F := fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)
  set d : κ → FiniteAdeleRing (𝓞 F) F := fun i => (x i).2
  have e : pureA F f g ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) + x) = f (a + b) * g (c + d) := by
    unfold pureA
    congr 2
    funext i
    refine (map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) (algebraMap F _ (ξ i)) (x i).1).trans ?_
    rw [← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp F]
    rfl
  rw [e]
  by_cases h0 : g (c + d) = 0
  · rw [h0, mul_zero, norm_zero]; positivity
  have hc : g' c = 1 := h1 c ⟨c + d, subset_tsupport _ h0, -d, by simpa using ⟨x, hx, rfl⟩, by simp⟩
  have h2 : (1 + ‖a + b‖) ^ k * ‖f (a + b)‖ ≤ 2 ^ k * p := by
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, 0)) (k := k) (n := 0) le_rfl le_rfl f (a + b)
    rw [norm_iteratedFDeriv_zero] at this
    exact this
  have h3 : 1 + ‖a‖ ≤ (1 + |R|) * (1 + ‖a + b‖) := by
    have := norm_sub_le (a + b) b
    rw [add_sub_cancel_right] at this
    have h4 : ‖b‖ ≤ |R| := (hR x hx).trans (le_abs_self R)
    nlinarith [mul_nonneg (abs_nonneg R) (norm_nonneg (a + b))]
  have h4 := pow_le_pow_left₀ (by positivity) h3 k
  rw [hc, norm_one, one_mul, norm_mul, mul_right_comm _ _ p, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc ‖f (a + b)‖ * ‖g (c + d)‖ * (1 + ‖a‖) ^ k ≤ ‖f (a + b)‖ * C * ((1 + |R|) * (1 + ‖a + b‖)) ^ k := by
        gcongr; exact hC _
    _ = (1 + |R|) ^ k * C * ((1 + ‖a + b‖) ^ k * ‖f (a + b)‖) := by rw [mul_pow]; ring
    _ ≤ (1 + |R|) ^ k * C * (2 ^ k * p) := by gcongr
    _ = _ := by ring

variable {F} [Invertible (2 : AdeleRing (𝓞 F) F)] {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ}

theorem norm_schr (hψ : ∀ x, ‖ψ x‖ = 1) (w : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F))
    (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (x : κ → AdeleRing (𝓞 F) F) : ‖schr ψ w Φ x‖ = ‖Φ (x + w.1)‖ := by
  rw [schr, norm_mul, hψ, one_mul]

theorem theta_bound (hψ : ∀ x, ‖ψ x‖ = 1) {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) {D : Set ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F))}
    (hD : IsCompact D) : ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧
      ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, ∀ w ∈ D, ‖thetaSum F (schr ψ w (pureA F f g))‖ ≤
        C * (s.sup (schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)) f := by
  obtain ⟨s, u, hu, hu0, h⟩ := exists_majorant F hg (hD.image continuous_fst)
  refine ⟨s, ∑' ξ, u ξ, tsum_nonneg hu0, fun f w hw => ?_⟩
  refine tsum_of_norm_bounded (hu.hasSum.mul_right _) fun ξ => ?_
  rw [norm_schr hψ]
  exact h f _ ⟨w, hw, rfl⟩ ξ

theorem theta_continuous_pure [LocallyCompactSpace (AdeleRing (𝓞 F) F)] (hc : Continuous ψ) (hψ : ∀ x, ‖ψ x‖ = 1)
    {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F))
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) :
    Continuous fun w => thetaSum F (schr ψ w (pureA F f g)) := by
  refine continuous_iff_continuousAt.mpr fun w₀ => ?_
  obtain ⟨D, hD, hw₀⟩ := exists_compact_mem_nhds w₀
  obtain ⟨s, u, hu, -, h⟩ := exists_majorant F hg (hD.image continuous_fst)
  have hp : Continuous (pureA F f g) :=
    (f.continuous.comp (continuous_infPart F)).mul (hg.1.continuous.comp (continuous_finPart F))
  refine ContinuousOn.continuousAt (continuousOn_tsum (fun ξ => Continuous.continuousOn ?_) (hu.mul_right _)
    fun ξ w hw => (norm_schr hψ _ _ _).le.trans (h f _ ⟨w, hw, rfl⟩ ξ)) hw₀
  unfold schr
  refine (hc.comp ?_).mul (hp.comp (continuous_const.add continuous_fst))
  exact (continuous_const.dotProduct continuous_snd).add (continuous_const.mul (continuous_fst.dotProduct continuous_snd))

end Est

section Alg

variable {F : Type} [Field F] {R : Type} [CommRing R] [Algebra F R] {κ : Type} [Fintype κ]

def omL (R : Type) [CommRing R] (κ : Type) [Fintype κ] :
    ((κ → R) × (κ → R)) →ₗ[R] ((κ → R) × (κ → R)) →ₗ[R] R :=
  LinearMap.mk₂ R (fun w w' => w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)
    (fun _ _ _ => by simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring)
    (fun _ _ _ => by simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring)
    (fun _ _ _ => by simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring)
    (fun _ _ _ => by simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring)

theorem omL_apply (w w' : (κ → R) × (κ → R)) : omL R κ w w' = w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2 := rfl

def emb (R : Type) [CommRing R] [Algebra F R] : ((κ → F) × (κ → F)) →ₗ[F] ((κ → R) × (κ → R)) :=
  ((Algebra.linearMap F R).compLeft κ).prodMap ((Algebra.linearMap F R).compLeft κ)

omit [Fintype κ] in
theorem emb_apply (w : (κ → F) × (κ → F)) :
    emb R w = (fun i => algebraMap F R (w.1 i), fun i => algebraMap F R (w.2 i)) := rfl

theorem omL_emb (u v : (κ → F) × (κ → F)) : omL R κ (emb R u) (emb R v) = algebraMap F R (omL F κ u v) := by
  simp [omL_apply, emb_apply, dotProduct]

omit [Fintype κ] in
theorem emb_sum {ι : Type} [Fintype ι] (c : ι → F) (b : ι → (κ → F) × (κ → F)) :
    emb R (∑ i, c i • b i) = ∑ i, algebraMap F R (c i) • emb R (b i) := by
  simp [map_sum, algebraMap_smul]

theorem exists_omL_eq (φ : ((κ → F) × (κ → F)) →ₗ[F] F) : ∃ w, ∀ v, omL F κ v w = φ v := by
  refine ⟨(fun i => -φ (0, Pi.single i 1), fun i => φ (Pi.single i 1, 0)), fun v => ?_⟩
  have e : v = ∑ i, v.1 i • ((Pi.single i 1, 0) : (κ → F) × (κ → F)) + ∑ i, v.2 i • ((0, Pi.single i 1) : (κ → F) × (κ → F)) := by
    ext j <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [e, map_add, map_sum, map_sum]
  simp only [map_smul, smul_eq_mul, omL_apply, dotProduct, neg_mul, Finset.sum_neg_distrib, sub_neg_eq_add]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

variable [Invertible (2 : R)] (ψ : AddChar R ℂ)

theorem schr_schr (w w' : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (⅟(2 : R) * omL R κ w w') • schr ψ (w + w') φ := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul, omL_apply, Prod.fst_add, Prod.snd_add, add_assoc x, ← mul_assoc,
    ← AddChar.map_add_eq_mul, add_dotProduct, dotProduct_add]
  congr 2
  linear_combination (-(w.1 ⬝ᵥ w'.2)) * invOf_two_add_invOf_two (R := R)

theorem schr_comm (w w' : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (omL R κ w w') • schr ψ w' (schr ψ w φ) := by
  rw [schr_schr, schr_schr, smul_smul, ← AddChar.map_add_eq_mul, add_comm w' w]
  congr 2
  simp only [omL_apply]
  linear_combination (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) * invOf_two_add_invOf_two (R := R)

def schrLin (w : (κ → R) × (κ → R)) : ((κ → R) → ℂ) →ₗ[ℂ] ((κ → R) → ℂ) where
  toFun := schr ψ w
  map_add' _ _ := by funext x; simp [schr, mul_add]
  map_smul' _ _ := by funext x; simp [schr, mul_left_comm]

theorem schr_zero (φ : (κ → R) → ℂ) : schr ψ 0 φ = φ := by
  funext x; simp [schr]

end Alg

theorem exists_avg {F : Type} [Field F] {A : Type} [CommRing A] [Algebra F A] {κ : Type} [Fintype κ]
    [Invertible (2 : A)] [TopologicalSpace A] [IsTopologicalRing A] {ψ : AddChar A ℂ} (hc : Continuous ψ)
    (hψ : ∀ x, ‖ψ x‖ = 1) (htriv : ∀ a : F, ψ (algebraMap F A a) = 1)
    (hann : ∀ x : A, (∀ a : F, ψ (x * algebraMap F A a) = 1) → ∃ b : F, x = algebraMap F A b)
    (hcl : IsClosed ((algebraMap F A).range.toAddSubgroup : Set A)) {D₀ : Set A} (hD₀ : IsCompact D₀)
    (hD₀' : ∀ x, ∃ k : F, x - algebraMap F A k ∈ D₀) (Sp : Submodule ℂ ((κ → A) → ℂ)) (θ : ((κ → A) → ℂ) →ₗ[ℂ] ℂ)
    (hpres : ∀ w, ∀ Φ ∈ Sp, schr ψ w Φ ∈ Sp)
    (hrat : ∀ w : (κ → F) × (κ → F), ∀ Φ ∈ Sp, θ (schr ψ (emb A w) Φ) = θ Φ)
    (hcont : ∀ Φ ∈ Sp, Continuous fun w => θ (schr ψ w Φ)) (L : Submodule F ((κ → F) × (κ → F)))
    (hL : ∀ w ∈ L, ∀ w' ∈ L, w.1 ⬝ᵥ w'.2 = w'.1 ⬝ᵥ w.2) :
    ∃ l : ((κ → A) → ℂ) →ₗ[ℂ] ℂ,
      (∃ D, IsCompact D ∧ ∀ Φ ∈ Sp, ∀ B : ℝ, (∀ w ∈ D, ‖θ (schr ψ w Φ)‖ ≤ B) → ‖l Φ‖ ≤ B) ∧
      ((∀ Φ ∈ Sp, l Φ = 0) → ∀ Φ ∈ Sp, θ Φ = 0) ∧
      (∀ y ∈ Submodule.span A (emb A '' (L : Set ((κ → F) × (κ → F)))), ∀ Φ ∈ Sp, l (schr ψ y Φ) = l Φ) ∧
      ∀ (s : ((κ → F) × (κ → F)) ≃ₗ[F] ((κ → F) × (κ → F))) (sA : ((κ → A) × (κ → A)) →ₗ[A] ((κ → A) × (κ → A)))
        (T : Module.End ℂ ((κ → A) → ℂ)) (a : ℂ), (∀ w, sA (emb A w) = emb A (s w)) → (∀ w, s w ∈ L ↔ w ∈ L) →
        (∀ Φ ∈ Sp, T Φ ∈ Sp) → (∀ w, ∀ Φ ∈ Sp, T (schr ψ w Φ) = schr ψ (sA w) (T Φ)) →
        (∀ Φ ∈ Sp, θ (T Φ) = a * θ Φ) → ∀ Φ ∈ Sp, l (T Φ) = a * l Φ := by
  let n := Module.finrank F L
  let b : Module.Basis (Fin n) F L := Module.finBasis F L
  let β : (Fin n → A) →ₗ[A] ((κ → A) × (κ → A)) := Fintype.linearCombination A fun i => emb A (b i : (κ → F) × (κ → F))
  have hβ : ∀ t, β t = ∑ i, t i • emb A (b i : (κ → F) × (κ → F)) := fun t => rfl
  clear_value β
  have hβc : Continuous β := by
    rw [show ⇑β = fun t => ∑ i, t i • emb A (b i : (κ → F) × (κ → F)) from funext hβ]
    fun_prop
  have hβom : ∀ t w, omL A κ (β t) (emb A w) = ∑ i, t i * algebraMap F A (omL F κ (b i) w) := fun t w => by
    simp only [hβ, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, omL_emb, smul_eq_mul]
  have hiso : ∀ t t', omL A κ (β t) (β t') = 0 := fun t t' => by
    rw [hβ t', map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_smul, hβom, Finset.sum_eq_zero, smul_zero]
    intro i _
    rw [omL_apply, hL _ (b i).2 _ (b j).2, sub_self, map_zero, mul_zero]
  have hadd : ∀ t t' Φ, schr ψ (β t) (schr ψ (β t') Φ) = schr ψ (β (t + t')) Φ := fun t t' Φ => by
    rw [schr_schr, hiso, mul_zero, AddChar.map_zero_eq_one, one_smul, map_add]
  have hβL : ∀ w : L, emb A (w : (κ → F) × (κ → F)) = β fun i => algebraMap F A (b.repr w i) := fun w => by
    rw [hβ, ← emb_sum]
    refine congrArg (emb A) ?_
    have h := congrArg L.subtype (b.sum_repr w)
    rw [map_sum] at h
    simp only [map_smul, Submodule.subtype_apply] at h
    exact h.symm
  let Γ : AddSubgroup (Fin n → A) := AddSubgroup.pi Set.univ fun _ => (algebraMap F A).range.toAddSubgroup
  have hΓ : ∀ γ, γ ∈ Γ ↔ ∃ c : Fin n → F, γ = fun i => algebraMap F A (c i) := fun γ => by
    constructor
    · intro h
      choose c hc using fun i => h i trivial
      exact ⟨c, funext fun i => (hc i).symm⟩
    · rintro ⟨c, rfl⟩ i _
      exact ⟨c i, rfl⟩
  obtain ⟨M, hMb, hMt, hMσ, hM0⟩ := exists_mean Γ (isClosed_set_pi fun _ _ => hcl)
    (isCompact_univ_pi fun _ : Fin n => hD₀) (fun x => by
      choose c hc using fun i => hD₀' (x i)
      exact ⟨_, (hΓ _).mpr ⟨c, rfl⟩, fun i _ => hc i⟩)
  let fn : ((κ → A) → ℂ) →ₗ[ℂ] ((Fin n → A) → ℂ) := LinearMap.pi fun t => θ ∘ₗ schrLin ψ (β t)
  have hfn : ∀ Φ t, fn Φ t = θ (schr ψ (β t) Φ) := fun Φ t => rfl
  clear_value fn
  have hper : ∀ Φ ∈ Sp, IsPer Γ (fn Φ) := fun Φ hΦ => by
    constructor
    · rw [funext (hfn Φ)]
      exact (hcont Φ hΦ).comp hβc
    · intro γ hγ t
      obtain ⟨c, rfl⟩ := (hΓ γ).mp hγ
      rw [hfn, hfn, add_comm, ← hadd, hβ, ← emb_sum]
      exact hrat _ _ (hpres _ _ hΦ)
  refine ⟨M ∘ₗ fn, ⟨_, (isCompact_univ_pi fun _ : Fin n => hD₀).image hβc, fun Φ hΦ B hB =>
    hMb _ (hper _ hΦ) _ fun t ht => ?_⟩, fun h0 Φ₀ hΦ₀ => ?_, fun y hy Φ hΦ => ?_,
    fun s sA T a hsA hs hT hTs hTθ Φ hΦ => ?_⟩
  · rw [hfn]
    exact hB _ ⟨t, ht, rfl⟩
  · have := hM0 (Set.range fun (c : Fin n → F) (t : Fin n → A) => ψ (∑ i, t i * algebraMap F A (c i))) ?_
      ⟨0, by funext t; simp⟩ ?_ ?_ ?_ _ (hper _ hΦ₀) ?_
    · have h1 := congrFun this 0
      rwa [hfn, map_zero, schr_zero] at h1
    · rintro _ ⟨c, rfl⟩
      refine ⟨hc.comp (by fun_prop), fun γ hγ t => ?_⟩
      obtain ⟨c', rfl⟩ := (hΓ γ).mp hγ
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, ← map_mul, ← map_sum, AddChar.map_add_eq_mul, htriv,
        mul_one]
    · rintro _ ⟨c, rfl⟩ _ ⟨c', rfl⟩
      refine ⟨c + c', funext fun t => ?_⟩
      simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib, AddChar.map_add_eq_mul, Pi.mul_apply]
    · rintro _ ⟨c, rfl⟩
      refine ⟨-c, funext fun t => ?_⟩
      simp only [Pi.neg_apply, map_neg, mul_neg, Finset.sum_neg_distrib, AddChar.map_neg_eq_inv, Pi.star_apply]
      exact Complex.inv_eq_conj (hψ _)
    · intro x y hxy i _
      obtain ⟨c, hc'⟩ := hann ((-x + y) i) fun a => by
        have h1 := hxy _ ⟨Pi.single i a, rfl⟩
        simp only [Pi.single_apply, apply_ite (algebraMap F A), map_zero, mul_ite, mul_zero, Finset.sum_ite_eq',
          Finset.mem_univ, if_true] at h1
        rw [Pi.add_apply, Pi.neg_apply, add_mul, neg_mul, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv, h1]
        exact inv_mul_cancel₀ (norm_ne_zero_iff.mp (by rw [hψ]; exact one_ne_zero))
      exact ⟨c, hc'.symm⟩
    · rintro _ ⟨c, rfl⟩
      obtain ⟨φ, hφ⟩ := LinearMap.exists_extend (b.constr F c)
      obtain ⟨w, hw⟩ := exists_omL_eq φ
      have hwc : ∀ i, omL F κ (b i) w = c i := fun i => by
        rw [hw]
        simpa using LinearMap.congr_fun hφ (b i)
      refine Eq.trans ?_ (h0 _ (hpres (emb A w) _ hΦ₀))
      refine congrArg M (funext fun t => ?_)
      rw [Pi.mul_apply, hfn, hfn, schr_comm, hβom, map_smul, hrat _ _ (hpres _ _ hΦ₀)]
      simp only [hwc, smul_eq_mul]
  · obtain ⟨t₀, rfl⟩ : y ∈ LinearMap.range β := by
      refine Submodule.span_le.mpr ?_ hy
      rintro _ ⟨w, hw, rfl⟩
      exact ⟨_, (hβL ⟨w, hw⟩).symm⟩
    refine Eq.trans ?_ (hMt _ (hper _ hΦ) t₀)
    refine congrArg M (funext fun t => ?_)
    rw [hfn, hfn, hadd]
  · have hmap : L.map (s : _ →ₗ[F] _) = L := by
      ext w
      rw [Submodule.mem_map_equiv, ← hs, LinearEquiv.apply_symm_apply]
    let sL : L ≃ₗ[F] L := s.ofSubmodules L L hmap
    let S : Matrix (Fin n) (Fin n) A := (LinearMap.toMatrix b b (sL : L →ₗ[F] L)).map (algebraMap F A)
    let S' : Matrix (Fin n) (Fin n) A := (LinearMap.toMatrix b b (sL.symm : L →ₗ[F] L)).map (algebraMap F A)
    have hSS : S * S' = 1 := by
      rw [← Matrix.map_mul, ← LinearMap.toMatrix_comp, LinearEquiv.comp_symm, LinearMap.toMatrix_id,
        Matrix.map_one _ (map_zero _) (map_one _)]
    have hS : ∀ t, β (S *ᵥ t) = sA (β t) := fun t => by
      have h1 : ∀ j, sA (emb A (b j : (κ → F) × (κ → F))) = β fun i => S i j := fun j => by
        refine (hsA _).trans ((hβL (sL (b j))).trans ?_)
        simp [S, LinearMap.toMatrix_apply]
      rw [hβ t, map_sum]
      simp only [map_smul sA, h1, ← map_smul β, ← map_sum β]
      refine congrArg β (funext fun i => ?_)
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    have h2 := hMσ (Matrix.mulVecLin S).toAddMonoidHom (continuous_const.matrix_mulVec continuous_id)
      (fun t => ⟨S' *ᵥ t, by simp [hSS]⟩) (fun γ hγ => by
        obtain ⟨c, rfl⟩ := (hΓ γ).mp hγ
        refine (hΓ _).mpr ⟨LinearMap.toMatrix b b (sL : L →ₗ[F] L) *ᵥ c, funext fun i => ?_⟩
        simp [S, Matrix.mulVec, dotProduct]) _ (hper _ (hT _ hΦ))
    refine h2.symm.trans ?_
    rw [LinearMap.comp_apply, ← smul_eq_mul, ← map_smul]
    refine congrArg M (funext fun t => ?_)
    rw [Pi.smul_apply, hfn, hfn, smul_eq_mul, ← hTθ _ (hpres _ _ hΦ), hTs _ _ hΦ, ← hS]
    rfl

theorem theta_mean : ∀ (F : Type) [Field F] [NumberField F] [LocallyCompactSpace (AdeleRing (𝓞 F) F)] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), Continuous ψ → ψ ≠ 1 → (∀ a : F, ψ (algebraMap F (AdeleRing (𝓞 F) F) a) = 1) → ∀ L : Submodule F ((κ → F) × (κ → F)), (∀ w, w ∈ L ↔ ∀ w' ∈ L, w.1 ⬝ᵥ w'.2 = w'.1 ⬝ᵥ w.2) → ∃ l ∈ (adeleClass F).adm κ, (∃ Φ ∈ schA F κ, l Φ ≠ 0) ∧ (∀ y ∈ Submodule.span (AdeleRing (𝓞 F) F) ((fun w : (κ → F) × (κ → F) => ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (w.1 i), fun i => algebraMap F (AdeleRing (𝓞 F) F) (w.2 i)) : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F))) '' L), ∀ Φ ∈ schA F κ, l (schr ψ y Φ) = l Φ) ∧ ∀ (s : ((κ → F) × (κ → F)) ≃ₗ[F] ((κ → F) × (κ → F))) (sA : ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) →ₗ[AdeleRing (𝓞 F) F] ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F))) (T : Module.End ℂ ((κ → AdeleRing (𝓞 F) F) → ℂ)) (a : ℂ), (∀ w, sA (fun i => algebraMap F (AdeleRing (𝓞 F) F) (w.1 i), fun i => algebraMap F (AdeleRing (𝓞 F) F) (w.2 i)) = (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((s w).1 i), fun i => algebraMap F (AdeleRing (𝓞 F) F) ((s w).2 i))) → (∀ w, s w ∈ L ↔ w ∈ L) → (∀ Φ ∈ schA F κ, T Φ ∈ schA F κ) → (∀ w, ∀ Φ ∈ schA F κ, T (schr ψ w Φ) = schr ψ (sA w) (T Φ)) → (∀ Φ ∈ schA F κ, thetaSum F (T Φ) = a * thetaSum F Φ) → ∀ Φ ∈ schA F κ, l (T Φ) = a * l Φ := by
  intro F _ _ _ _ κ _ ψ hc hne htriv L hL
  obtain ⟨-, ⟨θ, -, hθ⟩, Φ₀, hΦ₀, hΦ₀'⟩ := ThetaAdm.theta_adm F κ
  obtain ⟨hpres, hrat⟩ := AdelicHeis.schr_mem_and_thetaSum F κ ψ hc hne htriv
  obtain ⟨hψ, hann⟩ := AdeleAnn.unitary_and_annihilator_eq F ψ hc hne htriv
  obtain ⟨C₀, hC₀, hC₀'⟩ := GroundTheory.Global.exists_isCompact_forall_exists_sub_mem F
  have hD₀ : IsCompact (C₀ ×ˢ (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) :
      Set (AdeleRing (𝓞 F) F)) := hC₀.prod (GroundTheory.Global.isCompact_integralFiniteAdeles F)
  have hpure : ∀ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ), ∀ g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F),
      pureA F f g ∈ schA F κ := fun f g hg => Submodule.subset_span ⟨f, g, hg, rfl⟩
  have hcont : ∀ Φ ∈ schA F κ, Continuous fun w => θ (schrLin ψ w Φ) := fun Φ hΦ => by
    induction hΦ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, g, hg, rfl⟩ := hx
      exact (theta_continuous_pure hc hψ hg f).congr fun w => (hθ _ (hpres w _ (hpure f g hg))).symm
    | zero => simp only [map_zero]; exact continuous_const
    | add x y _ _ hx hy => simp only [map_add]; exact hx.add hy
    | smul c x _ hx => simp only [map_smul]; exact hx.const_smul c
  obtain ⟨l, ⟨D, hD, hb⟩, h0, hinv, heig⟩ := exists_avg hc hψ htriv hann (GroundTheory.Global.isClosed_principalSubgroup F)
    hD₀ hC₀' (schA F κ) θ hpres (fun w Φ hΦ => by rw [hθ _ (hpres _ _ hΦ), hθ _ hΦ]; exact hrat w Φ) hcont L
    fun w hw => (hL w).mp hw
  refine ⟨l, fun g hg => ?_, ?_, hinv, fun s sA T a hsA hs hT hTs hTθ => heig s sA T a hsA hs hT hTs fun Φ hΦ => ?_⟩
  · refine ⟨SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) (fun f => l (pureA F f g)) (fun f f' => ?_)
      (fun c f => ?_) ?_, fun f => rfl⟩
    · rw [← map_add]
      refine congrArg l (funext fun x => ?_)
      simp [pureA, add_mul]
    · rw [← map_smul]
      refine congrArg l (funext fun x => ?_)
      simp [pureA, mul_assoc]
    · obtain ⟨s, C, hC, h⟩ := theta_bound hψ hg hD
      refine ⟨s, C, hC, fun f => hb _ (hpure f g hg) _ fun w hw => ?_⟩
      rw [hθ _ (hpres _ _ (hpure f g hg))]
      exact h f w hw
  · by_contra h1
    push Not at h1
    exact hΦ₀' ((hθ _ hΦ₀).symm.trans (h0 h1 _ hΦ₀))
  · rw [hθ _ (hT _ hΦ), hθ _ hΦ, hTθ _ hΦ]

end GlobalTheory.CompanionTheory.ThetaAvg
