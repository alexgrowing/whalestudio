import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormEqXModMonicOfAdicCompleteInvolution
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryMemIntegralUnitaryDoubleCosetOfGLnDoubleC

noncomputable section

namespace GlobalTheory.LFun

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU
open Formalism.MainNotions.SchurIrreducible (IsSplit IsUnram)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}

namespace InertChart

theorem under_eq_iff (hw : IsInertAt F E v w) (u : HeightOneSpectrum (𝓞 E)) : u.under (𝓞 F) = v ↔ u = w := by
  have h' : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = w.asIdeal := hw
  constructor
  · rintro rfl
    exact (HeightOneSpectrum.ext (w.isMaximal.eq_of_le u.isPrime.ne_top (h' ▸ Ideal.map_comap_le))).symm
  · rintro rfl
    exact (HeightOneSpectrum.ext (v.isMaximal.eq_of_le (u.under (𝓞 F)).isPrime.ne_top
      (Ideal.map_le_iff_le_comap.1 h'.le))).symm

theorem absNorm_eq (h2 : Module.finrank F E = 2) (hw : IsInertAt F E v w) :
    Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ 2 := by
  rw [← show Ideal.map _ v.asIdeal = w.asIdeal from hw, Ideal.absNorm_algebraMap, ← h2]
  congr 1
  exact (Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 F) F (𝓞 E) E).symm

theorem not_map_le_sq (hw : IsInertAt F E v w) :
    ¬ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal ≤ w.asIdeal ^ 2 := by
  rw [show Ideal.map _ v.asIdeal = w.asIdeal from hw]
  exact (Ideal.pow_lt_self _ w.ne_bot w.isPrime.ne_top 2 le_rfl).not_ge

theorem isSplit_or_isInertAt (hv : IsUnram (E := E) v) : IsSplit (E := E) v ∨ ∃ w, IsInertAt F E v w := by
  classical
  refine (em _).imp_right fun hs => ?_
  set I := Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal with hI
  have hI0 : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]
    exact v.ne_bot
  have := v.isMaximal
  obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hle : I ≤ Q := Ideal.map_le_iff_le_comap.2 hQv.over.le
  let P : HeightOneSpectrum (𝓞 E) := ⟨Q, hQ.isPrime, fun h0 => hI0 (le_bot_iff.1 (h0 ▸ hle))⟩
  have h1 := hv P hQv.over.symm
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal Q v.ne_bot] at h1
  have h2 : ¬ I ≤ Q ^ 2 := fun h => (Ideal.ramificationIdx'_ne_one_iff hle).2 h h1
  have hfac : ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors I, p = Q := by
    intro p hp
    obtain ⟨hpp, hpl⟩ := (Ideal.mem_normalizedFactors_iff hI0).1 hp
    by_contra hne
    exact hs ⟨⟨p, hpp, fun h0 => hI0 (le_bot_iff.1 (h0 ▸ hpl))⟩, P, fun e => hne (congrArg (·.asIdeal) e),
      (v.isMaximal.eq_of_le (Ideal.comap_ne_top _ hpp.ne_top) (Ideal.map_le_iff_le_comap.1 hpl)).symm,
      hQv.over.symm⟩
  obtain ⟨n, hn⟩ : ∃ n, I = Q ^ n := by
    refine ⟨Multiset.card (UniqueFactorizationMonoid.normalizedFactors I), ?_⟩
    conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self hI0]
    rw [Multiset.eq_replicate_card.2 hfac, Multiset.prod_replicate, Multiset.card_replicate]
  refine ⟨P, ?_⟩
  rcases n with _ | _ | n
  · rw [hn, pow_zero, Ideal.one_eq_top, top_le_iff] at hle
    exact absurd hle hQ.ne_top
  · exact hn.trans (pow_one _)
  · exact absurd (hn ▸ Ideal.pow_le_pow_right (by omega)) h2

variable {σ : E →ₐ[F] E}

theorem conj_conj (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem conj_ne (h : IsCMExt F E σ) : ¬ ∀ x, σ x = x := fun h1 => by
  have := h.2.1
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply IsTotallyComplex.complexEmbedding_not_isReal τ
  rw [ComplexEmbedding.isReal_iff]
  ext y
  exact (h.2.2.2 τ y).symm.trans (congrArg τ (h1 y))

theorem exists_conj_sub_unit (h : IsCMExt F E σ) (hw : IsInertAt F E v w) :
    ∃ x : 𝓞 E, w.valuation E (σ x - x) = 1 := by
  have : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h.2.2.1 }
  have : IsGalois F E := inferInstance
  have : w.asIdeal.LiesOver v.asIdeal := ⟨congrArg (·.asIdeal) ((under_eq_iff hw w).2 rfl).symm⟩
  have := v.isPrime
  have := w.isPrime
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[F] E) v.asIdeal w.asIdeal
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal (E ≃ₐ[F] E),
    ← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot,
    not_ne_iff.1 (mt (Ideal.ramificationIdx'_ne_one_iff (le_of_eq hw)).1 (not_map_le_sq hw))] at hcard
  let s : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext (conj_conj h)) (AlgHom.ext (conj_conj h))
  by_contra hn
  have hs : s ∈ w.asIdeal.inertia (E ≃ₐ[F] E) := AddSubgroup.mem_inertia.2 fun x => by
    by_contra hx
    exact hn ⟨x, (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E) w).2 hx⟩
  rw [Subgroup.eq_bot_of_card_eq _ hcard, Subgroup.mem_bot] at hs
  exact conj_ne h fun x => congrArg (fun t : E ≃ₐ[F] E => t x) hs

theorem continuous_complMap (h : w.under (𝓞 F) = v) : Continuous (complMap h) := by
  subst h
  refine continuous_of_continuousAt_zero _ (Metric.tendsto_nhds.2 fun ε hε => ?_)
  obtain ⟨ϖ, hϖ⟩ := exists_isUnifV w
  have h1 : ‖ϖ‖ < 1 := Valued.toNormedField.norm_lt_one_iff.2 (by rw [hϖ]; decide)
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε h1
  filter_upwards [(GlobalTheory.Idele.isOpen_valued_le (K := F) (w.under (𝓞 F)) (-(m : ℤ))).mem_nhds (x := 0) (by simp)]
    with a ha
  rw [map_zero, dist_zero_right]
  refine (Valued.toNormedField.norm_le_iff.2 ?_).trans_lt ((norm_pow ϖ m).trans_lt hm)
  refine (GlobalTheory.AdeleBaseChange.locMap_valued w m a ha).trans_eq ?_
  rw [map_pow, hϖ]
  change _ = WithZero.exp (-1 : ℤ) ^ m
  rw [← WithZero.exp_nsmul]
  simp

theorem toCompl_surjective (h : w.under (𝓞 F) = v) : Function.Surjective (toCompl h) := fun y => by
  obtain ⟨Y, hY⟩ := (finAdEquiv F E).surjective (singleFin w y)
  exact ⟨_, (finAdEquiv_apply h Y).symm.trans (hY ▸ evalV_singleFin_self w y)⟩

theorem exists_adele (hw : IsInertAt F E v w) (h : w.under (𝓞 F) = v) (y : Fv F v ⊗[F] E) :
    ∃ Y : Af F ⊗[F] E, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) Y = y ∧
      finAdEquiv F E Y w = toCompl h y ∧ ∀ u, u ≠ w → finAdEquiv F E Y u = 0 := by
  have h1 := GlobalTheory.AutFunCompare.map_tensNU_self _ _ (singleFin_mul v) (evalV_singleFin_self v) y
  refine ⟨_, h1, by rw [finAdEquiv_apply h, h1], fun u hu => ?_⟩
  rw [finAdEquiv_apply rfl, GlobalTheory.AutFunCompare.map_tensNU_zero _ _ _
    (evalV_singleFin_ne (mt (under_eq_iff hw u).1 hu)), map_zero]

theorem toCompl_bijective (hw : IsInertAt F E v w) (h : w.under (𝓞 F) = v) : Function.Bijective (toCompl h) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun y hy => ?_, toCompl_surjective h⟩
  obtain ⟨Y, h1, h2, h3⟩ := exists_adele hw h y
  have : finAdEquiv F E Y = 0 := FiniteAdeleRing.ext _ fun u => by
    by_cases e : u = w
    · subst e; exact h2.trans hy
    · exact h3 u e
  rw [← h1, (map_eq_zero_iff _ (finAdEquiv F E).injective).1 this, map_zero]

theorem toCompl_mem (h : w.under (𝓞 F) = v) {y : Fv F v ⊗[F] E} (hy : y ∈ intLoc F E v) : toCompl h y ∈ Ov E w :=
  intLoc_induction (p := fun y => toCompl h y ∈ Ov E w)
    (fun _ ha x => mul_mem (complMap_mem h ha) (GlobalTheory.AdeleBaseChange.algebraMap_int_mem x w))
    (by rw [map_zero]; exact zero_mem _) (fun _ _ h h' => by rw [map_add]; exact add_mem h h')
    (fun _ h => by rw [map_neg]; exact neg_mem h) hy

theorem mem_intLoc_iff (hw : IsInertAt F E v w) (h : w.under (𝓞 F) = v) (y : Fv F v ⊗[F] E) :
    y ∈ intLoc F E v ↔ toCompl h y ∈ Ov E w := by
  refine ⟨toCompl_mem h, fun hy => ?_⟩
  obtain ⟨Y, h1, h2, h3⟩ := exists_adele hw h y
  let c := (Algebra.TensorProduct.comm F E (Af F)).toRingEquiv
  have hι : ∀ x a, ((toFinAd F E).comp c.toRingHom) (x ⊗ₜ[F] a) =
      algebraMap E _ x * GlobalTheory.AdeleBaseChange.adMap F E a := fun x a => (toFinAd_tmul a x).trans (mul_comm _ _)
  have h4 := GlobalTheory.AdeleBaseChange.mem_int_of_map hι (y := c.symm Y) fun u => by
    change finAdEquiv F E (c (c.symm Y)) u ∈ _
    rw [c.apply_symm_apply]
    by_cases e : u = w
    · subst e; rw [h2]; exact hy
    · rw [h3 u e]; exact zero_mem _
  obtain ⟨m, g, hg⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
  obtain ⟨r, hr, e⟩ := P.levelaf_decomp g hg h4
  rw [← h1, ← c.apply_symm_apply Y, e, map_sum, map_sum]
  exact sum_mem fun j _ => tmul_mem_intLoc (hr j v) (g j)

def complEquiv (hw : IsInertAt F E v w) (h : w.under (𝓞 F) = v) : Fv F v ⊗[F] E ≃+* w.adicCompletion E :=
  RingEquiv.ofBijective _ (toCompl_bijective hw h)

theorem continuous_complEquiv (hw : IsInertAt F E v w) (h : w.under (𝓞 F) = v) :
    Continuous (complEquiv hw h) ∧ Continuous (complEquiv hw h).symm := by
  letI : Algebra (Fv F v) (w.adicCompletion E) := (complMap h).toAlgebra
  haveI : ContinuousSMul (Fv F v) (w.adicCompletion E) := continuousSMul_of_algebraMap _ _ (continuous_complMap h)
  letI : NontriviallyNormedField (Fv F v) := Valued.toNontriviallyNormedField _ _
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  let f : (Fv F v ⊗[F] E) ≃ₐ[Fv F v] w.adicCompletion E :=
    { complEquiv hw h with commutes' := fun a => (toCompl_tmul h a 1).trans (by rw [map_one, mul_one]; rfl) }
  have : FiniteDimensional (Fv F v) (w.adicCompletion E) := f.toLinearEquiv.finiteDimensional
  have : IsModuleTopology (Fv F v) (w.adicCompletion E) := isModuleTopologyOfFiniteDimensional
  exact ⟨IsModuleTopology.continuous_of_linearMap f.toLinearMap,
    IsModuleTopology.continuous_of_linearMap f.symm.toLinearMap⟩

theorem existsUnique_isConjAt (σ : E →ₐ[F] E) (hw : IsInertAt F E v w) (h : w.under (𝓞 F) = v) :
    ∃! c, IsConjAt σ h c := by
  let e := complEquiv hw h
  refine ⟨(toCompl h).comp ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ).comp e.symm.toRingHom), fun y =>
    congrArg (fun z => toCompl h (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ z)) (e.symm_apply_apply y), fun c hc => RingHom.ext fun x => ?_⟩
  obtain ⟨y, rfl⟩ := toCompl_surjective h x
  exact (hc y).trans (congrArg (fun z => toCompl h (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ z)) (e.symm_apply_apply y)).symm

variable {h : w.under (𝓞 F) = v} {c : w.adicCompletion E →+* w.adicCompletion E}

theorem conj_algebraMap (hc : IsConjAt σ h c) (x : E) : c (algebraMap E _ x) = algebraMap E _ (σ x) := by
  have := hc (1 ⊗ₜ x)
  rwa [show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ ((1 : Fv F v) ⊗ₜ[F] x) = 1 ⊗ₜ σ x from rfl, toCompl_tmul, toCompl_tmul,
    map_one, one_mul, one_mul] at this

theorem conj_mem (hw : IsInertAt F E v w) (hc : IsConjAt σ h c) {x : w.adicCompletion E} (hx : x ∈ Ov E w) :
    c x ∈ Ov E w := by
  obtain ⟨y, rfl⟩ := toCompl_surjective h x
  rw [hc]
  exact toCompl_mem h (sigR_mem_intLoc σ ((mem_intLoc_iff hw h y).2 hx))

theorem exists_isUnramInv (hσ : IsCMExt F E σ) (hw : IsInertAt F E v w) (hc : IsConjAt σ h c) :
    ∃ ϖ, IsUnramInv ϖ c (qV F v) := by
  have hval : ∀ a : E, Valued.v (algebraMap E (w.adicCompletion E) a) = w.valuation E a := fun a =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
  obtain ⟨s, hs, hs2⟩ := SetLike.not_le_iff_exists.1 (mt Ideal.map_le_iff_le_comap.2 (not_map_le_sq hw))
  have hs1 : algebraMap (𝓞 F) (𝓞 E) s ∈ w.asIdeal := hw ▸ Ideal.mem_map_of_mem _ hs
  set ϖ : w.adicCompletion E := algebraMap E _ (algebraMap (𝓞 F) (𝓞 E) s : E) with hϖ
  have h1 : c ϖ = ϖ := (conj_algebraMap hc _).trans (congrArg _ (σ.commutes (s : F)))
  have h2 : Valued.v ϖ = WithZero.exp (-1 : ℤ) := by
    rw [hϖ, hval, HeightOneSpectrum.valuation_of_algebraMap]
    have a := (w.intValuation_le_pow_iff_mem _ 1).2 (by rwa [pow_one])
    have b := not_le.1 (mt (w.intValuation_le_pow_iff_mem _ 2).1 hs2)
    have h0 : w.intValuation (algebraMap (𝓞 F) (𝓞 E) s) ≠ 0 := b.ne_bot
    rw [← WithZero.exp_log h0] at a b ⊢
    rw [WithZero.exp_le_exp] at a
    rw [WithZero.exp_lt_exp] at b
    congr 1
    omega
  have h3 : ∀ u, Valued.v u = 1 → Valued.v (c u) = 1 := fun u hu => by
    have a : Valued.v (c u) ≤ 1 := conj_mem hw hc hu.le
    have b : Valued.v (c u⁻¹) ≤ 1 := conj_mem hw hc (show Valued.v u⁻¹ ≤ 1 by rw [map_inv₀, hu, inv_one])
    have h0 : u ≠ 0 := fun h0 => by simp [h0] at hu
    rw [map_inv₀, map_inv₀, inv_le_one₀ (by simpa [pos_iff_ne_zero] using h0)] at b
    exact le_antisymm a b
  refine ⟨ϖ, fun x => ?_, fun x => ?_, h1, h2, ?_, one_lt_absNorm v, ?_⟩
  · obtain ⟨y, rfl⟩ := toCompl_surjective h x
    rw [hc, hc]
    congr 1
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (conj_conj hσ x)
    | add x y hx hy => simp only [map_add, hx, hy]
  · by_cases h0 : x = 0
    · simp [h0]
    have h0' : Valued.v x ≠ 0 := by simpa using h0
    have a : Valued.v (x * ϖ ^ WithZero.log (Valued.v x)) = 1 := by
      rw [map_mul, map_zpow₀, h2, ← WithZero.exp_zsmul, ← WithZero.exp_log h0', ← WithZero.exp_add]
      simp
    have b := h3 _ a
    rw [map_mul, map_zpow₀, h1, ← a, map_mul, map_mul] at b
    exact mul_right_cancel₀ (by rw [map_zpow₀, h2]; exact zpow_ne_zero _ WithZero.exp_ne_zero) b
  · obtain ⟨x, hx⟩ := exists_conj_sub_unit hσ hw
    exact ⟨algebraMap E _ (x : E), GlobalTheory.AdeleBaseChange.algebraMap_int_mem x w, by
      rw [conj_algebraMap hc, ← map_sub, hval, hx]⟩
  · exact (P.tjcosets_card_residue w).trans (absNorm_eq hσ.2.2.1 hw)

variable {n : ℕ}

theorem exists_norm {ϖ : w.adicCompletion E} {q : ℕ} (hU : IsUnramInv ϖ c q) {B : GL (Fin n) (w.adicCompletion E)}
    (hB : B ∈ KGL w n) (hB' : cT c B.1 = B.1) : ∃ k ∈ KGL w n, cT c k.1 * k.1 = B.1 := by
  obtain ⟨hcc, hv, -, -, ⟨x, hx1, hx2⟩, -⟩ := hU
  obtain ⟨B, rfl⟩ := hB
  have := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers w
  have : Finite (w.adicCompletionIntegers E ⧸ IsLocalRing.maximalIdeal (w.adicCompletionIntegers E)) :=
    GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers w
  let ι := (w.adicCompletionIntegers E).subtype
  let d : w.adicCompletionIntegers E →+* w.adicCompletionIntegers E :=
    (c.comp ι).codRestrict (w.adicCompletionIntegers E) fun x => by
      change Valued.v (c x) ≤ 1
      rw [hv]; exact x.2
  have hd : ∀ x, d (d x) = x := fun x => Subtype.ext (hcc x)
  have hω : IsUnit ((⟨x, hx1⟩ : w.adicCompletionIntegers E) - d ⟨x, hx1⟩) := by
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    change Valued.v (x - c x) = 1
    rw [Valuation.map_sub_swap, hx2]
  have h1 : cT d B.1 = B.1 := Matrix.ext fun i j => Subtype.ext (congrFun (congrFun hB' i) j)
  obtain ⟨p, hp⟩ := GlobalTheory.UnitaryDoubleCoset.exists_poly_norm hd
    (GlobalTheory.InertNorm.exists_dvd_mul_map_sub_X (w.adicCompletionIntegers E) (IsLocalRing.maximalIdeal _) d hd
      (fun x hx hu => hx (by simpa [hd] using hu.map d)) ⟨_, hω⟩) h1 B.isUnit
  have h2 : IsUnit (Polynomial.aeval B.1 p) := isUnit_of_mul_isUnit_right (hp ▸ B.isUnit)
  refine ⟨_, ⟨h2.unit, rfl⟩, ?_⟩
  change cT c ((Polynomial.aeval B.1 p).map ι) * (Polynomial.aeval B.1 p).map ι = B.1.map ι
  rw [GlobalTheory.UnitaryDoubleCoset.cT_map ι (c := d) (fun _ => rfl), ← Matrix.map_mul, hp]

theorem exists_congr_antiJ {ϖ : w.adicCompletion E} {q : ℕ} (hU : IsUnramInv ϖ c q)
    {B : GL (Fin n) (w.adicCompletion E)} (hB : B ∈ KGL w n) (hB' : cT c B.1 = B.1) :
    ∃ k ∈ KGL w n, cT c k.1 * B.1 * k.1 = antiJ _ n := by
  have hint : ∀ i j, antiJ (w.adicCompletion E) n i j ∈ Ov E w := fun i j => by
    unfold antiJ; split_ifs
    exacts [one_mem _, zero_mem _]
  obtain ⟨A, hA, eA⟩ := P.cartan_exists_glint (Ov E w) _ _ (GlobalTheory.UnitarySwap.antiJ_mul_self (n := n)) hint hint
  obtain ⟨k, hk, e⟩ := exists_norm hU hB hB'
  obtain ⟨l, hl, e'⟩ := exists_norm hU hA (by
    rw [eA]
    ext i j
    simp [cT, antiJ, add_comm i.val, apply_ite c])
  refine ⟨k⁻¹ * l, mul_mem (inv_mem hk) hl, ?_⟩
  rw [← e, ← Matrix.mul_assoc, ← cT_mul, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel_left, e', eA]

variable {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}

theorem mem_latLoc_iff (hw : IsInertAt F E v w) (h : w.under (𝓞 F) = v) (y : Fin n → Fv F v ⊗[F] E) :
    y ∈ latLoc F L v ↔ toCompl h ∘ y ∈ latAt w L := by
  constructor
  · refine latLoc_induction (p := fun y => toCompl h ∘ y ∈ latAt w L) (fun a ha x hx => ?_) ?_
      (fun y z hy hz => ?_) fun y hy => ?_
    · exact (latAt w L).smul_mem ⟨_, complMap_mem h ha⟩ (Submodule.subset_span ⟨x, hx, rfl⟩)
    · convert zero_mem (latAt w L) using 1
      exact funext fun i => map_zero _
    · convert add_mem hy hz using 1
      exact funext fun i => map_add _ _ _
    · convert neg_mem hy using 1
      exact funext fun i => map_neg _ _
  · let e := complEquiv hw h
    have key : ∀ z ∈ latAt w L, e.symm ∘ z ∈ latLoc F L v := fun z hz => by
      induction hz using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨z, hz, rfl⟩ := hx
        convert tmul_mem_latLoc (one_mem _) hz using 1
        exact funext fun i => e.symm_apply_eq.2 ((toCompl_tmul h 1 _).trans (by rw [map_one, one_mul])).symm
      | zero =>
        convert zero_mem (latLoc F L v) using 1
        exact funext fun i => map_zero _
      | add a b _ _ ha hb =>
        convert add_mem ha hb using 1
        exact funext fun i => map_add _ _ _
      | smul a b _ hb =>
        convert (latLoc F L v).smul_mem ⟨e.symm a, (mem_intLoc_iff hw h _).2
          ((e.apply_symm_apply a).symm ▸ a.2 : e (e.symm a) ∈ Ov E w)⟩ hb using 1
        exact funext fun i => map_mul e.symm _ _
    intro hy
    convert key _ hy using 1
    exact funext fun i => (e.symm_apply_apply _).symm

theorem comp_mulVec (h : w.under (𝓞 F) = v) (g : GL (Fin n) (Fv F v ⊗[F] E)) (y : Fin n → Fv F v ⊗[F] E) :
    toCompl h ∘ (g.1 *ᵥ y) = (bc (toCompl h) g).1 *ᵥ (toCompl h ∘ y) :=
  funext fun i => RingHom.map_mulVec (toCompl h) _ y i

theorem exists_comp (h : w.under (𝓞 F) = v) (z : Fin n → w.adicCompletion E) : ∃ y, toCompl h ∘ y = z :=
  (toCompl_surjective h).comp_left z

theorem exists_isFrameAt (hw : IsInertAt F E v w) (hL : L.FG) (hL' : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ a, IsFrameAt w L a := by
  have : Submodule.IsLattice E L := ⟨hL, hL'⟩
  have h := (under_eq_iff hw w).2 rfl
  obtain ⟨b, h1, h2⟩ := Frames.exists_rational_frame L v
  refine ⟨bc (toCompl h) (bc (inclR (Fv F v)) b), fun z => ?_⟩
  obtain ⟨y, rfl⟩ := exists_comp h z
  rw [← comp_mulVec, ← mem_latLoc_iff hw, ← Frames.frame_of_rational b h1 h2]
  exact forall_congr' fun i => (mem_intLoc_iff hw h _).symm

theorem isFrameAt_mul {a k : GL (Fin n) (w.adicCompletion E)} (ha : IsFrameAt w L a) (hk : k ∈ KGL w n) :
    IsFrameAt w L (a * k) ∧ ∀ g : GL (Fin n) (w.adicCompletion E),
      (∀ z, z ∈ latAt w L ↔ g.1 *ᵥ z ∈ latAt w L) ↔ a⁻¹ * g * a ∈ KGL w n := by
  have e := Final.StabStd (w.adicCompletion E) (Ov E w) (Fin n) Subtype.val_injective
  have hm : ∀ y : Fin n → w.adicCompletion E, y ∈ stdLat (n := Fin n) (Ov E w) ↔ ∀ i, y i ∈ Ov E w := fun y =>
    ⟨fun h i => by obtain ⟨r, hr⟩ := h i trivial; exact hr ▸ r.2, fun h i _ => ⟨⟨_, h i⟩, rfl⟩⟩
  refine ⟨fun y => ?_, fun g => ⟨fun hg => e.le fun y => ?_, fun hg z => ?_⟩⟩
  · rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← ha, ← hm, ← hm]
    exact e.ge hk y
  · rw [hm, hm, ha, ha, hg, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul,
      ← mul_assoc, mul_inv_cancel_left]
  · have := e.ge hg ((a⁻¹).1 *ᵥ z)
    rwa [hm, hm, ha, ha, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul,
      ← Units.val_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec, ← mul_assoc,
      mul_inv_cancel_left, mul_inv_cancel_right] at this

theorem JR_map (h : w.under (𝓞 F) = v) : (JR (Fv F v) J).map (toCompl h) = J.map (algebraMap E _) :=
  Matrix.ext fun _ _ => (toCompl_tmul h 1 _).trans (by rw [map_one, one_mul]; rfl)

theorem hform_mulVec {A : Type} [CommRing A] (τ : A →+* A) (M a : Matrix (Fin n) (Fin n) A) (x y : Fin n → A) :
    hform τ M (a *ᵥ x) (a *ᵥ y) = (τ ∘ x) ⬝ᵥ ((cT τ a * M * a) *ᵥ y) := by
  have e : ∀ x y, hform τ M x y = (τ ∘ x) ⬝ᵥ (M *ᵥ y) := fun x y => by
    simp [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have e' : τ ∘ (a *ᵥ x) = (τ ∘ x) ᵥ* cT τ a := by
    rw [cT, Matrix.vecMul_transpose]
    exact funext fun i => RingHom.map_mulVec τ a x i
  rw [e, e', ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem mem_latAt_iff (hw : IsInertAt F E v w) (hc : IsConjAt σ h c) (hL : IsSelfDualAt σ J L v)
    (z : Fin n → w.adicCompletion E) :
    z ∈ latAt w L ↔ ∀ x ∈ latAt w L, hform c (J.map (algebraMap E _)) x z ∈ Ov E w := by
  have e : ∀ x y, toCompl h (hLin σ J (Fv F v) y x) =
      hform c (J.map (algebraMap E _)) (toCompl h ∘ x) (toCompl h ∘ y) := fun x y => by
    rw [← JR_map h]
    simp only [hLin, hR, hform, map_sum, map_mul, ← hc _, Function.comp_apply, Matrix.map_apply]
  obtain ⟨y, rfl⟩ := exists_comp h z
  rw [← mem_latLoc_iff hw, hL]
  refine ⟨fun hy z hz => ?_, fun hy x hx => ?_⟩
  · obtain ⟨x, rfl⟩ := exists_comp h z
    rw [← e]
    exact toCompl_mem h (hy x ((mem_latLoc_iff hw h x).2 hz))
  · rw [mem_intLoc_iff hw h, e]
    exact hy _ ((mem_latLoc_iff hw h x).1 hx)

theorem exists_gram (hw : IsInertAt F E v w) (hc : IsConjAt σ h c) (hJ : J.det ≠ 0) (hL : IsSelfDualAt σ J L v)
    {a : GL (Fin n) (w.adicCompletion E)} (ha : IsFrameAt w L a) :
    ∃ B ∈ KGL w n, B.1 = cT c a.1 * J.map (algebraMap E _) * a.1 := by
  set B := cT c a.1 * J.map (algebraMap E (w.adicCompletion E)) * a.1 with hB
  have hu : IsUnit B := by
    refine (IsUnit.mul (IsUnit.of_mul_eq_one (cT c (a⁻¹).1) ?_) ?_).mul a.isUnit
    · rw [← cT_mul, Units.inv_mul, cT_one]
    · rw [Matrix.isUnit_iff_isUnit_det, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact ((map_ne_zero _).2 hJ).isUnit
  have hs : ∀ j i : Fin n, (Pi.single j 1 : Fin n → w.adicCompletion E) i ∈ Ov E w := fun j i => by
    by_cases e : i = j
    · subst e; simp
    · simp [e]
  refine P.cartan_exists_glint (Ov E w) B (hu.unit⁻¹).1 hu.mul_val_inv (fun i j => ?_) fun i j => ?_
  · have := (mem_latAt_iff hw hc hL _).1 ((ha _).1 (hs j)) _ ((ha _).1 (hs i))
    rw [hform_mulVec, ← hB, show c ∘ Pi.single i 1 = Pi.single i 1 from funext fun k => by
      by_cases e : k = i
      · subst e; simp
      · simp [e]] at this
    simpa using this
  · have := (ha ((hu.unit⁻¹).1 *ᵥ Pi.single j 1)).2 ((mem_latAt_iff hw hc hL _).2 fun x hx => by
      have e : a.1 *ᵥ ((a⁻¹).1 *ᵥ x) = x := by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      have h1 := (ha _).2 (e.symm ▸ hx) j
      rw [← e, hform_mulVec, ← hB, Matrix.mulVec_mulVec, hu.mul_val_inv, Matrix.one_mulVec, dotProduct_single, mul_one]
      exact conj_mem hw hc h1) i
    simpa using this

theorem exists_frame_antiJ (hσ : IsCMExt F E σ) (hJ : IsHermND σ J) (hL : L.FG)
    (hL' : Submodule.span E (L : Set (Fin n → E)) = ⊤) (hw : IsInertAt F E v w) (hc : IsConjAt σ h c)
    (hs : IsSelfDualAt σ J L v) :
    ∃ a, IsFrameAt w L a ∧ cT c a.1 * J.map (algebraMap E _) * a.1 = antiJ _ n := by
  obtain ⟨ϖ, hU⟩ := exists_isUnramInv hσ hw hc
  obtain ⟨a, ha⟩ := exists_isFrameAt hw hL hL'
  obtain ⟨B, hB, eB⟩ := exists_gram hw hc hJ.2 hs ha
  have h1 : cT c (J.map (algebraMap E (w.adicCompletion E))) = J.map (algebraMap E _) :=
    Matrix.ext fun i j => (conj_algebraMap hc _).trans (congrArg _ (hJ.1 i j))
  obtain ⟨k, hk, e⟩ := exists_congr_antiJ hU hB (by
    rw [eB, cT_mul, cT_mul, h1, GlobalTheory.UnitaryDoubleCoset.cT_cT hU.1, Matrix.mul_assoc])
  refine ⟨a * k, (isFrameAt_mul ha hk).1, ?_⟩
  rw [← e, eB, Units.val_mul, cT_mul]
  simp only [Matrix.mul_assoc]

theorem bc_mem_iff (hw : IsInertAt F E v w) (hc : IsConjAt σ h c) {a : GL (Fin n) (w.adicCompletion E)}
    (ha : cT c a.1 * J.map (algebraMap E _) * a.1 = antiJ _ n) (g : GL (Fin n) (Fv F v ⊗[F] E)) :
    g ∈ HR (Fv F v) σ J ↔ a⁻¹ * bc (toCompl h) g * a ∈ GU c n := by
  have h1 : cT c (bc (toCompl h) g).1 = (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) g.1).map (toCompl h) :=
    Matrix.ext fun i j => hc _
  have h2 : g ∈ HR (Fv F v) σ J ↔ bc (toCompl h) g ∈ UJ c (J.map (algebraMap E _)) := by
    change _ ↔ cT c (bc (toCompl h) g).1 * _ * g.1.map (toCompl h) = _
    rw [h1, ← JR_map h, ← Matrix.map_mul, ← Matrix.map_mul]
    exact (Matrix.map_injective (toCompl_bijective hw h).1).eq_iff.symm
  have h3 : ∀ x : GL (Fin n) (w.adicCompletion E), cT c (a⁻¹ * x * a).1 * antiJ _ n * (a⁻¹ * x * a).1 =
      cT c a.1 * (cT c x.1 * J.map (algebraMap E _) * x.1) * a.1 := fun x => by
    rw [← ha, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← cT_mul, Matrix.mul_assoc, ← Units.val_mul, ← mul_assoc,
      mul_inv_cancel_left, Units.val_mul, cT_mul]
    simp only [Matrix.mul_assoc]
  have h4 : IsUnit (cT c a.1) := IsUnit.of_mul_eq_one (cT c (a⁻¹).1) (by rw [← cT_mul, Units.inv_mul, cT_one])
  rw [h2]
  change _ ↔ _ * _ * _ = _
  rw [h3, ← ha, a.isUnit.mul_left_inj, h4.mul_right_inj]
  rfl

def chart (hw : IsInertAt F E v w) (hc : IsConjAt σ h c) {a : GL (Fin n) (w.adicCompletion E)}
    (ha : cT c a.1 * J.map (algebraMap E _) * a.1 = antiJ _ n) : GLoc σ J v ≃* GU c n :=
  have e1 : ∀ x : GL (Fin n) (w.adicCompletion E), bc (toCompl h) (bc (complEquiv hw h).symm.toRingHom x) = x :=
    fun _ => Units.ext (Matrix.ext fun _ _ => (complEquiv hw h).apply_symm_apply _)
  have e2 : ∀ x : GL (Fin n) (Fv F v ⊗[F] E), bc (complEquiv hw h).symm.toRingHom (bc (toCompl h) x) = x :=
    fun _ => Units.ext (Matrix.ext fun _ _ => (complEquiv hw h).symm_apply_apply _)
  { toFun := fun g => ⟨a⁻¹ * locMat σ J h g * a, (bc_mem_iff hw hc ha _).1 g.2⟩
    invFun := fun u => ⟨bc (complEquiv hw h).symm.toRingHom (a * u * a⁻¹), (bc_mem_iff hw hc ha _).2 (by
      rw [e1, show a⁻¹ * (a * u * a⁻¹) * a = u by group]; exact u.2)⟩
    left_inv := fun g => Subtype.ext ((congrArg (bc (complEquiv hw h).symm.toRingHom)
      (show a * (a⁻¹ * locMat σ J h g * a) * a⁻¹ = locMat σ J h g by group)).trans (e2 g.1))
    right_inv := fun u => Subtype.ext ((congrArg (a⁻¹ * · * a) (e1 _)).trans (by group))
    map_mul' := fun g g' => Subtype.ext (by simp only [map_mul, Subgroup.coe_mul]; group) }

theorem continuous_chart (hw : IsInertAt F E v w) (hc : IsConjAt σ h c) {a : GL (Fin n) (w.adicCompletion E)}
    (ha : cT c a.1 * J.map (algebraMap E _) * a.1 = antiJ _ n) :
    Continuous (chart hw hc ha) ∧ Continuous (chart hw hc ha).symm := by
  have h1 : Continuous (bc (n := Fin n) (toCompl h)) :=
    Continuous.units_map _ (continuous_id.matrix_map (continuous_complEquiv hw h).1)
  have h2 : Continuous (bc (n := Fin n) (complEquiv hw h).symm.toRingHom) :=
    Continuous.units_map _ (continuous_id.matrix_map (continuous_complEquiv hw h).2)
  exact ⟨((continuous_const.mul (h1.comp continuous_subtype_val)).mul continuous_const).subtype_mk _,
    (h2.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const)).subtype_mk _⟩

theorem isInertChart_chart (hw : IsInertAt F E v w) (hc : IsConjAt σ h c) {a : GL (Fin n) (w.adicCompletion E)}
    (ha' : IsFrameAt w L a) (ha : cT c a.1 * J.map (algebraMap E _) * a.1 = antiJ _ n) :
    IsInertChart σ J L h c (chart hw hc ha) := by
  refine ⟨hc, ⟨a, ha', ha, fun _ => rfl⟩, fun g => ?_⟩
  refine Iff.trans ?_ (((isFrameAt_mul ha' (one_mem _)).2 (locMat σ J h g)).trans
    ⟨fun hg => ⟨(chart hw hc ha g).2, hg⟩, fun hg => hg.2⟩)
  rw [mem_stabLoc]
  refine ⟨fun hg z => ?_, fun hg y => ?_⟩
  · obtain ⟨y, rfl⟩ := exists_comp h z
    rw [← mem_latLoc_iff hw, hg, mem_latLoc_iff hw h, comp_mulVec]
    rfl
  · rw [mem_latLoc_iff hw h, hg, mem_latLoc_iff hw h, comp_mulVec]
    rfl

end InertChart

open InertChart in

theorem exists_isInertChart (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (v : HeightOneSpectrum (𝓞 F)) :
    (IsUnram (E := E) v → IsSplit (E := E) v ∨ ∃ w, IsInertAt F E v w) ∧
    ∀ (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), IsInertAt F E v w →
      Function.Bijective (toCompl h) ∧ (∃! c, IsConjAt σ h c) ∧
      (∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v ↔ u = w) ∧
      Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ 2 ∧
      ∀ c, IsConjAt σ h c → (∃ ϖ, IsUnramInv ϖ c (qV F v)) ∧
        ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)), IsHermND σ J → L.FG →
          Submodule.span E (L : Set (Fin n → E)) = ⊤ → IsSelfDualAt σ J L v →
          ∃ e, IsInertChart σ J L h c e ∧ Continuous e ∧ Continuous e.symm :=
  ⟨isSplit_or_isInertAt, fun _ h hw => ⟨toCompl_bijective hw h, existsUnique_isConjAt σ hw h, under_eq_iff hw,
    absNorm_eq hσ.2.2.1 hw, fun _ hc => ⟨exists_isUnramInv hσ hw hc, fun _ _ _ hJ hL hL' hs =>
      let ⟨_, ha', ha⟩ := exists_frame_antiJ hσ hJ hL hL' hw hc hs
      ⟨_, isInertChart_chart hw hc ha' ha, continuous_chart hw hc ha⟩⟩⟩⟩

end GlobalTheory.LFun

end
