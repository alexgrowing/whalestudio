import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DegOneIffSurjective
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharConstOnTranslatesTrivialStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsResidueClassNearRealEmbeddingsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResidueDegreeOneOfLinearMemStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIdeleCharLocalFactorizationStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadraticExistsIntegralGeneratorCommonDenominatoStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfinitePlaceEqOfEmbeddingCompAlgebraMapEqStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImEmbeddingNeZeroOfNotMemRangeOfTotallyRealQuadrStatement

noncomputable section
open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit NumberField.mixedEmbedding
namespace GlobalTheory.HeckeInfTriv

section Inf
variable (E : Type) [Field E] [NumberField E]

theorem continuous_mixedSymm : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace E).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace E).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace E).apply_symm_apply y)) ⟨v, hv⟩).symm

theorem continuous_infIdele : Continuous (infIdele E) :=
  Continuous.units_map _ (continuous_id.prodMk continuous_const)

variable [IsTotallyComplex E]

def cplxUnit : ({w : InfinitePlace E // w.IsComplex} → ℂˣ) →* (mixedSpace E)ˣ where
  toFun z := ⟨((fun _ => 1), fun w => (z w : ℂ)), ((fun _ => 1), fun w => ((z w)⁻¹ : ℂˣ)),
    Prod.ext (funext fun _ => mul_one _) (funext fun w => (z w).mul_inv),
    Prod.ext (funext fun _ => mul_one _) (funext fun w => (z w).inv_mul)⟩
  map_one' := Units.ext (Prod.ext rfl (funext fun _ => rfl))
  map_mul' z z' := Units.ext (Prod.ext (funext fun _ => (mul_one _).symm) (funext fun _ => rfl))

def infUnit : ({w : InfinitePlace E // w.IsComplex} → ℂˣ) →* (InfiniteAdeleRing E)ˣ :=
  (Units.map (InfiniteAdeleRing.ringEquiv_mixedSpace E).symm.toRingHom.toMonoidHom).comp (cplxUnit E)

theorem continuous_infUnit : Continuous (infUnit E) := by
  refine (Continuous.units_map ((InfiniteAdeleRing.ringEquiv_mixedSpace E).symm.toRingHom.toMonoidHom) (continuous_mixedSymm E)).comp (f := cplxUnit E) ?_
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact continuous_const.prodMk (continuous_pi fun w => Units.continuous_val.comp (continuous_apply w))
  · exact continuous_const.prodMk (continuous_pi fun w => Units.continuous_coe_inv.comp (continuous_apply w))

theorem real_eq (f g : {w : InfinitePlace E // w.IsReal} → ℝ) : f = g :=
  funext fun w => absurd w.2 (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w.1))

theorem infUnit_emb (k : Eˣ) :
    infUnit E (fun w => Units.map w.1.embedding.toMonoidHom k) = infPart E (diagUnits E k) := by
  apply Units.ext
  change (InfiniteAdeleRing.ringEquiv_mixedSpace E).symm ((fun _ => 1), fun w => w.1.embedding (k : E)) =
    algebraMap E (InfiniteAdeleRing E) (k : E)
  rw [RingEquiv.symm_apply_eq, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  exact Prod.ext (real_eq E _ _) (funext fun w => (mixedEmbedding_apply_isComplex E (k : E) w).symm)

theorem infUnit_surj (u : (InfiniteAdeleRing E)ˣ) : ∃ z, infUnit E z = u := by
  refine ⟨fun w => Units.map (((Pi.evalRingHom _ w).comp (RingHom.snd _ _)).comp
    (InfiniteAdeleRing.ringEquiv_mixedSpace E).toRingHom).toMonoidHom u, ?_⟩
  apply Units.ext
  change (InfiniteAdeleRing.ringEquiv_mixedSpace E).symm ((fun _ => 1),
    fun w => (InfiniteAdeleRing.ringEquiv_mixedSpace E (u : InfiniteAdeleRing E)).2 w) = u
  rw [RingEquiv.symm_apply_eq]
  exact Prod.ext (real_eq E _ _) rfl

end Inf

section Loc
variable {E : Type} [Field E] [NumberField E]

theorem finPart_diag_val (v : HeightOneSpectrum (𝓞 E)) (k : Eˣ) :
    ((finPart E v (diagUnits E k) : (v.adicCompletion E)ˣ) : v.adicCompletion E) =
      algebraMap E (v.adicCompletion E) (k : E) := rfl

theorem val_coe (v : HeightOneSpectrum (𝓞 E)) (y : 𝓞 E) :
    Valued.v (algebraMap E (v.adicCompletion E) (y : E)) = v.intValuation y :=
  (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (y : E)).trans (v.valuation_of_algebraMap y)

theorem loc_unit (χ : Ideles E →* ℂˣ) (v : HeightOneSpectrum (𝓞 E)) (k : Eˣ) (y : 𝓞 E) (hk : (k : E) = y)
    (hy : y ∉ v.asIdeal) (hu : UnrAt χ v) : χ (localIdele E v (finPart E v (diagUnits E k))) = 1 := by
  apply hu
  rw [finPart_diag_val, hk, val_coe]
  exact v.intValuation_eq_one_iff.2 hy

theorem coe_algebraMap (F : Type) [Field F] [NumberField F] [Algebra F E] (a : 𝓞 F) :
    ((algebraMap (𝓞 F) (𝓞 E) a : 𝓞 E) : E) = algebraMap F E (a : F) := rfl

end Loc

theorem inf_trivial_of_trivAt_degOne : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] [Algebra.IsQuadraticExtension F E] (χ : Ideles E →* ℂˣ), IsHeckeChar E χ → (∀ᶠ w in Filter.cofinite, DegOne F w → TrivAt χ w) → ∀ x : (InfiniteAdeleRing E)ˣ, χ (infIdele E x) = 1 := by
  intro F E _ _ _ _ _ _ _ _ χ hχ hdeg
  classical
  obtain ⟨hunr, hcond, hfact⟩ := GlobalTheory.T.continuous_ideleChar_local_factorization E χ hχ.1
  obtain ⟨θ, hθF, D, hD0, hDspan⟩ := GlobalTheory.T.exists_integral_generator_common_denom_of_isQuadratic F E
  have hθ0 : (θ : E) ≠ 0 := fun h => hθF ⟨0, by rw [h, map_zero]⟩
  have hθ0' : θ ≠ 0 := fun h => hθ0 (by rw [h]; rfl)
  have hD0' : algebraMap (𝓞 F) (𝓞 E) D ≠ 0 := by
    intro h
    apply hD0
    have h1 : algebraMap F E (D : F) = 0 := by rw [← coe_algebraMap, h]; rfl
    exact_mod_cast (map_eq_zero_iff _ (algebraMap F E).injective).1 h1
  set e0 : 𝓞 E := algebraMap (𝓞 F) (𝓞 E) D * θ with he0
  have he0ne : e0 ≠ 0 := mul_ne_zero hD0' hθ0'
  have hfin : Set.Finite ({v | ¬ UnrAt χ v} ∪ {v | ¬ (DegOne F v → TrivAt χ v)} ∪
      {v : HeightOneSpectrum (𝓞 E) | e0 ∈ v.asIdeal}) := by
    refine ((Filter.eventually_cofinite.1 hunr).union (Filter.eventually_cofinite.1 hdeg)).union ?_
    refine (Ideal.finite_factors (I := Ideal.span {e0}) ?_).subset fun v hv => ?_
    · rwa [ne_eq, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]
    · exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hv)
  set S := hfin.toFinset with hS
  have hnotS : ∀ v, v ∉ S → UnrAt χ v ∧ (DegOne F v → TrivAt χ v) ∧ e0 ∉ v.asIdeal := by
    intro v hv
    simp only [hS, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hv
    exact ⟨hv.1.1, hv.1.2, hv.2⟩
  choose n hn using hcond
  have hπ : ∀ v : HeightOneSpectrum (𝓞 E), ∃ π : 𝓞 E, π ∈ v.asIdeal ∧ π ≠ 0 := fun v =>
    Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  choose π hπv hπ0 using hπ
  set P : 𝓞 E := ∏ v ∈ S, π v ^ n v with hP
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (hπ0 v)
  set m : Ideal (𝓞 F) := (Ideal.span {θ * P}).comap (algebraMap (𝓞 F) (𝓞 E)) with hm
  have hm0 : m ≠ ⊥ := Ideal.comap_ne_bot_of_integral_mem (mul_ne_zero hθ0' hP0)
    (Ideal.mem_span_singleton_self _) (Algebra.IsIntegral.isIntegral _)
  obtain ⟨C, hC⟩ := GlobalTheory.T.exists_residueClass_near_real_embeddings F m 0 hm0
  set t : Eˣ := Units.mk0 (θ : E) hθ0 with ht
  have hxb : ∀ b : 𝓞 F, ((algebraMap (𝓞 F) (𝓞 E) b + θ : 𝓞 E) : E) ≠ 0 := by
    intro b h
    apply hθF
    refine ⟨-(b : F), ?_⟩
    have h1 : ((algebraMap (𝓞 F) (𝓞 E) b : 𝓞 E) : E) + (θ : E) = 0 := by exact_mod_cast h
    rw [coe_algebraMap] at h1
    rw [map_neg]
    linear_combination -h1
  set xb : 𝓞 F → Eˣ := fun b => Units.mk0 _ (hxb b) with hxbdef
  have key : ∀ b ∈ m, χ (infIdele E (infPart E (diagUnits E (xb b)))) =
      χ (infIdele E (infPart E (diagUnits E t))) := by
    intro b hb
    have hloc : ∀ v, χ (localIdele E v (finPart E v (diagUnits E (xb b * t⁻¹)))) = 1 := by
      intro v
      by_cases hvS : v ∈ S
      · apply hn v
        obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hb)
        have h2 : algebraMap (𝓞 F) (𝓞 E) b + θ = (r * P + 1) * θ := by rw [← hr]; ring
        have h3 : ((algebraMap (𝓞 F) (𝓞 E) b + θ : 𝓞 E) : E) = ((r * P : 𝓞 E) : E) * (θ : E) + (θ : E) := by
          rw [h2]; push_cast; ring
        have hq1 : ((xb b * t⁻¹ : Eˣ) : E) - 1 = ((r * P : 𝓞 E) : E) := by
          simp only [hxbdef, ht, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
          rw [h3]
          field_simp
          ring
        rw [finPart_diag_val, ← map_one (algebraMap E (v.adicCompletion E)), ← map_sub, hq1, val_coe,
          v.intValuation_le_pow_iff_mem]
        obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun w => π w ^ n w) hvS
        exact Ideal.mul_mem_left _ _ (by rw [hP, hc]; exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (hπv v) _))
      · obtain ⟨hu, hd, he0v⟩ := hnotS v hvS
        simp only [map_mul, map_inv]
        have htv : χ (localIdele E v (finPart E v (diagUnits E t))) = 1 :=
          loc_unit χ v t θ rfl (fun h => he0v (Ideal.mul_mem_left _ _ h)) hu
        rw [htv, inv_one, mul_one]
        by_cases hmem : algebraMap (𝓞 F) (𝓞 E) b + θ ∈ v.asIdeal
        · haveI := v.isPrime
          haveI := v.isMaximal
          have hdeg1 : DegOne F v := GlobalTheory.T.residue_degree_one_of_linear_mem' (𝓞 F) (𝓞 E) v.asIdeal θ D b 1
            (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal v.asIdeal) hDspan
            (fun h => he0v (Ideal.mul_mem_right _ _ h))
            (by rw [map_one]; exact fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h))
            (by rwa [map_one, one_mul])
          exact hd hdeg1 _
        · exact loc_unit χ v (xb b) _ rfl hmem hu
    have hdq := hfact (diagUnits E (xb b * t⁻¹)) S (fun v _ => hloc v)
    rw [hχ.2, Finset.prod_eq_one (fun v _ => hloc v), mul_one] at hdq
    simp only [map_mul, map_inv] at hdq
    exact mul_inv_eq_one.1 hdq.symm

  have hreal : ∀ i : {w : InfinitePlace E // w.IsComplex},
      ComplexEmbedding.IsReal (i.1.embedding.comp (algebraMap F E)) := fun i =>
    InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _)
  set τ : {w : InfinitePlace E // w.IsComplex} → (F →+* ℝ) := fun i => (hreal i).embedding with hτ
  have hτapp : ∀ i (a : F), ((τ i a : ℝ) : ℂ) = i.1.embedding (algebraMap F E a) := fun i a =>
    (hreal i).coe_embedding_apply a
  have hτinj : ∀ {j i : {w : InfinitePlace E // w.IsComplex}}, τ j = τ i → j = i := by
    intro j i h
    apply Subtype.ext
    apply GlobalTheory.T.infinitePlace_eq_of_embedding_comp_algebraMap_eq' F E
    ext a
    simp only [RingHom.comp_apply]
    rw [← hτapp, ← hτapp, h]
  set ψ : ({w : InfinitePlace E // w.IsComplex} → ℂˣ) →* ℂˣ := (χ.comp (infIdele E)).comp (infUnit E) with hψ
  have hψc : Continuous ψ := hχ.1.comp ((continuous_infIdele E).comp (continuous_infUnit E))
  set T : Set ({w : InfinitePlace E // w.IsComplex} → ℝ) := {y | ∃ b ∈ m, y = fun i => τ i (b : F)} with hT
  have hψ1 := GlobalTheory.T.eq_one_of_continuous_char_const_on_translates {w : InfinitePlace E // w.IsComplex} ψ (fun i => i.1.embedding (θ : E)) T (max C 0)
    (χ (infIdele E (infPart E (diagUnits E t)))) hψc (fun i => GlobalTheory.T.im_embedding_ne_zero_of_not_mem_range_algebraMap F E i.1 θ hθF) ?_ ?_
  · intro x
    obtain ⟨z, rfl⟩ := infUnit_surj E x
    have := DFunLike.congr_fun hψ1 z
    simpa [hψ] using this
  · intro y
    let y' : (F →+* ℝ) → ℝ := fun τ' => if h : ∃ i, τ i = τ' then y h.choose else 0
    obtain ⟨b, hb, hbC⟩ := hC y'
    refine ⟨fun i => τ i (b : F), ⟨b, by simpa using hb, rfl⟩, ?_⟩
    refine (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun i => ?_
    have hy' : y' (τ i) = y i := by
      have h : ∃ j, τ j = τ i := ⟨i, rfl⟩
      simp only [y', dif_pos h]
      rw [hτinj h.choose_spec]
    rw [Pi.sub_apply, Real.norm_eq_abs, ← hy']
    exact (hbC (τ i)).trans (le_max_left _ _)
  · rintro _ ⟨b, hb, rfl⟩ z hz
    have hzb : z = fun w => Units.map w.1.embedding.toMonoidHom (xb b) := funext fun i => Units.ext (by
      rw [hz i, Units.coe_map, hτapp]
      simp only [hxbdef, Units.val_mk0, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
      rw [← map_add, ← coe_algebraMap]
      rfl)
    rw [hzb]
    show χ (infIdele E (infUnit E _)) = _
    rw [infUnit_emb]
    exact key b hb

end GlobalTheory.HeckeInfTriv
