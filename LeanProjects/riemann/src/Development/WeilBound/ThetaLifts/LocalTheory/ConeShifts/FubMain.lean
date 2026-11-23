import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.FubLoc

noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.ThKG.Fub
open GlobalTheory.Doubling hiding npow norm_npow npow_ne_zero

attribute [local instance] ae_ring ae_smul ae_t2 ae_lc ae_sc id_lc id_sc id_borel

theorem inAt_iff (𝔞 : FractionalIdeal (𝓞 E)⁰ E) (v : Pl F) (l : (AE F E)ˣ) : InAt 𝔞 v (l : AE F E) ↔
    ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → vw w l ≤ WithZero.exp (-FractionalIdeal.count E w 𝔞) := Iff.rfl

open Classical in
theorem uLocP {B : Base F E} (hB : B.IsGood σ) {ν : Chr F E} {z : ℕ} (hz : 1 ≤ z) (𝔞 : FractionalIdeal (𝓞 E)⁰ E) {v : Pl F}
    (hν : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → UnrAt ν w) (γ : Measure (part (PI (F := F)) ⊤ (io (idem F v))))
    (hγ : γ.IsHaarMeasure ∧ γ {x | x.1 ∈ (UI F E : Set (AE F E)ˣ)} = 1) :
    Integrable (fun x : part PI ⊤ (io (idem F v)) => (if InAt 𝔞 v (x.1 : AE F E) then (1 : ℂ) else 0) * wt ν z x.1) γ ∧
      ∫ x : part PI ⊤ (io (idem F v)), (if InAt 𝔞 v (x.1 : AE F E) then (1 : ℂ) else 0) * wt ν z x.1 ∂γ =
        ∏ w ∈ Formalism.L2.Host.aboveF (L := E) F v, tw ν z (FractionalIdeal.count E w 𝔞) w := by
  have := prodW hB hz (Formalism.L2.Host.aboveF (L := E) F v) (fun w hw => hν w (mem_aboveF.1 hw)) (fun w => FractionalIdeal.count E w 𝔞)
    (c := 0) (by simp) (map_zero _) (by simp) (fun l h _ => by rw [← show PI 0 l = l from h.2, unitInvariant_zero, map_one]) _
    (idem_eq_sum v) γ hγ
  simp only [unitInvariant_zero, one_mem, and_true, mem_aboveF] at this
  simp only [inAt_iff]
  convert this

theorem ab_tendsto (T₀ : Finset (Pl F)) [DecidableEq (Pl F)] :
    Tendsto (fun T : Finset (Pl F) => ab (E := E) (T ∪ T₀)) atTop atTop :=
  tendsto_atTop_finset_of_monotone (fun _ _ h _ hw => mem_ab.2 (Finset.union_subset_union_left h (mem_ab.1 hw)))
    fun w => ⟨{w.under (𝓞 F)}, mem_ab.2 (by simp)⟩

open Classical in
theorem lim_tw {ν : Chr F E} {z : ℕ} (hz : 2 ≤ z) (m : HeightOneSpectrum (𝓞 E) → ℤ) (S T₀ : Finset (Pl F))
    (hν : UnrOff ν (S : Set (Pl F))) (hm : ∀ w, w.under (𝓞 F) ∉ T₀ → m w = 0) :
    Tendsto (fun T : Finset (Pl F) => ∏ w ∈ ab ((T ∪ T₀) \ S), tw ν z (m w) w) atTop
      (𝓝 ((∏ w ∈ ab (T₀ \ S), ((val ν w : ℂ) * npow w (-(z : ℂ))) ^ m w) * charL ν (S : Set (Pl F)) (z : ℂ))) := by
  have h1 := ((bounded_charFam (above E (S : Set (Pl F))) ν).converges (s := (z : ℂ)) (by
    simp only [Complex.natCast_re]; have : (2 : ℝ) ≤ z := by exact_mod_cast hz
    linarith)).hasProd
  have h2 := (hasProd_subtype_iff_mulIndicator (s := {w | w ∉ above E (S : Set (Pl F))})
    (f := fun w => locL (charFam ν) w (z : ℂ))).1 h1
  have h3 := (Tendsto.comp h2 (ab_tendsto T₀)).const_mul (∏ w ∈ ab (T₀ \ S), ((val ν w : ℂ) * npow w (-(z : ℂ))) ^ m w)
  refine h3.congr fun T => ?_
  simp only [tw, Finset.prod_mul_distrib, Function.comp]
  congr 1
  · refine Finset.prod_subset (fun w hw => ?_) fun w hw hw' => ?_
    · rw [mem_ab, Finset.mem_sdiff] at hw ⊢; exact ⟨Finset.mem_union_right _ hw.1, hw.2⟩
    · rw [mem_ab, Finset.mem_sdiff] at hw hw'
      rw [hm w fun h => hw' ⟨h, hw.2⟩, zpow_zero]
  · symm
    refine Finset.prod_subset_one_on_sdiff (fun w hw => ?_) (fun w hw => ?_) fun w hw => ?_
    · rw [mem_ab] at hw ⊢; exact (Finset.mem_sdiff.1 hw).1
    · simp only [Finset.mem_sdiff, mem_ab] at hw
      exact Set.mulIndicator_of_notMem (fun h => hw.2 ⟨hw.1, h⟩) _
    · have h := (Finset.mem_sdiff.1 (mem_ab.1 hw)).2
      rw [Set.mulIndicator_of_mem (show w ∈ {w | w ∉ above E (S : Set (Pl F))} from h), locL, charFam_of_unrAt (hν w h)]
      simp [eulerFac, eulerPoly]

set_option maxHeartbeats 600000 in
open Classical in
theorem tail {B : Base F E} (hB : B.IsGood σ) {z : ℕ} (hz : 2 ≤ z) (𝔞 : FractionalIdeal (𝓞 E)⁰ E) (T T₀ : Finset (Pl F))
    (hT : T ⊆ T₀) (hm : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∉ T₀ → FractionalIdeal.count E w 𝔞 = 0)
    (β : Measure (part (PI (F := F)) ⊤ (io (rest T)))) (hβ : β.IsHaarMeasure ∧ β {x | x.1 ∈ (UI F E : Set (AE F E)ˣ)} = 1)
    {ν : Chr F E} (hc : Continuous ν) (hν : UnrOff ν (T : Set (Pl F))) :
    Integrable (fun x : part PI ⊤ (io (rest T)) => (if ∀ v ∉ T, InAt 𝔞 v (x.1 : AE F E) then (1 : ℂ) else 0) * wt ν z x.1) β ∧
      Tendsto (fun T' : Finset (Pl F) => ∏ w ∈ ab ((T' ∪ T₀) \ T), tw ν z (FractionalIdeal.count E w 𝔞) w) atTop
        (𝓝 (∫ x : part PI ⊤ (io (rest T)), (if ∀ v ∉ T, InAt 𝔞 v (x.1 : AE F E) then (1 : ℂ) else 0) * wt ν z x.1 ∂β)) := by
  haveI := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum F
  have hi := fun T : Finset (Pl F) => io_idem (E := E) (rest_idem T)
  let D : Finset (Pl F) → Set (part (PI (F := F) (E := E)) ⊤ (io (rest T))) := fun T' => {x | PI (io (rest (T' ∪ T₀))) x.1 ∈ UI F E}
  have mD : ∀ T', MeasurableSet (D T') := fun T' =>
    (isOpen_UI.preimage ((unitInvariant_continuous (hi _)).comp continuous_subtype_val)).measurableSet
  have hD : ∀ (A : Finset (Pl F)) (x : (AE F E)ˣ), PI (io (rest A)) x ∈ UI F E ↔
      ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∉ A → vw w x = 1 := fun A x => by
    have e : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∉ A → vw w (PI (io (rest A)) x) = vw w x := fun w hw => by
      rw [vw, cw_PI_one (hi A) (by rw [cw_rest, if_neg hw])]; rfl
    refine ⟨fun h w hw => (e w hw).symm.trans (h w), fun h w => ?_⟩
    by_cases hw : w.under (𝓞 F) ∈ A
    · rw [vw, cw_PI_zero (hi A) (rest_zero.2 hw), map_one]
    · exact (e w hw).trans (h w hw)
  have cov : AECover β atTop D := by
    refine ⟨Eventually.of_forall fun x => ?_, mD⟩
    have f1 : ∀ y : (AE F E)ˣ, ∀ᶠ w in cofinite, vw w y ≤ 1 := fun y => (fc F E y).2
    have f2 : {w | ¬ vw w x.1 = 1}.Finite := ((f1 x.1).and (f1 x.1⁻¹)).mono fun w h => le_antisymm h.1 (by
      calc 1 = vw w x.1 * vw w x.1⁻¹ := (vw_inv w _).symm
        _ ≤ vw w x.1 * 1 := mul_le_mul_right h.2 _
        _ = vw w x.1 := mul_one _)
    filter_upwards [eventually_ge_atTop (f2.toFinset.image fun w => w.under (𝓞 F))] with T' h
    refine (hD _ _).2 fun w hw => by_contra fun h' => hw (Finset.mem_union_left _ (h ?_))
    exact Finset.mem_image_of_mem _ (f2.mem_toFinset.2 h')
  have key : ∀ ν : Chr F E, Continuous ν → UnrOff ν (T : Set (Pl F)) → ∀ T',
      IntegrableOn (fun x : part PI ⊤ (io (rest T)) => (if ∀ v ∉ T, InAt 𝔞 v (x.1 : AE F E) then (1 : ℂ) else 0) * wt ν z x.1) (D T') β ∧
      ∫ x in D T', (if ∀ v ∉ T, InAt 𝔞 v (x.1 : AE F E) then (1 : ℂ) else 0) * wt ν z x.1 ∂β =
        ∏ w ∈ ab ((T' ∪ T₀) \ T), tw ν z (FractionalIdeal.count E w 𝔞) w := fun ν hc hν T' => by
    have hs : T ⊆ T' ∪ T₀ := hT.trans Finset.subset_union_right
    have := prodW hB (z := z) (by omega) (ab ((T' ∪ T₀) \ T)) (fun w hw => hν w (Finset.mem_sdiff.1 (mem_ab.1 hw)).2)
      (fun w => FractionalIdeal.count E w 𝔞) (hi (T' ∪ T₀)) (inf_io (rest_fst _))
      (fun w hw => ew_rest (Finset.mem_sdiff.1 (mem_ab.1 hw)).1)
      (fun l h hu => nu_rest hc (fun w hw => hν w fun h => hw (hs h)) h hu) _ (rest_split hs) β hβ
    rw [← integrable_indicator_iff (mD T'), ← integral_indicator (mD T')]
    have e : (D T').indicator (fun x : part PI ⊤ (io (rest T)) => (if ∀ v ∉ T, InAt 𝔞 v (x.1 : AE F E) then (1 : ℂ) else 0) *
        wt ν z x.1) = fun x : part PI ⊤ (io (rest T)) => (if (∀ w ∈ ab ((T' ∪ T₀) \ T),
          vw w x.1 ≤ WithZero.exp (-FractionalIdeal.count E w 𝔞)) ∧ PI (io (rest (T' ∪ T₀))) x.1 ∈ UI F E then (1 : ℂ) else 0) *
            wt ν z x.1 := by
      funext x
      by_cases hx : PI (io (rest (T' ∪ T₀))) x.1 ∈ UI F E
      · rw [Set.indicator_of_mem (show x ∈ D T' from hx)]
        congr 1
        refine if_congr ⟨fun h => ⟨fun w hw => (inAt_iff _ _ _).1 (h _ (Finset.mem_sdiff.1 (mem_ab.1 hw)).2) w rfl, hx⟩,
          fun h v hv => (inAt_iff _ _ _).2 fun w hw => ?_⟩ rfl rfl
        subst hw
        by_cases h1 : w.under (𝓞 F) ∈ T' ∪ T₀
        · exact h.1 w (mem_ab.2 (Finset.mem_sdiff.2 ⟨h1, hv⟩))
        · rw [(hD _ _).1 hx w h1, hm w fun h2 => h1 (Finset.mem_union_right _ h2)]; simp
      · rw [Set.indicator_of_notMem (show x ∉ D T' from hx), if_neg fun h => hx h.2, zero_mul]
    rw [e]
    convert this
  have u1 : UnrOff (1 : Chr F E) (T : Set (Pl F)) := fun w _ x _ => map_one Circle.toUnits
  obtain ⟨C, hC⟩ := (lim_tw (ν := (1 : Chr F E)) hz (fun w => FractionalIdeal.count E w 𝔞) T T₀ u1 hm).norm.isBoundedUnder_le
  have int : Integrable (fun x : part PI ⊤ (io (rest T)) =>
      (if ∀ v ∉ T, InAt 𝔞 v (x.1 : AE F E) then (1 : ℂ) else 0) * wt ν z x.1) β := by
    refine cov.integrable_of_integral_norm_bounded C (fun T' => (key ν hc hν T').1) (Eventually.mono hC fun T' h => le_trans ?_ h)
    beta_reduce
    rw [← (key 1 continuous_const u1 T').2]
    have e : ∀ x : part (PI (F := F) (E := E)) ⊤ (io (rest T)),
        (if ∀ v ∉ T, InAt 𝔞 v (x.1 : AE F E) then (1 : ℂ) else 0) * wt 1 z x.1 =
        ((‖(if ∀ v ∉ T, InAt 𝔞 v (x.1 : AE F E) then (1 : ℂ) else 0) * wt ν z x.1‖ : ℝ) : ℂ) := fun x => by
      have hn := Circle.norm_coe (ν x.1)
      split_ifs <;> simp [wt, hn]
    simp only [e]
    rw [integral_complex_ofReal, Complex.norm_real]
    exact le_abs_self _
  refine ⟨int, (cov.integral_tendsto_of_countably_generated int).congr fun T' => (key ν hc hν T').2⟩

open Classical in
theorem euler {ν : Chr F E} {z : ℕ} (hz : 2 ≤ z) (𝔞 : FractionalIdeal (𝓞 E)⁰ E)
    (fin : {w | ¬ FractionalIdeal.count E w 𝔞 = 0}.Finite) {S₀ S T : Finset (Pl F)} (hS : S₀ ⊆ S) (hT : S ⊆ T)
    (hν : UnrOff ν (S : Set (Pl F)))
    (hram : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ S → ¬ UnrAt ν w ∧ FractionalIdeal.count E w 𝔞 = 0) (u : Pl F → ℂ)
    (hu2 : ∀ v ∉ S, u v = ∏ w ∈ Formalism.L2.Host.aboveF (L := E) F v, tw ν z (FractionalIdeal.count E w 𝔞) w) (I : ℂ)
    (t2 : Tendsto (fun T' : Finset (Pl F) => ∏ w ∈ ab ((T' ∪ (T ∪ fin.toFinset.image fun w => w.under (𝓞 F))) \ T),
      tw ν z (FractionalIdeal.count E w 𝔞) w) atTop (𝓝 I)) :
    (∏ v ∈ T \ S, u v) * I = (∏ w ∈ fin.toFinset, npow w (-(z : ℂ)) ^ FractionalIdeal.count E w 𝔞) * (idealVal ν 𝔞 : ℂ) *
      charL ν (S₀ : Set (Pl F)) (z : ℂ) := by
  let T₀ := T ∪ fin.toFinset.image fun w => w.under (𝓞 F)
  have hm0 : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∉ T₀ → FractionalIdeal.count E w 𝔞 = 0 := fun w hw =>
    by_contra fun h => hw (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (fin.mem_toFinset.2 h)))
  have t3 := lim_tw hz (fun w => FractionalIdeal.count E w 𝔞) S T₀ hν hm0
  have t5 := tendsto_nhds_unique ((t2.const_mul (∏ v ∈ T \ S, u v)).congr fun T' => ?_) t3
  · rw [t5]
    congr 1
    · have hsub : fin.toFinset ⊆ ab (T₀ \ S) := fun w hw => mem_ab.2 (Finset.mem_sdiff.2
        ⟨Finset.mem_union_right _ (Finset.mem_image_of_mem _ hw), fun h => fin.mem_toFinset.1 hw (hram w h).2⟩)
      rw [← Finset.prod_subset hsub fun w _ hw => by rw [not_not.1 (mt fin.mem_toFinset.2 hw), zpow_zero], idealVal,
        finprod_eq_prod_of_mulSupport_subset _ (s := fin.toFinset) fun w hw => by
          simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
          intro h; exact hw (by simp only [h, zpow_zero])]
      simp only [mul_zpow, Finset.prod_mul_distrib, Units.coe_prod, Units.val_zpow_eq_zpow_val]
      ring
    · simp only [charL, LS, eulerProd]
      refine (tprod_subtype {w | w ∉ above E (S : Set (Pl F))} fun w => locL (charFam ν) w (z : ℂ)).trans
        (Eq.trans (tprod_congr fun w => ?_) (tprod_subtype {w | w ∉ above E (S₀ : Set (Pl F))} fun w => locL (charFam ν) w (z : ℂ)).symm)
      by_cases h : w.under (𝓞 F) ∈ S
      · have : locL (charFam ν) w (z : ℂ) = 1 := by rw [locL, charFam, if_neg (hram w h).1, eulerFac_zero]
        simp only [Set.mulIndicator_apply, this, ite_self]
      · rw [Set.mulIndicator_of_mem (show w ∈ {w | w ∉ above E (S : Set (Pl F))} from h),
          Set.mulIndicator_of_mem (show w ∈ {w | w ∉ above E (S₀ : Set (Pl F))} from fun h' => h (hS h'))]
  · rw [Finset.prod_congr rfl fun v hv => hu2 v (Finset.mem_sdiff.1 hv).2, ← Finset.prod_biUnion (fun a _ b _ hab =>
      Finset.disjoint_left.2 fun w h h' => hab ((mem_aboveF.1 h).symm.trans (mem_aboveF.1 h'))), ← Finset.prod_union
      (Finset.disjoint_left.2 fun w h h' => (Finset.mem_sdiff.1 (mem_ab.1 h')).2 (by
        simp only [Finset.mem_biUnion, mem_aboveF, exists_eq_right', Finset.mem_sdiff] at h; exact h.1))]
    refine Finset.prod_congr (Finset.ext fun w => ?_) fun _ _ => rfl
    simp only [Finset.mem_union, Finset.mem_biUnion, mem_aboveF, exists_eq_right', Finset.mem_sdiff, mem_ab, T₀]
    have := @hT (w.under (𝓞 F))
    tauto

theorem wt_mul (ν : Chr F E) (z : ℕ) (a b : (AE F E)ˣ) : wt ν z (a * b) = wt ν z a * wt ν z b := map_mul (wtH ν z) a b

set_option maxHeartbeats 1000000 in
theorem ideleFub : IdeleFub := by
  classical
  intro F E _ _ _ _ _ σ B n X K m μ hB hm hμ 𝔞 z h𝔞 hz
  have sy := sysI (F := F) (E := E)
  have hi := fun T : Finset (Pl F) => io_idem (E := E) (rest_idem T)
  have hr := io_idem (E := E) (real_idem (F := F))
  have hv := fun v : Pl F => io_idem (E := E) (idem_idem v)
  have di := idAt_eq (E := E) (evI F) real_idem fun _ => at_inf_iff
  have df := fun v => idAt_eq (E := E) (evFin F v) (idem_idem v) fun _ => at_fin_iff
  have e1 : (⊤ : Subgroup (AE F E)ˣ) = part PI ⊤ (io (realAd F 1) + io (rest ∅)) := by
    rw [io, io, ← map_add, real_add_rest, map_one]
    exact Subgroup.ext fun g => ⟨fun h => ⟨h, unitInvariant_one g⟩, fun h => h.1⟩
  have sp := sy.split hr (hi ∅) (io_orth (real_rest ∅))
  let et : (⊤ : Subgroup (AE F E)ˣ) ≃ₜ* (AE F E)ˣ :=
    { Subgroup.topEquiv with
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk _ }
  have hme : MeasurableEmbedding et.symm := et.symm.toHomeomorph.measurableEmbedding
  obtain ⟨μ', m1, -, m3⟩ := transport e1 _ BorelSpace.measurable_eq (μ.map et.symm)
  obtain ⟨α, a1, -, a3⟩ := transport di _ rfl m.xi
  choose γ g1 g2 g3 using fun v => transport (df v) _ rfl (m.xf v)
  have hγ : ∀ v, (γ v).IsHaarMeasure ∧ γ v {x | x.1 ∈ (UI F E : Set (AE F E)ˣ)} = 1 := fun v =>
    ⟨g1 v (hm.xf v).1, by rw [g2, ← units_eq]; exact (hm.xf v).2⟩
  choose β hβ using fun T : Finset (Pl F) => exists_haar _ (sy.closed (hi T)) _ (UI F E).one_mem
    (co_I (hi T) (inf_io (rest_fst T))).1 (co_I (hi T) (inf_io (rest_fst T))).2
  haveI := m1 (ContinuousMulEquiv.isHaarMeasure_map μ et.symm); haveI := a1 hm.xi; haveI := (hβ ∅).1
  obtain ⟨c, c0, c1, -⟩ := sp.fub μ' α (β ∅)
  have fin : {w | ¬ FractionalIdeal.count E w 𝔞 = 0}.Finite := FractionalIdeal.finite_factors 𝔞
  let κa : ℂ := ∏ w ∈ fin.toFinset, npow w (-(z : ℂ)) ^ FractionalIdeal.count E w 𝔞
  refine ⟨fun l => ⟨PI (io (realAd F 1)) l, di ▸ PI_mem hr l⟩, fun v l => ⟨PI (io (idem F v)) l, (df v) ▸ PI_mem (hv v) l⟩, c * κa,
    mul_ne_zero (by exact_mod_cast c0) (Finset.prod_ne_zero_iff.2 fun w _ => zpow_ne_zero _ (npow_ne_zero _ _)),
    fun l => ⟨coe_PI_io real_idem l, fun v => coe_PI_io (idem_idem v) l⟩, fun ν S₀ S hc hS hν hram => ?_⟩
  have hu := fun v (h : v ∉ S) => uLocP hB (ν := ν) (z := z) (by omega) 𝔞 (v := v) (fun w hw => hν w (by
    show ¬ (w.under (𝓞 F) ∈ (S : Set (Pl F))); rw [hw]; exact h)) (γ v) (hγ v)
  have hu2 : ∀ v ∉ S, uLoc v (m.xf v) 𝔞 ν z = ∏ w ∈ Formalism.L2.Host.aboveF (L := E) F v, tw ν z (FractionalIdeal.count E w 𝔞) w :=
    fun v h => (g3 v fun l => (if InAt 𝔞 v (l : AE F E) then 1 else 0) * wt ν z l).2.symm.trans (hu v h).2
  refine ⟨fun v h => ⟨by rw [hu2 v h]; exact Finset.prod_ne_zero_iff.2 fun w _ => tw_ne ν (by omega) _ _,
    (g3 v fun l => (if InAt 𝔞 v (l : AE F E) then 1 else 0) * wt ν z l).1.1 (hu v h).1⟩, fun T hT gi g i1 i2 => ?_⟩
  let T₀ := T ∪ fin.toFinset.image fun w => w.under (𝓞 F)
  have hm0 : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∉ T₀ → FractionalIdeal.count E w 𝔞 = 0 := fun w hw =>
    by_contra fun h => hw (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (fin.mem_toFinset.2 h)))
  obtain ⟨t1, t2⟩ := tail hB hz 𝔞 T T₀ Finset.subset_union_left hm0 (β T) (hβ T) hc fun w hw => hν w fun h => hw (hT h)
  have t4 : (∏ v ∈ T \ S, uLoc v (m.xf v) 𝔞 ν z) * ∫ x : part PI ⊤ (io (rest T)),
      (if ∀ v ∉ T, InAt 𝔞 v (x.1 : AE F E) then (1 : ℂ) else 0) * wt ν z x.1 ∂(β T) =
      κa * (idealVal ν 𝔞 : ℂ) * charL ν (S₀ : Set (Pl F)) (z : ℂ) :=
    euler hz 𝔞 fin hS hT hν hram _ hu2 _ t2
  have hsum : (io (rest ∅) : AE F E) = ∑ v ∈ T, io (idem F v) + io (rest T) := by
    rw [sum_rest T, io, map_add, map_sum]; rfl
  obtain ⟨p1, p2⟩ := sy.prod (fun v => io (idem F v)) hv (fun _ _ h => io_orth (idem_orth h)) _ (hi T) γ hγ (β T) (hβ T) T
    (fun v h => io_orth (idem_rest h))
    (fun T' h => co_I (sy.good_sum _ hv (fun _ _ h => io_orth (idem_orth h)) _ (hi T) T' fun v h' => io_orth (idem_rest (h h')))
      (by rw [map_add, inf_io (rest_fst T), add_zero, map_sum, Finset.sum_eq_zero fun v _ => inf_io rfl]))
    _ hsum (β ∅) (hβ ∅) (fun v l => ext0 _ (g v) l * wt ν z l)
    (fun l => (if ∀ v ∉ T, InAt 𝔞 v (l : AE F E) then (1 : ℂ) else 0) * wt ν z l)
    (fun v h => (g3 v fun l => ext0 _ (g v) l * wt ν z l).1.2 (by simp only [extendByZeroOnSubset_apply_coe]; exact i2 v h)) t1
  obtain ⟨q1, q2⟩ := c1 (fun l => ext0 _ gi l * wt ν z l) (fun y => (∏ v ∈ T, ext0 _ (g v) (PI (io (idem F v)) y) *
      wt ν z (PI (io (idem F v)) y)) * ((if ∀ v ∉ T, InAt 𝔞 v (PI (io (rest T)) y : AE F E) then (1 : ℂ) else 0) *
        wt ν z (PI (io (rest T)) y)))
    ((a3 fun l => ext0 _ gi l * wt ν z l).1.2 (by simp only [extendByZeroOnSubset_apply_coe]; exact i1)) p1
  rw [p2, (a3 fun l => ext0 _ gi l * wt ν z l).2] at q2
  simp only [fun v => (g3 v fun l => ext0 _ (g v) l * wt ν z l).2, extendByZeroOnSubset_apply_coe] at q2
  have r1 : ∀ v, (io (idem F v) * io (rest ∅) : AE F E) = io (idem F v) := fun v => by
    rw [io_mul, rest, Finset.sum_empty, sub_zero, mul_sub, idem_real, mul_one, sub_zero]
  have r2 : (io (rest T) * io (rest ∅) : AE F E) = io (rest T) := by
    rw [io_mul, rest.eq_1 ∅, Finset.sum_empty, sub_zero, mul_sub, mul_one, mul_comm, real_rest, sub_zero]
  have m4 := m3 fun x => (ext0 _ gi (PI (io (realAd F 1)) x) * wt ν z (PI (io (realAd F 1)) x)) *
    ((∏ v ∈ T, ext0 _ (g v) (PI (io (idem F v)) (PI (io (rest ∅)) x)) * wt ν z (PI (io (idem F v)) (PI (io (rest ∅)) x))) *
      ((if ∀ v ∉ T, InAt 𝔞 v (PI (io (rest T)) (PI (io (rest ∅)) x) : AE F E) then (1 : ℂ) else 0) *
        wt ν z (PI (io (rest T)) (PI (io (rest ∅)) x))))
  rw [m4.1, hme.integrable_map_iff] at q1
  rw [m4.2, hme.integral_map] at q2
  have ef : ∀ x : (AE F E)ˣ, (ext0 _ gi (PI (io (realAd F 1)) x) * wt ν z (PI (io (realAd F 1)) x)) *
      ((∏ v ∈ T, ext0 _ (g v) (PI (io (idem F v)) (PI (io (rest ∅)) x)) * wt ν z (PI (io (idem F v)) (PI (io (rest ∅)) x))) *
        ((if ∀ v ∉ T, InAt 𝔞 v (PI (io (rest T)) (PI (io (rest ∅)) x) : AE F E) then (1 : ℂ) else 0) *
          wt ν z (PI (io (rest T)) (PI (io (rest ∅)) x)))) =
      gi ⟨PI (io (realAd F 1)) x, di ▸ PI_mem hr x⟩ * (∏ v ∈ T, g v ⟨PI (io (idem F v)) x, (df v) ▸ PI_mem (hv v) x⟩) *
        (if ∀ v ∉ T, InAt 𝔞 v (x : AE F E) then 1 else 0) * wt ν z x := fun x => by
    have hx : wt ν z x = wt ν z (PI (io (realAd F 1)) x) * ((∏ v ∈ T, wt ν z (PI (io (idem F v)) x)) * wt ν z (PI (io (rest T)) x)) := by
      have h1 := sp.mul x (e1 ▸ Subgroup.mem_top x)
      rw [hsum, PI_sum _ hv (fun _ _ h => io_orth (idem_orth h)) _ (hi T) T fun v h => io_orth (idem_rest h)] at h1
      have := congrArg (wtH ν z) h1
      rw [map_mul, map_mul, map_prod] at this
      exact this.symm
    have hin : (∀ v ∉ T, InAt 𝔞 v (PI (io (rest T)) x : AE F E)) ↔ ∀ v ∉ T, InAt 𝔞 v (x : AE F E) :=
      forall₂_congr fun v h => by
        simp only [inAt_iff]
        refine forall₂_congr fun w hw => ?_
        rw [vw, cw_PI_one (hi T) (by rw [cw_rest, hw, if_neg h])]; rfl
    simp only [fun v => unitInvariant_comp (hv v) (hi ∅) x, unitInvariant_comp (hi T) (hi ∅) x, r1, r2, hin, ← extendByZeroOnSubset_apply_coe gi,
      ← fun v => extendByZeroOnSubset_apply_coe (g v), Finset.prod_mul_distrib]
    rw [hx]; ring
  have q3 := q1.congr (Eventually.of_forall ef)
  refine ⟨q3, ?_⟩
  rw [← integral_congr_ae (Eventually.of_forall ef)]
  refine (congrArg _ q2).trans ?_
  linear_combination (c * (@integral _ _ _ _ (borel _) m.xi fun l => gi l * wt ν z l.1) *
    ∏ v ∈ T, @integral _ _ _ _ (borel _) (m.xf v) fun l => g v l * wt ν z l.1) * t4

end PositivityTheory.ThKG.Loc.Cone

end
