import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.ContinuousFc

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

theorem mem_part_iff {a : AE F E} (ha : a * a = a) (h0 : infTens F E a = 0) (l : (AE F E)ˣ) :
    l ∈ part PI ⊤ a ↔ infTens F E l = 1 ∧ ∀ w, cw w a = 0 → cw w (l : AE F E) = 1 := by
  refine ⟨fun h => ⟨inf_of_part ha h0 h, fun w hw => by rw [← show PI a l = l from h.2]; exact cw_PI_zero ha hw l⟩,
    fun h => ⟨trivial, Units.ext (ae_ext (show infTens F E (PI a l : AE F E) = infTens F E l by rw [hom_PI _ ha, h0, h.1]; simp) fun w => ?_)⟩⟩
  rcases cw_cases ha w with e | e
  · exact (cw_PI_zero ha e l).trans (h.2 w e).symm
  · exact cw_PI_one ha e l

theorem PI_mem {a : AE F E} (ha : a * a = a) (l : (AE F E)ˣ) : PI a l ∈ part PI ⊤ a :=
  ⟨trivial, by show PI a (PI a l) = PI a l; rw [unitInvariant_comp ha ha, ha]⟩

theorem PI_sum {ι : Type} [DecidableEq ι] (e : ι → AE F E) (he : ∀ i, e i * e i = e i) (ho : ∀ i j, i ≠ j → e i * e j = 0)
    (c : AE F E) (hc : c * c = c) (T : Finset ι) (hT : ∀ i ∈ T, e i * c = 0) (x : (AE F E)ˣ) :
    PI (∑ i ∈ T, e i + c) x = (∏ i ∈ T, PI (e i) x) * PI c x := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert i T hi ih =>
    have hT' : ∀ j ∈ T, e j * c = 0 := fun j hj => hT j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, Finset.prod_insert hi, add_assoc, mul_assoc, ← ih hT']
    refine unitInvariant_add (he i) (sysI.good_sum e he ho c hc T hT') ?_ x
    rw [mul_add, Finset.mul_sum, Finset.sum_eq_zero fun j hj => ho i j (fun e => hi (e ▸ hj)), hT i (Finset.mem_insert_self _ _),
      add_zero]

def wtH (ν : Chr F E) (z : ℕ) : (AE F E)ˣ →* ℂ where
  toFun := wt ν z
  map_one' := by simp [wt]
  map_mul' a b := by simp only [wt, map_mul, Circle.coe_mul, NNReal.coe_mul, Complex.ofReal_mul]; ring

theorem abs_UI {a : AE F E} (ha : a * a = a) (h0 : infTens F E a = 0) {l} (h : l ∈ part PI ⊤ a) (hu : l ∈ UI F E) : absE F E l = 1 :=
  one_of_compact (absE F E) continuous_absE (cpt_I ha h0) fun n => ⟨Subgroup.zpow_mem _ h n, Subgroup.zpow_mem _ hu n⟩

theorem cw_loc (u w : HeightOneSpectrum (𝓞 E)) (y : (w.adicCompletion E)ˣ) :
    cw u (locIdele F w y : AE F E) = Neutral.B1.finiteSingle E w y u := by
  rw [cw_def, finTens_locIdele]; rfl

theorem ew_zero {u w : HeightOneSpectrum (𝓞 E)} : cw u (ew F w) = 0 ↔ u ≠ w := by
  rw [cw_ew]; split_ifs with h <;> simp [h]

theorem loc_mem (w : HeightOneSpectrum (𝓞 E)) (y : (w.adicCompletion E)ˣ) : locIdele F w y ∈ part PI ⊤ (ew F w) :=
  (mem_part_iff (ew_idem w) (inf_ew w) _).2 ⟨infTens_locIdele w y, fun u hu => by rw [cw_loc, finSingle_ne (ew_zero.1 hu)]⟩

theorem nu_ew {ν : Chr F E} {w} (hν : UnrAt ν w) {l} (h : l ∈ part PI ⊤ (ew F w)) (hu : l ∈ UI F E) : ν l = 1 := by
  obtain ⟨h1, h2⟩ := (mem_part_iff (ew_idem w) (inf_ew w) _).1 h
  have e : l = locIdele F w (Units.map (cw w).toMonoidHom l) := Units.ext (ae_ext (h1.trans (infTens_locIdele _ _).symm) fun u => by
    rw [cw_loc]
    by_cases hu : u = w
    · subst hu; rw [finSingle_self]; rfl
    · rw [finSingle_ne hu, h2 u (ew_zero.2 hu)])
  have := hν (Units.map (cw w).toMonoidHom l) (hu w)
  rw [e]
  exact Circle.coe_eq_one.1 (congrArg Units.val this)

variable (F) in

def pw (w : HeightOneSpectrum (𝓞 E)) : (AE F E)ˣ := locIdele F w (Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w))

theorem vw_pw (w : HeightOneSpectrum (𝓞 E)) : vw w (pw F w) = WithZero.exp (-1 : ℤ) := by
  rw [vw, pw, cw_loc, finSingle_self]; exact Formalism.L2.Host.unif_spec w

theorem abs_pw {B : Base F E} (hB : B.IsGood σ) (w : HeightOneSpectrum (𝓞 E)) :
    (absE F E (pw F w) : ℝ) = ((Ideal.absNorm w.asIdeal : ℕ) : ℝ)⁻¹ := by
  have hne : ∀ u, u ≠ w → cw u (pw F w : AE F E) = 1 := fun u hu => by rw [pw, cw_loc, finSingle_ne hu]
  have e : pw F w = ideleAt F E (w.under (𝓞 F)) (unitFin F E (w.under (𝓞 F)) (pw F w)) := by
    refine Units.ext (ae_ext ((infTens_locIdele _ _).trans (map_extUnit_zero (fstA F) _ _ (fun a => rfl) _).symm) fun u => ?_)
    by_cases hu : u.under (𝓞 F) = w.under (𝓞 F)
    · rw [cw_eq hu, cw_eq hu]
      exact congrArg _ (congrArg Units.val (unitFin_ideleAt_self _ (unitFin F E (w.under (𝓞 F)) (pw F w)))).symm
    · rw [hne u fun e => hu (e ▸ rfl), cw_eq rfl]
      rw [show compFin F E _ _ = 1 from congrArg Units.val (unitFin_ideleAt_ne hu _), map_one]
  have o1 : Formalism.UG.ordL (toCompl (rfl : w.under (𝓞 F) = _) (unitFin F E (w.under (𝓞 F)) (pw F w)).1) = 1 := by
    have h : Valued.v (toCompl (rfl : w.under (𝓞 F) = _) (unitFin F E (w.under (𝓞 F)) (pw F w)).1) = WithZero.exp (-1 : ℤ) := by
      rw [← vw_pw (F := F) w, vw, cw_eq rfl]; rfl
    rw [GlobalTheory.AbsInert.ordL_eq_neg_log (h ▸ WithZero.exp_ne_zero), h]; simp
  have hUn := hB.unram
  have hU : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) (w.under (𝓞 F)) :=
    GlobalTheory.LFun.isUnram_iff.2 fun w _ => Ideal.ramificationIdx_eq_one w.asIdeal (𝓞 F)
  rw [e, absE_ideleAt]
  rcases GlobalTheory.LFun.InertChart.isSplit_or_isInertAt hU with hs | ⟨u, hi⟩
  · obtain ⟨w₁, w₂, hn, h1, h2⟩ := GlobalTheory.LFun.isSplit_iff.1 hs
    obtain ⟨w', hw', h'⟩ : ∃ w', w ≠ w' ∧ w'.under (𝓞 F) = w.under (𝓞 F) := by
      by_cases h : w = w₁
      exacts [⟨w₂, h ▸ hn, h2⟩, ⟨w₁, h, h1⟩]
    have o2 : Formalism.UG.ordL (toCompl h' (unitFin F E (w.under (𝓞 F)) (pw F w)).1) = 0 := by
      have h : toCompl h' (unitFin F E (w.under (𝓞 F)) (pw F w)).1 = 1 := (cw_eq h' _).symm.trans (hne w' hw'.symm)
      rw [h, GlobalTheory.AbsInert.ordL_eq_neg_log (by simp)]; simp
    rw [GlobalTheory.Doubling.AbsSplit.absEv_split F E σ hB.cm _ w rfl w' h' hw', o1, o2]
    simp [Formalism.UG.qV]
  · obtain rfl := (GlobalTheory.LFun.InertChart.under_eq_iff hi w).1 rfl
    rw [GlobalTheory.AbsInert.absEv_inert F E σ hB.cm _ w rfl hi, o1, GlobalTheory.LFun.InertChart.absNorm_eq hB.cm.2.2.1 hi]
    simp [Formalism.UG.qV]

theorem wt_pw {B : Base F E} (hB : B.IsGood σ) (ν : Chr F E) (z : ℕ) (w : HeightOneSpectrum (𝓞 E)) :
    wt ν z (pw F w) = (val ν w : ℂ) * npow w (-(z : ℂ)) := by
  rw [wt, abs_pw hB, npow, Complex.cpow_neg, Complex.cpow_natCast]
  push_cast
  rw [inv_pow]; rfl

def tw (ν : Chr F E) (z : ℕ) (m : ℤ) (w : HeightOneSpectrum (𝓞 E)) : ℂ :=
  ((val ν w : ℂ) * npow w (-(z : ℂ))) ^ m * (1 - (val ν w : ℂ) * npow w (-(z : ℂ)))⁻¹

theorem norm_t_lt (ν : Chr F E) {z : ℕ} (hz : 1 ≤ z) (w : HeightOneSpectrum (𝓞 E)) : ‖(val ν w : ℂ) * npow w (-(z : ℂ))‖ < 1 := by
  rw [norm_mul, norm_val, one_mul, norm_npow]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast one_lt_absNorm w) (by simp; omega)

theorem tw_ne (ν : Chr F E) {z : ℕ} (hz : 1 ≤ z) (m : ℤ) (w : HeightOneSpectrum (𝓞 E)) : tw ν z m w ≠ 0 :=
  mul_ne_zero (zpow_ne_zero _ (mul_ne_zero (Units.ne_zero _) (npow_ne_zero _ _))) (inv_ne_zero fun h => by
    have := norm_t_lt ν hz w
    rw [← sub_eq_zero.1 h] at this; simp at this)

open Classical in
theorem locW {B : Base F E} (hB : B.IsGood σ) {ν : Chr F E} {z : ℕ} (hz : 1 ≤ z) {w} (hν : UnrAt ν w) (m : ℤ)
    (γ : Measure (part (PI (F := F)) ⊤ (ew F w))) (hγ : γ.IsHaarMeasure ∧ γ {x | x.1 ∈ (UI F E : Set (AE F E)ˣ)} = 1) :
    Integrable (fun x : part PI ⊤ (ew F w) => (if vw w x.1 ≤ WithZero.exp (-m) then (1 : ℂ) else 0) * wt ν z x.1) γ ∧
      ∫ x : part PI ⊤ (ew F w), (if vw w x.1 ≤ WithZero.exp (-m) then (1 : ℂ) else 0) * wt ν z x.1 ∂γ = tw ν z m w := by
  haveI := hγ.1
  have hs : ∀ x : part (PI (F := F)) ⊤ (ew F w), -WithZero.log (vw w x.1) = 0 ↔ x.1 ∈ UI F E := fun x => by
    refine ⟨fun h u => ?_, fun h => by rw [h w]; simp⟩
    by_cases hu : u = w
    · subst hu; rw [← WithZero.exp_log (vw_ne u x.1), neg_eq_zero.1 h]; rfl
    · rw [vw, ((mem_part_iff (ew_idem w) (inf_ew w) _).1 x.2).2 u (ew_zero.2 hu), map_one]
  have hs' : {x : part (PI (F := F)) ⊤ (ew F w) | -WithZero.log (vw w x.1) = 0} = {x | x.1 ∈ (UI F E : Set (AE F E)ˣ)} := Set.ext hs
  have := tate γ (fun x => -WithZero.log (vw w x.1)) (fun x y => by
      rw [Subgroup.coe_mul, vw_mul, WithZero.log_mul (vw_ne _ _) (vw_ne _ _)]; ring)
    (by rw [hs']; exact isOpen_UI.preimage continuous_subtype_val) (by rw [hs']; exact hγ.2) ⟨pw F w, loc_mem w _⟩
    (by show -WithZero.log (vw w (pw F w)) = 1; rw [vw_pw]; simp) ((wtH ν z).comp (Subgroup.subtype _))
    (fun x hx => by
      show wt ν z x.1 = 1
      rw [wt, nu_ew hν x.2 ((hs x).1 hx), abs_UI (ew_idem w) (inf_ew w) x.2 ((hs x).1 hx)]; simp)
    (by show ‖wt ν z (pw F w)‖ < 1; rw [wt_pw hB]; exact norm_t_lt ν hz w) m
  have e : ∀ x : part (PI (F := F)) ⊤ (ew F w), m ≤ -WithZero.log (vw w x.1) ↔ vw w x.1 ≤ WithZero.exp (-m) := fun x => by
    rw [← WithZero.log_le_iff_le_exp (vw_ne _ _)]; omega
  simp only [e] at this
  refine ⟨this.1, this.2.trans ?_⟩
  show wt ν z (pw F w) ^ m * (1 - wt ν z (pw F w))⁻¹ = _
  rw [wt_pw hB, tw]

theorem inf_sum (W : Finset (HeightOneSpectrum (𝓞 E))) {c : AE F E} (h0 : infTens F E c = 0) :
    infTens F E (∑ w ∈ W, ew F w + c) = 0 := by
  rw [map_add, h0, add_zero, map_sum, Finset.sum_eq_zero fun w _ => inf_ew w]

open Classical in
theorem prodW {B : Base F E} (hB : B.IsGood σ) {ν : Chr F E} {z : ℕ} (hz : 1 ≤ z) (W : Finset (HeightOneSpectrum (𝓞 E)))
    (hν : ∀ w ∈ W, UnrAt ν w) (m : HeightOneSpectrum (𝓞 E) → ℤ) {c : AE F E} (hc : c * c = c) (h0 : infTens F E c = 0)
    (hW : ∀ w ∈ W, ew F w * c = 0) (hνc : ∀ l ∈ part PI ⊤ c, l ∈ UI F E → ν l = 1) (b : AE F E) (hb : b = ∑ w ∈ W, ew F w + c)
    (μ : Measure (part (PI (F := F)) ⊤ b)) (hμ : μ.IsHaarMeasure ∧ μ {x | x.1 ∈ (UI F E : Set (AE F E)ˣ)} = 1) :
    Integrable (fun x : part PI ⊤ b => (if (∀ w ∈ W, vw w x.1 ≤ WithZero.exp (-m w)) ∧ PI c x.1 ∈ UI F E then (1 : ℂ) else 0) *
      wt ν z x.1) μ ∧
    ∫ x : part PI ⊤ b, (if (∀ w ∈ W, vw w x.1 ≤ WithZero.exp (-m w)) ∧ PI c x.1 ∈ UI F E then (1 : ℂ) else 0) * wt ν z x.1 ∂μ =
      ∏ w ∈ W, tw ν z (m w) w := by
  have hex := fun {a : AE F E} (ha : a * a = a) (h0 : infTens F E a = 0) =>
    exists_haar _ (sysI.closed ha) _ (UI F E).one_mem (co_I ha h0).1 (co_I ha h0).2
  choose γ hγ using fun w => hex (ew_idem w) (inf_ew (F := F) w)
  obtain ⟨β, hβ⟩ := hex hc h0
  have mU : MeasurableSet {x : part (PI (F := F)) ⊤ c | x.1 ∈ (UI F E : Set (AE F E)ˣ)} :=
    (isOpen_UI.preimage continuous_subtype_val).measurableSet
  have eg : (fun x : part (PI (F := F)) ⊤ c => (if x.1 ∈ UI F E then (1 : ℂ) else 0)) =
      Set.indicator {x | x.1 ∈ (UI F E : Set (AE F E)ˣ)} fun _ => 1 := funext fun x => by simp [Set.indicator_apply]
  obtain ⟨p1, p2⟩ := sysI.prod (ew F) ew_idem (fun _ _ => ew_orth) c hc γ hγ β hβ W hW
    (fun T' h => co_I (sysI.good_sum _ ew_idem (fun _ _ => ew_orth) c hc T' fun w hw => hW w (h hw)) (inf_sum T' h0)) b hb μ hμ
    (fun w x => (if vw w x ≤ WithZero.exp (-m w) then (1 : ℂ) else 0) * wt ν z x) (fun x => if x ∈ UI F E then 1 else 0)
    (fun w hw => (locW hB hz (hν w hw) (m w) _ (hγ w)).1)
    (by rw [eg, integrable_indicator_iff mU]; exact integrableOn_const (by rw [hβ.2]; simp))
  rw [Finset.prod_congr rfl fun w hw => (locW hB hz (hν w hw) (m w) _ (hγ w)).2, eg, integral_indicator mU, setIntegral_const,
    Measure.real, hβ.2] at p2
  have e : (fun x : part (PI (F := F)) ⊤ b => (if (∀ w ∈ W, vw w x.1 ≤ WithZero.exp (-m w)) ∧ PI c x.1 ∈ UI F E then (1 : ℂ) else 0) *
      wt ν z x.1) = fun x : part PI ⊤ b => (∏ w ∈ W, (if vw w (PI (ew F w) x.1) ≤ WithZero.exp (-m w) then (1 : ℂ) else 0) *
        wt ν z (PI (ew F w) x.1)) * (if PI c x.1 ∈ UI F E then 1 else 0) := funext fun x => by
    have hv : ∀ w, vw w (PI (ew F w) x.1) = vw w x.1 := fun w => by
      rw [vw, cw_PI_one (ew_idem w) (by rw [cw_ew, if_pos rfl])]; rfl
    by_cases hu : PI c x.1 ∈ UI F E
    · have hx : x.1 = (∏ w ∈ W, PI (ew F w) x.1) * PI c x.1 := by
        rw [← PI_sum _ ew_idem (fun _ _ => ew_orth) c hc W hW, ← hb]; exact x.2.2.symm
      have hw : wt ν z x.1 = ∏ w ∈ W, wt ν z (PI (ew F w) x.1) := by
        have := congrArg (wtH ν z) hx
        rw [map_mul, map_prod] at this
        refine this.trans ?_
        show _ * wt ν z _ = _
        rw [wt, hνc _ (PI_mem hc _) hu, abs_UI hc h0 (PI_mem hc _) hu]
        simp [wtH]
      simp only [hv, hu, and_true, if_true, mul_one, Finset.prod_mul_distrib, Finset.prod_boole, hw]
    · simp [hu]
  rw [e]
  exact ⟨p1, p2.trans (by simp)⟩

open Classical in

def ab (T : Finset (Pl F)) : Finset (HeightOneSpectrum (𝓞 E)) := T.biUnion (Formalism.L2.Host.aboveF (L := E) F)

theorem mem_ab {T : Finset (Pl F)} {w : HeightOneSpectrum (𝓞 E)} : w ∈ ab T ↔ w.under (𝓞 F) ∈ T := by
  simp [ab, mem_aboveF]

open Classical in
theorem rest_split {T T' : Finset (Pl F)} (h : T ⊆ T') :
    (io (rest T) : AE F E) = ∑ w ∈ ab (T' \ T), ew F w + io (rest T') := by
  refine ae_ext (by rw [inf_io (rest_fst _), inf_sum _ (inf_io (rest_fst _))]) fun u => ?_
  rw [map_add, map_sum, cw_rest, cw_rest]
  simp only [cw_ew, Finset.sum_ite_eq, mem_ab, Finset.mem_sdiff]
  by_cases h1 : u.under (𝓞 F) ∈ T
  · simp [h1, h h1]
  · by_cases h2 : u.under (𝓞 F) ∈ T' <;> simp [h1, h2]

theorem ew_rest {T : Finset (Pl F)} {w : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) ∈ T) : ew F w * io (rest T) = 0 :=
  ae_ext (by rw [map_mul, inf_ew, zero_mul, map_zero]) fun u => by
    rw [map_mul, cw_ew, cw_rest, map_zero]
    split_ifs with h1 h2
    · simp
    · exact absurd (h1 ▸ h) h2
    all_goals simp

theorem rest_zero {T : Finset (Pl F)} {w : HeightOneSpectrum (𝓞 E)} : cw w (io (rest T) : AE F E) = 0 ↔ w.under (𝓞 F) ∈ T := by
  rw [cw_rest]; split_ifs with h <;> simp [h]

theorem nu_rest {ν : Chr F E} (hc : Continuous ν) {T : Finset (Pl F)} (hν : UnrOff ν (T : Set (Pl F))) {l}
    (h : l ∈ part PI ⊤ (io (rest T))) (hu : l ∈ UI F E) : ν l = 1 := by
  classical
  have hi := fun T : Finset (Pl F) => io_idem (E := E) (rest_idem T)
  have h0 := fun T : Finset (Pl F) => inf_io (E := E) (rest_fst T)
  have mono : ∀ {A A' : Finset (Pl F)}, A ⊆ A' → ((part PI ⊤ (io (rest A')) : Subgroup (AE F E)ˣ) : Set (AE F E)ˣ) ∩ UI F E ⊆
      ((part PI ⊤ (io (rest A)) : Subgroup (AE F E)ˣ) : Set (AE F E)ˣ) ∩ UI F E := by
    intro A A' hA x hx
    have h1 := (mem_part_iff (hi A') (h0 A') x).1 hx.1
    exact ⟨(mem_part_iff (hi A) (h0 A) x).2 ⟨h1.1, fun w hw => h1.2 w (rest_zero.2 (hA (rest_zero.1 hw)))⟩, hx.2⟩
  obtain ⟨T₀, hT₀⟩ := exists_subset_nhds_of_isCompact'
    (V := fun A : Finset (Pl F) => ((part PI ⊤ (io (rest A)) : Subgroup (AE F E)ˣ) : Set (AE F E)ˣ) ∩ UI F E)
    (fun A A' => ⟨A ∪ A', mono Finset.subset_union_left, mono Finset.subset_union_right⟩) (fun A => cpt_I (hi A) (h0 A))
    (fun A => (cpt_I (hi A) (h0 A)).isClosed) (U := {x | ‖(ν x : ℂ) - 1‖ < 1}) fun x hx => by
      have hx' := Set.mem_iInter.1 hx
      obtain rfl : x = 1 := Units.ext (ae_ext (by rw [((mem_part_iff (hi ∅) (h0 ∅) x).1 (hx' ∅).1).1, Units.val_one, map_one])
        fun w => by
          rw [((mem_part_iff (hi _) (h0 _) x).1 (hx' {w.under (𝓞 F)}).1).2 w (rest_zero.2 (Finset.mem_singleton_self _)),
            Units.val_one, map_one])
      exact (isOpen_lt ((continuous_subtype_val.comp hc).sub continuous_const).norm continuous_const).mem_nhds
        (show ‖((ν 1 : Circle) : ℂ) - 1‖ < 1 by rw [map_one]; simp)
  have hx : l = (∏ w ∈ ab ((T ∪ T₀) \ T), PI (ew F w) l) * PI (io (rest (T ∪ T₀))) l := by
    rw [← PI_sum _ ew_idem (fun _ _ => ew_orth) _ (hi _) _ fun w hw => ew_rest (Finset.mem_sdiff.1 (mem_ab.1 hw)).1,
      ← rest_split Finset.subset_union_left]
    exact h.2.symm
  rw [hx, map_mul, map_prod, Finset.prod_eq_one fun w hw => nu_ew (hν w (Finset.mem_sdiff.1 (mem_ab.1 hw)).2) (PI_mem (ew_idem w) _)
    (sysI.pU _ (ew_idem w) _ hu), one_mul]
  refine circle_one fun n => ?_
  rw [← map_pow]
  exact hT₀ (mono Finset.subset_union_right ⟨Subgroup.pow_mem _ (PI_mem (hi _) _) n, Subgroup.pow_mem _ (sysI.pU _ (hi _) _ hu) n⟩)

end PositivityTheory.ThKG.Loc.Cone

end
