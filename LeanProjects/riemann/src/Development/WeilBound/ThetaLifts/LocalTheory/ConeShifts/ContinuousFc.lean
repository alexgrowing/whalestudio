import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.ExtendByZeroOnSubsetApplyCoe
import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.FubTate
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrdLEqNegLog
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormCmExtensionSplitPlaceEqZpow
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IntegralFiniteAdeleCompactClosedMultiples

noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.ThKG.Fub GlobalTheory.Doubling

attribute [local instance] ae_ring ae_smul ae_t2 ae_lc ae_sc

theorem id_lc : LocallyCompactSpace (AE F E)ˣ := units_top.1
theorem id_sc : SecondCountableTopology (AE F E)ˣ := units_top.2
theorem id_borel : BorelSpace (AE F E)ˣ := ⟨rfl⟩

attribute [local instance] id_lc id_sc id_borel

variable (F E) in

def fc : AE F E →+* FiniteAdeleRing (𝓞 E) E := (finAdEquiv F E).toRingHom.comp (finTens F E)

def cw (w : HeightOneSpectrum (𝓞 E)) : AE F E →+* w.adicCompletion E := (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV E w).toRingHom.comp (fc F E)

theorem cw_def (w : HeightOneSpectrum (𝓞 E)) (x : AE F E) : cw w x = finAdEquiv F E (finTens F E x) w := rfl

theorem ae_ext {x y : AE F E} (h1 : infTens F E x = infTens F E y) (h2 : ∀ w, cw w x = cw w y) : x = y :=
  tens_ext h1 ((finAdEquiv F E).injective (FiniteAdeleRing.ext _ h2))

theorem cw_eq {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) = v) (x : AE F E) : cw w x = toCompl h (compFin F E v x) := by
  rw [cw_def, finAdEquiv_apply h]
  congr 1
  change ((Algebra.TensorProduct.map _ _).comp (Algebra.TensorProduct.map _ _)) _ = _
  rw [← Algebra.TensorProduct.map_comp]
  rfl

theorem continuous_fc : Continuous (fc F E) := by
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele E
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Af F)
  haveI : LocallyCompactSpace (Af F ⊗[F] E) := e0.isClosedEmbedding.locallyCompactSpace
  haveI : T2Space (Af F ⊗[F] E) := e0.isEmbedding.t2Space
  have ho : IsOpenMap (finAdEquiv F E).symm :=
    AddMonoidHom.isOpenMap_of_sigmaCompact (finAdEquiv F E).symm.toAddEquiv.toAddMonoidHom (finAdEquiv F E).symm.surjective
      continuous_finAdEquiv_symm
  have h1 : Continuous (finAdEquiv F E) :=
    ((finAdEquiv F E).symm.toEquiv.toHomeomorphOfContinuousOpen continuous_finAdEquiv_symm ho).symm.continuous
  exact h1.comp (GlobalTheory.AutFunCompare.continuous_tensNU (E := E) (sndA F).toLinearMap (map_mul (sndA F)) continuous_snd)

def io (a : AF F) : AE F E := algebraMap (AF F) (AE F E) a

theorem cw_io (w : HeightOneSpectrum (𝓞 E)) (a : AF F) : cw w (io a : AE F E) = complMap rfl (evFin F (w.under (𝓞 F)) a) :=
  (finAdEquiv_tmul a.2 (1 : E) w).trans (by rw [map_one, mul_one]; rfl)

theorem inf_io {a : AF F} (h : a.1 = 0) : infTens F E (io a) = 0 := by
  show a.1 ⊗ₜ[F] (1 : E) = 0
  rw [h, TensorProduct.zero_tmul]

theorem io_mul (a b : AF F) : (io a * io b : AE F E) = io (a * b) := (map_mul _ _ _).symm
theorem io_idem {a : AF F} (h : a * a = a) : (io a * io a : AE F E) = io a := by rw [io_mul, h]
theorem io_orth {a b : AF F} (h : a * b = 0) : (io a * io b : AE F E) = 0 := by rw [io_mul, h]; exact map_zero _

variable (F) in

def ew (w : HeightOneSpectrum (𝓞 E)) : AE F E := extZero F E ((finAdEquiv F E).symm (1 - Neutral.B1.finiteSingle E w 0))

theorem inf_ew (w : HeightOneSpectrum (𝓞 E)) : infTens F E (ew F w) = 0 := infTens_extZero _

open Classical in
theorem cw_ew (u w : HeightOneSpectrum (𝓞 E)) : cw u (ew F w) = if u = w then 1 else 0 := by
  rw [cw_def, ew, finTens_extZero, RingEquiv.apply_symm_apply]
  show 1 - Neutral.B1.finiteSingle E w 0 u = _
  split_ifs with h
  · subst h; rw [finSingle_self, sub_zero]
  · rw [finSingle_ne h, sub_self]

theorem ew_idem (w : HeightOneSpectrum (𝓞 E)) : ew F w * ew F w = ew F w :=
  ae_ext (by rw [map_mul, inf_ew, mul_zero]) fun u => by rw [map_mul, cw_ew]; split_ifs <;> simp

theorem ew_orth {w w' : HeightOneSpectrum (𝓞 E)} (h : w ≠ w') : ew F w * ew F w' = 0 :=
  ae_ext (by rw [map_mul, inf_ew, zero_mul, map_zero]) fun u => by
    rw [map_mul, cw_ew, cw_ew, map_zero]
    split_ifs with h1 h2
    · exact absurd (h1.symm.trans h2) h
    all_goals simp

open Classical in
theorem cw_idem (w : HeightOneSpectrum (𝓞 E)) (v : Pl F) : cw w (io (idem F v) : AE F E) = if w.under (𝓞 F) = v then 1 else 0 := by
  rw [cw_io]
  split_ifs with h
  · subst h; rw [evFin_idem_self_k, map_one]
  · rw [evFin_idem_ne_k h, map_zero]

open Classical in
theorem cw_rest (w : HeightOneSpectrum (𝓞 E)) (T : Finset (Pl F)) :
    cw w (io (rest T) : AE F E) = if w.under (𝓞 F) ∈ T then 0 else 1 := by
  rw [cw_io, evFin_rest]; split_ifs <;> simp

theorem idem_eq_sum (v : Pl F) : (io (idem F v) : AE F E) = ∑ w ∈ Formalism.L2.Host.aboveF (L := E) F v, ew F w + 0 := by
  classical
  refine ae_ext (by rw [inf_io rfl, add_zero, map_sum, Finset.sum_eq_zero fun w _ => inf_ew w]) fun u => ?_
  rw [add_zero, map_sum, cw_idem]
  simp only [cw_ew, Finset.sum_ite_eq, mem_aboveF]

abbrev PI (a : AE F E) : (AE F E)ˣ →* (AE F E)ˣ := unitP (R := AE F E) a

theorem hom_PI {A : Type} [CommRing A] (φ : AE F E →+* A) {a : AE F E} (h : a * a = a) (l : (AE F E)ˣ) :
    φ (PI a l) = φ a * φ l + (1 - φ a) := by
  rw [coe_unitP h]; simp

theorem cw_PI_one {a : AE F E} (h : a * a = a) {w} (h1 : cw w a = 1) (l : (AE F E)ˣ) : cw w (PI a l : AE F E) = cw w (l : AE F E) := by
  rw [hom_PI _ h, h1]; simp

theorem cw_PI_zero {a : AE F E} (h : a * a = a) {w} (h1 : cw w a = 0) (l : (AE F E)ˣ) : cw w (PI a l : AE F E) = 1 := by
  rw [hom_PI _ h, h1]; simp

theorem cw_cases {a : AE F E} (h : a * a = a) (w) : cw w a = 0 ∨ cw w a = 1 :=
  IsIdempotentElem.iff_eq_zero_or_one.1 (show _ * _ = _ by rw [← map_mul, h])

def vw (w : HeightOneSpectrum (𝓞 E)) (l : (AE F E)ˣ) : WithZero (Multiplicative ℤ) := Valued.v (cw w (l : AE F E))

theorem vw_mul (w) (l l' : (AE F E)ˣ) : vw w (l * l') = vw w l * vw w l' := by simp [vw]
theorem vw_one (w) : vw w (1 : (AE F E)ˣ) = 1 := by simp [vw]
theorem vw_inv (w) (l : (AE F E)ˣ) : vw w l * vw w l⁻¹ = 1 := by rw [← vw_mul, mul_inv_cancel, vw_one]
theorem vw_ne (w) (l : (AE F E)ˣ) : vw w l ≠ 0 := left_ne_zero_of_mul_eq_one (vw_inv w l)

variable (F E) in

def UI : Subgroup (AE F E)ˣ where
  carrier := {l | ∀ w, vw w l = 1}
  one_mem' := vw_one
  mul_mem' h h' w := by rw [vw_mul, h w, h' w, one_mul]
  inv_mem' {l} h w := by have := vw_inv w l; rwa [h w, one_mul] at this

theorem mem_UI_iff (l : (AE F E)ˣ) : l ∈ UI F E ↔ (∀ w, vw w l ≤ 1) ∧ ∀ w, vw w l⁻¹ ≤ 1 :=
  ⟨fun h => ⟨fun w => (h w).le, fun w => ((UI F E).inv_mem h w).le⟩, fun h w => le_antisymm (h.1 w) (by
    calc 1 = vw w l * vw w l⁻¹ := (vw_inv w l).symm
      _ ≤ vw w l * 1 := mul_le_mul_right (h.2 w) _
      _ = vw w l := mul_one _)⟩

theorem isOpen_UI : IsOpen (UI F E : Set (AE F E)ˣ) := by
  have h : IsOpen {a : FiniteAdeleRing (𝓞 E) E | ∀ w, a w ∈ HeightOneSpectrum.adicCompletionIntegers E w} :=
    RestrictedProduct.isOpen_forall_mem fun w => Valued.isOpen_integer _
  have h1 := h.preimage (continuous_fc (F := F))
  have : (UI F E : Set (AE F E)ˣ) = (Units.val ⁻¹' (fc F E ⁻¹' {a | ∀ w, a w ∈ HeightOneSpectrum.adicCompletionIntegers E w})) ∩ ((fun l : (AE F E)ˣ => ((l⁻¹ : (AE F E)ˣ) : AE F E)) ⁻¹'
      (fc F E ⁻¹' {a | ∀ w, a w ∈ HeightOneSpectrum.adicCompletionIntegers E w})) := Set.ext fun l => mem_UI_iff l
  rw [this]
  exact (h1.preimage Units.continuous_val).inter (h1.preimage Units.continuous_coe_inv)

theorem sysI : Sys (PI (F := F) (E := E)) ⊤ (UI F E) fun a => a * a = a where
  cont a ha := unitInvariant_continuous ha
  comp a b ha hb := unitInvariant_comp ha hb
  zero := unitInvariant_zero
  add a b ha hb h := ⟨idem_add ha hb h, unitInvariant_add ha hb h⟩
  idem _ h := h
  cK := isClosed_univ
  mK _ _ _ _ := trivial
  mU := isOpen_UI.measurableSet
  one := (UI F E).one_mem
  mul _ h _ h' := (UI F E).mul_mem h h'
  pU a ha l hl w := by
    rcases cw_cases ha w with e | e
    · rw [vw, cw_PI_zero ha e, map_one]
    · rw [vw, cw_PI_one ha e]; exact hl w

theorem inf_of_part {a : AE F E} (ha : a * a = a) (h0 : infTens F E a = 0) {l : (AE F E)ˣ} (h : l ∈ part PI ⊤ a) :
    infTens F E l = 1 := by
  rw [← show PI a l = l from h.2, hom_PI _ ha, h0]; simp

theorem cpt_I {a : AE F E} (ha : a * a = a) (h0 : infTens F E a = 0) :
    IsCompact ((part PI ⊤ a : Set (AE F E)ˣ) ∩ UI F E) := by
  let j : FiniteAdeleRing (𝓞 E) E → AE F E := fun y => 1 - extZero F E 1 + extZero F E ((finAdEquiv F E).symm y)
  have hj : Continuous j := continuous_const.add (continuous_extZero.comp continuous_finAdEquiv_symm)
  have hS := (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties E).1.image hj
  have hc := hS.prod (hS.image MulOpposite.continuous_op)
  have key : ∀ l ∈ (part PI ⊤ a : Set (AE F E)ˣ) ∩ UI F E, ∃ y, (∀ w, y w ∈ HeightOneSpectrum.adicCompletionIntegers E w) ∧
      j y = (l : AE F E) := fun l hl => ⟨fc F E l, fun w => (hl.2 w).le, tens_ext
        (by rw [inf_of_part ha h0 hl.1, map_add, map_sub, map_one, infTens_extZero, infTens_extZero, sub_zero, add_zero])
        (by rw [map_add, map_sub, map_one, finTens_extZero, finTens_extZero, sub_self, zero_add]
            exact (finAdEquiv F E).symm_apply_apply _)⟩
  refine (Units.isClosedEmbedding_embedProduct.isCompact_preimage hc).of_isClosed_subset
    ((sysI.closed ha).inter ((UI F E).isClosed_of_isOpen isOpen_UI)) fun l hl => ⟨key l hl, _, key l⁻¹
      ⟨Subgroup.inv_mem _ hl.1, (UI F E).inv_mem hl.2⟩, rfl⟩

theorem co_I {a : AE F E} (ha : a * a = a) (h0 : infTens F E a = 0) : CO PI ⊤ (UI F E : Set (AE F E)ˣ) a := by
  refine ⟨?_, isOpen_UI.preimage continuous_subtype_val⟩
  have := (sysI.closed ha).isClosedEmbedding_subtypeVal.isCompact_preimage (cpt_I ha h0)
  exact this.of_isClosed_subset (((UI F E).isClosed_of_isOpen isOpen_UI).preimage continuous_subtype_val) fun x hx => ⟨x.2, hx⟩

theorem coe_PI_io {a : AF F} (h : a * a = a) (l : (AE F E)ˣ) :
    (PI (io a) l : AE F E) = a • (l : AE F E) + (1 - a) • (1 : AE F E) := by
  rw [coe_unitP (io_idem h), smul_eq_mul, smul_eq_mul, Algebra.smul_def, Algebra.smul_def, map_sub, map_one]; rfl

theorem idAt_eq {R : Type} [Zero R] (ev : AF F → R) {a : AF F} (h : a * a = a) (hat : ∀ z : AE F E, At ev z ↔ a • z = z) :
    idAt E ev = part PI ⊤ (io a) := by
  have : {l : (AE F E)ˣ | At ev ((l : AE F E) - 1)} = ((part PI ⊤ (io a) : Subgroup (AE F E)ˣ) : Set (AE F E)ˣ) := Set.ext fun l => by
    show At ev ((l : AE F E) - 1) ↔ l ∈ part PI ⊤ (io a)
    rw [hat, fix_iff, ← coe_PI_io h, mem_part]
    exact ⟨fun e => ⟨trivial, Units.ext e⟩, fun e => congrArg Units.val e.2⟩
  rw [idAt, this, Subgroup.closure_eq]

theorem units_eq (v : Pl F) : {l : idAt E (evFin F v) | IsCompact (closure (Subgroup.zpowers l : Set (idAt E (evFin F v))))} =
    {l | l.1 ∈ (UI F E : Set (AE F E)ˣ)} := by
  have h := co_I (E := E) (io_idem (idem_idem v)) (inf_io rfl)
  rw [CO, ← idAt_eq (evFin F v) (idem_idem v) fun _ => at_fin_iff] at h
  refine Set.ext fun l => ⟨fun hl w => ?_, fun hl => h.1.of_isClosed_subset isClosed_closure (closure_minimal ?_ h.1.isClosed)⟩
  · obtain ⟨k, hk, hm⟩ := pow_mem_of_compact ((UI F E).subgroupOf _) h.2 hl fun n =>
      subset_closure (Subgroup.npow_mem_zpowers l n)
    have h1 : vw w (l.1 ^ k) = 1 := hm w
    rw [vw, Units.val_pow_eq_pow_val, map_pow, map_pow] at h1
    exact (pow_eq_one_iff_of_nonneg zero_le' hk.ne').1 h1
  · rintro _ ⟨n, rfl⟩
    exact (UI F E).zpow_mem hl n

theorem measEx_of (hS : StabEx) : MeasEx := by
  intro F E _ _ _ _ _ σ B n X r s hB hX K hK
  haveI := (ua_top (σ := σ) X.J).1
  haveI := (ua_top (σ := σ) X.J).2
  haveI := borelUA (σ := σ) X.J
  have hc := stab_compact hS hB hX hK
  have sy := sysU hK hc
  have ei := kAt_eq K (evI F) real_idem fun _ => at_inf_iff
  have ef := fun v => kAt_eq K (evFin F v) (idem_idem v) fun _ => at_fin_iff
  have di := idAt_eq (E := E) (evI F) real_idem fun _ => at_inf_iff
  have df := fun v => idAt_eq (E := E) (evFin F v) (idem_idem v) fun _ => at_fin_iff
  have h1 : ∀ {a}, Gd a → ∀ S, S = part (PU σ X.J) K a → ∃ μ : Measure S, μ.IsHaarMeasure ∧ μ Set.univ = 1 := by
    rintro a ha S rfl
    exact exists_haar _ (sy.closed ha) Set.univ trivial (co_U hK hc ha).1 (co_U hK hc ha).2
  have h2 : ∀ S : Subgroup (AE F E)ˣ, ∀ P : Set S, (∃ μ : Measure S, μ.IsHaarMeasure ∧ μ P = 1) →
      ∃ μ : @Measure S (borel _), @Measure.IsHaarMeasure _ _ _ (borel _) μ ∧ μ P = 1 := fun S P h => by
    have : borel S = Subtype.instMeasurableSpace := (@BorelSpace.measurable_eq S _ Subtype.instMeasurableSpace (Subtype.borelSpace _)).symm
    rw [this]; exact h
  choose kf hkf using fun v => h1 (gd_idem v) _ (ef v)
  obtain ⟨ki, hki⟩ := h1 gd_real _ ei
  have h3 : ∀ v, ∃ μ : Measure (idAt E (evFin F v)), μ.IsHaarMeasure ∧ μ {l | l.1 ∈ (UI F E : Set (AE F E)ˣ)} = 1 := fun v => by
    have h := co_I (E := E) (io_idem (idem_idem v)) (inf_io rfl)
    have hcl := sysI.closed (io_idem (E := E) (idem_idem v))
    rw [CO, ← df v] at h
    rw [← df v] at hcl
    exact exists_haar _ hcl _ (UI F E).one_mem h.1 h.2
  choose xf hxf using fun v => h2 _ _ (h3 v)
  haveI : LocallyCompactSpace (idAt E (evI F)) := by
    have hcl := sysI.closed (io_idem (E := E) (real_idem (F := F)))
    rw [← di] at hcl; exact hcl.locallyCompactSpace
  letI : MeasurableSpace (idAt E (evI F)) := borel _
  haveI : BorelSpace (idAt E (evI F)) := ⟨rfl⟩
  exact ⟨⟨kf, xf, ki, Measure.haar⟩, hkf, fun v => ⟨(hxf v).1, by rw [units_eq]; exact (hxf v).2⟩, hki.1, inferInstance⟩

end PositivityTheory.ThKG.Loc.Cone

end
