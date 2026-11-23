import Development.WeilBound.ThetaLifts.LocalTheory.StandardValuations.IntIndPow
import Development.WeilBound.ThetaLifts.LocalTheory.IsArchimedeanLocalEquivariantMap
import Development.WeilBound.ThetaLifts.LocalTheory.StandardValuations.ValIffNorm

set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKG.Std

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip Matrix
open PositivityTheory.KCo PositivityTheory.ThK.SplitDict PositivityTheory.ThKG.StdDict PositivityTheory.ThKG.Loc MeasureTheory ValuativeRel Topology GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {t : E →ₐ[F] Fv F v} {sec : Fv F v × Fv F v → AE F E}

theorem cont_piW (t : E →ₐ[F] Fv F v) : Continuous (piW t) := by
  have hev : Continuous (evFin F v) := (RestrictedProduct.continuous_eval v).comp continuous_snd
  exact (continuous_splitProj t).comp (GlobalTheory.AutFunCompare.continuous_tensNU (E := E) (evFin F v).toLinearMap
    (fun a b => map_mul (evFin F v) a b) hev)

theorem at_mul {a b : AE F E} (ha : At (evFin F v) (a - 1)) (hb : At (evFin F v) (b - 1)) : At (evFin F v) (a * b - 1) := fun u hu => by
  rw [show a * b - 1 = (a - 1) * b + (b - 1) by ring, smul_add, ← smul_mul_assoc, ha u hu, hb u hu, zero_mul, add_zero]

theorem at_idAt {l : (AE F E)ˣ} (h : l ∈ idAt E (evFin F v)) : At (evFin F v) ((l : AE F E) - 1) := by
  induction h using Subgroup.closure_induction with
  | mem u hu => exact hu
  | one => intro u _; simp
  | mul a b _ _ ha hb => exact at_mul ha hb
  | inv a _ ha =>
    intro u hu
    rw [show ((a⁻¹ : (AE F E)ˣ) : AE F E) - 1 = -(((a : AE F E) - 1) * (a⁻¹ : (AE F E)ˣ)) by simp [sub_mul], smul_neg,
      ← smul_mul_assoc, ha u hu, zero_mul, neg_zero]

theorem ext1 (h : IsSec σ t sec) {a b : AE F E} (ha : At (evFin F v) (a - 1)) (hb : At (evFin F v) (b - 1)) (h1 : piW t a = piW t b)
    (h2 : piW (t.comp σ) a = piW (t.comp σ) b) : a = b := by
  have := ha.kd_sub hb
  rw [sub_sub_sub_cancel_right] at this
  exact sub_eq_zero.1 (h.ext _ this (by rw [map_sub, h1, sub_self]) (by rw [map_sub, h2, sub_self]))

def uI (h : IsSec σ t sec) (x y : (Fv F v)ˣ) : idAt E (evFin F v) :=
  have at1 : ∀ p, At (evFin F v) (1 + sec p - 1) := fun p => by rw [add_sub_cancel_left]; exact h.at' p
  have m : ∀ x y : (Fv F v)ˣ, (1 + sec (x - 1, y - 1)) * (1 + sec ((x⁻¹ : (Fv F v)ˣ) - 1, (y⁻¹ : (Fv F v)ˣ) - 1)) = 1 := fun x y =>
    ext1 h (at_mul (at1 _) (at1 _)) (fun u _ => by simp) (by simp [h.fst]) (by simp [h.snd])
  ⟨⟨1 + sec (x - 1, y - 1), 1 + sec ((x⁻¹ : (Fv F v)ˣ) - 1, (y⁻¹ : (Fv F v)ˣ) - 1), m x y, by rw [mul_comm]; exact m x y⟩,
    Subgroup.subset_closure (at1 _)⟩

theorem uI_fst (h : IsSec σ t sec) (x y : (Fv F v)ˣ) : piW t ((uI h x y).1 : AE F E) = x := by
  show piW t (1 + _) = _
  simp [h.fst]

theorem uI_snd (h : IsSec σ t sec) (x y : (Fv F v)ˣ) : piW (t.comp σ) ((uI h x y).1 : AE F E) = y := by
  show piW _ (1 + _) = _
  simp [h.snd]

def cmp (t : E →ₐ[F] Fv F v) : idAt E (evFin F v) →* (Fv F v)ˣ :=
  (Units.map (piW t).toMonoidHom).comp (idAt E (evFin F v)).subtype

theorem cmp_val (l : idAt E (evFin F v)) : (cmp t l : Fv F v) = piW t (l.1 : AE F E) := rfl

theorem ext2 (h : IsSec σ t sec) {a b : idAt E (evFin F v)} (h1 : cmp t a = cmp t b) (h2 : cmp (t.comp σ) a = cmp (t.comp σ) b) :
    a = b := Subtype.ext (Units.ext (ext1 h (at_idAt a.2) (at_idAt b.2) (congrArg Units.val h1) (congrArg Units.val h2)))

theorem cmp_uI (h : IsSec σ t sec) (x y : (Fv F v)ˣ) : cmp t (uI h x y) = x ∧ cmp (t.comp σ) (uI h x y) = y :=
  ⟨Units.ext (uI_fst h x y), Units.ext (uI_snd h x y)⟩

theorem chr_id (hσ : IsCMExt F E σ) (χ : Chr F E) (l : idAt E (evFin F v)) :
    (χ l.1 : ℂ) = chrW χ t (cmp t l) * chrW χ (t.comp σ) (cmp (t.comp σ) l) := by
  obtain ⟨⟨sec, h⟩, -⟩ := section_statement F E σ hσ v t
  obtain ⟨⟨sec', h'⟩, -⟩ := section_statement F E σ hσ v (t.comp σ)
  have e : l = uI h (cmp t l) 1 * uI h 1 (cmp (t.comp σ) l) := ext2 h (by simp [cmp_uI]) (by simp [cmp_uI])
  conv_lhs => rw [e]
  rw [Subgroup.coe_mul, map_mul, Circle.coe_mul, (h.idele _ _ (at_idAt (uI h _ 1).2) (uI_fst h _ _) (uI_snd h _ _)).1 χ,
    (h'.idele _ _ (at_idAt (uI h 1 _).2) (uI_snd h _ _) (by rw [comp_comp hσ]; exact uI_fst h _ _)).1 χ]

theorem abs_id (hσ : IsCMExt F E σ) (l : idAt E (evFin F v)) :
    (absE F E l.1 : ℝ) = GlobalTheory.SplitWeil.nabs _ (cmp t l) * GlobalTheory.SplitWeil.nabs _ (cmp (t.comp σ) l) := by
  obtain ⟨⟨sec, h⟩, -⟩ := section_statement F E σ hσ v t
  have e1 : l.1 = GlobalTheory.Doubling.ideleAt F E v (GlobalTheory.Doubling.unitFin F E v l.1) := Units.ext (by
    change (l.1 : AE F E) = 1 - GlobalTheory.EmbChart.tensAt E v 1 + GlobalTheory.EmbChart.tensAt E v (compFin F E v l.1)
    have o := off_of_at (at_idAt l.2)
    rw [← PositivityTheory.Member.ZakTransform.ep_smul, ← map_one (compFin F E v), ← PositivityTheory.Member.ZakTransform.ep_smul]
    rw [sub_smul, sub_smul, one_smul, one_smul] at o
    rw [← o, sub_add_cancel])
  have e2 : evFin F v (Algebra.norm (AF F) (l.1 : AE F E)) = cmp t l * cmp (t.comp σ) l := by
    have := congrArg (piW t) (GlobalTheory.Doubling.algebraMap_norm_eq hσ (l.1 : AE F E))
    rw [Algebra.algebraMap_eq_smul_one, (h.smul _ _).1, map_one, mul_one, map_mul] at this
    rw [this]
    exact congrArg _ (h.conj _).1
  rw [e1, GlobalTheory.Doubling.absE_ideleAt, GlobalTheory.Doubling.absEv_unitFin, e2, coe_nnnorm, norm_mul,
    norm_nabs, norm_nabs]

theorem units_eq (h : IsSec σ t sec) : {l | IsCompact (closure (Subgroup.zpowers l : Set (idAt E (evFin F v))))} =
    {l | valuation _ (cmp t l : Fv F v) = 1 ∧ valuation _ (cmp (t.comp σ) l : Fv F v) = 1} := by
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul _ _
  ext l
  constructor
  · intro hl
    have key : ∀ s : E →ₐ[F] Fv F v, valuation _ (cmp s l : Fv F v) = 1 := fun s => by
      have hc : Continuous fun a : idAt E (evFin F v) => ‖(cmp s a : Fv F v)‖ :=
        ((cont_piW s).comp (Units.continuous_val.comp continuous_subtype_val)).norm
      obtain ⟨C, hC⟩ := (IsCompact.image hl hc).bddAbove
      have hb : ∀ n : ℤ, ‖(cmp s l : Fv F v)‖ ^ n ≤ C := fun n => by
        have := hC ⟨l ^ n, subset_closure ⟨n, rfl⟩, rfl⟩
        simpa only [map_zpow, Units.val_zpow_eq_zpow_val, norm_zpow] using this
      have h0 : 0 < ‖(cmp s l : Fv F v)‖ := norm_pos_iff.2 (cmp s l).ne_zero
      rw [val_iff_norm]
      by_contra hne
      rcases lt_or_gt_of_ne hne with h1 | h1
      · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C ((one_lt_inv₀ h0).2 h1)
        exact absurd (hb (-n)) (by rw [_root_.zpow_neg, zpow_natCast, ← inv_pow]; exact not_le.2 hn)
      · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C h1
        exact absurd (hb n) (by rw [zpow_natCast]; exact not_le.2 hn)
    exact ⟨key _, key _⟩
  · rintro ⟨h1, h2⟩
    have cs : Continuous sec := by
      have : sec = fun p => sgl v p.1 • sec (1, 0) + sgl v p.2 • sec (0, 1) := funext fun p =>
        sub_eq_zero.1 (h.ext _ ((h.at' p).kd_sub ((at_sgl_smul _ _).kd_add (at_sgl_smul _ _)))
          (by simp [(h.smul _ _).1, h.fst, ev_sgl]) (by simp [(h.smul _ _).2, h.snd, ev_sgl]))
      have c1 : Continuous (sgl (F := F) v) := continuous_const.prodMk (continuous_singleFin v)
      rw [this]
      exact ((c1.comp continuous_fst).smul continuous_const).add ((c1.comp continuous_snd).smul continuous_const)
    have cu : Continuous fun p : (Fv F v)ˣ × (Fv F v)ˣ => uI h p.1 p.2 := by
      refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
      · exact continuous_const.add (cs.comp (((Units.continuous_val.comp continuous_fst).sub continuous_const).prodMk
          ((Units.continuous_val.comp continuous_snd).sub continuous_const)))
      · exact continuous_const.add (cs.comp (((Units.continuous_coe_inv.comp continuous_fst).sub continuous_const).prodMk
          ((Units.continuous_coe_inv.comp continuous_snd).sub continuous_const)))
    have ck : IsCompact {x : (Fv F v)ˣ | valuation _ (x : Fv F v) = 1} := by
      rw [Units.isEmbedding_val₀.isCompact_iff]
      have : Units.val '' {x : (Fv F v)ˣ | valuation _ (x : Fv F v) = 1} =
          {x | valuation _ x ≤ valuation (Fv F v) 1} ∩ Metric.sphere 0 1 := by
        ext x
        simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_inter_iff, mem_sphere_zero_iff_norm, ← val_iff_norm, map_one]
        exact ⟨by rintro ⟨u, hu, rfl⟩; exact ⟨hu.le, hu⟩, fun hx => let ⟨u, hu⟩ := exists_unit hx.2; ⟨u, hu ▸ hx.2, hu⟩⟩
      rw [this]
      exact (IsNonarchimedeanLocalField.isCompact_closedBall _ _).inter_right Metric.isClosed_sphere
    refine ((ck.prod ck).image cu).closure_of_subset ?_
    rintro _ ⟨n, rfl⟩
    exact ⟨(cmp t (l ^ n), cmp (t.comp σ) (l ^ n)), ⟨by simp [h1], by simp [h2]⟩, ext2 h (cmp_uI h _ _).1 (cmp_uI h _ _).2⟩

theorem idele_int (hσ : IsCMExt F E σ) [SecondCountableTopology (Fv F v)] [MeasurableSpace (Fv F v)] [BorelSpace (Fv F v)]
    {m : Measure (Fv F v)} (hm : IsVol m) {ψ : AddChar (Fv F v) ℂ} (hψ : IsPsi ψ) {ϖ : (Fv F v)ˣ} (hϖ : IsUnif ϖ) (χ : Chr F E)
    (hχ : ∀ x, chrW χ (t.comp σ) x = (chrW χ t x)⁻¹) {c : ℕ} (hν : CondLE ϖ (c + 1) (chrW χ t)) (hν' : ¬ CondLE ϖ c (chrW χ t))
    (μ : @Measure (idAt E (evFin F v)) (borel _)) (hμ : @Measure.IsHaarMeasure _ _ _ (borel _) μ)
    (h1 : μ {l | IsCompact (closure (Subgroup.zpowers l : Set (idAt E (evFin F v))))} = 1) (C : ℂ) (z : ℕ) :
    @integral _ _ _ _ (borel _) μ (fun l => dl (chrW χ t) (piW t (l.1 : AE F E)) * gI m ψ (chrW χ t) (piW (t.comp σ) (l.1 : AE F E)) * C *
      (χ l.1 : ℂ) * ((absE F E l.1 : ℝ) : ℂ) ^ z) = gI m ψ (chrW χ t) (((ϖ : Fv F v) ^ (c + 1))⁻¹) * (chrW χ t ϖ : ℂ) ^ (c + 1) *
        ((GlobalTheory.SplitWeil.resCard (Fv F v) : ℂ) ^ (c + 1)) ^ z * C := by
  obtain ⟨⟨sec, h⟩, -⟩ := section_statement F E σ hσ v t
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  letI : MeasurableSpace (idAt E (evFin F v)) := borel _
  haveI : BorelSpace (idAt E (evFin F v)) := ⟨rfl⟩
  rw [units_eq h] at h1
  set U := {l : idAt E (evFin F v) | valuation _ (cmp t l : Fv F v) = 1 ∧ valuation _ (cmp (t.comp σ) l : Fv F v) = 1} with hU
  have hc : ∀ s : E →ₐ[F] Fv F v, Continuous fun a : idAt E (evFin F v) => ‖(cmp s a : Fv F v)‖ := fun s =>
    ((cont_piW s).comp (Units.continuous_val.comp continuous_subtype_val)).norm
  have mU : MeasurableSet U := by
    simp only [hU, val_iff_norm]
    exact ((isClosed_eq (hc _) continuous_const).inter (isClosed_eq (hc _) continuous_const)).measurableSet
  rw [← integral_mul_left_eq_self _ (uI h 1 (ϖ ^ (c + 1))⁻¹)]
  have hn : GlobalTheory.SplitWeil.nabs _ (ϖ ^ (c + 1))⁻¹ = (GlobalTheory.SplitWeil.resCard (Fv F v) : ℝ) ^ (c + 1) := by
    rw [← norm_nabs, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, norm_inv, norm_pow,
      norm_nabs, GlobalTheory.GLDoubling.nabs_unif hϖ, inv_pow, inv_inv]
  rw [integral_congr_ae (g := U.indicator fun _ => gI m ψ (chrW χ t) (((ϖ : Fv F v) ^ (c + 1))⁻¹) * (chrW χ t ϖ : ℂ) ^ (c + 1) *
        ((GlobalTheory.SplitWeil.resCard (Fv F v) : ℂ) ^ (c + 1)) ^ z * C) (Filter.Eventually.of_forall fun l => ?_), integral_indicator mU]
  · simp [Measure.real, h1]
  beta_reduce
  rw [chr_id (t := t) hσ, abs_id (t := t) hσ, ← cmp_val, ← cmp_val, map_mul, map_mul, (cmp_uI h _ _).1, (cmp_uI h _ _).2, one_mul, hχ]
  by_cases hl : l ∈ U
  · rw [Set.indicator_of_mem hl, dl_unit _ hl.1, mul_comm (ϖ ^ (c + 1))⁻¹, Units.val_mul, gI_unit hm _ hl.2, GlobalTheory.SplitWeil.nabs_mul,
      nabs_of_valuation_eq_one hl.1, nabs_of_valuation_eq_one hl.2, hn]
    simp only [map_mul, map_inv, map_pow, _root_.mul_inv_rev, inv_inv, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
      one_mul, Complex.ofReal_pow, Complex.ofReal_natCast]
    field_simp
  · rw [Set.indicator_of_notMem hl]
    by_cases h2 : valuation _ (cmp t l : Fv F v) = 1
    · rw [gI_zero hm hψ hϖ hν hν' fun h3 => hl ⟨h2, ?_⟩]
      · simp
      · rwa [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, mul_right_comm,
          inv_mul_cancel₀ (pow_ne_zero _ ϖ.ne_zero), one_mul] at h3
    · simp [dl_of_ne h2]

end PositivityTheory.ThKG.Std
