import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.HgtCount
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModerateGrowthOfHasCompactSupport
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaHeisenbergTranslatesSeparate

noncomputable section

namespace GlobalTheory.ThK.Dbl.Hgt

open scoped NNReal ENNReal TensorProduct Pointwise
open NumberField IsDedekindDomain MeasureTheory Topology GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Doubling

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField F] in
theorem nnnorm_nat (w : InfinitePlace F) (m : ℕ) : ‖(m : w.Completion)‖₊ = m := NNReal.eq <| by
  have := (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) (m : w.Completion)
  rw [map_natCast, Complex.norm_natCast] at this
  exact this.symm

theorem exists_rho : ∃ ρ : (AF F)ˣ, (∀ w, ‖evInf F w ρ‖₊ = 2⁻¹) ∧ ∀ v, evFin F v ρ = 1 := by
  have e : algebraMap F (Ainf F) 2⁻¹ * algebraMap F (Ainf F) 2 = 1 := by rw [← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
  refine ⟨⟨((algebraMap F (Ainf F) 2⁻¹, 1) : Ainf F × Af F), ((algebraMap F (Ainf F) 2, 1) : Ainf F × Af F),
    Prod.ext e (mul_one _), Prod.ext ((mul_comm _ _).trans e) (mul_one _)⟩, fun w => ?_,
    fun v => map_one (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v)⟩
  change ‖GlobalTheory.AutFunCompare.evW w (algebraMap F (Ainf F) 2⁻¹)‖₊ = _
  rw [AlgHom.commutes, map_inv₀, map_ofNat, nnnorm_inv]
  exact congrArg _ (nnnorm_nat w 2)

theorem compact_bound {Ω : Set (AF F)} (hΩ : IsCompact Ω) : ∃ (c : ℕ) (R : ℝ≥0), 0 < c ∧
    ∀ a ∈ Ω, (∀ w, ‖evInf F w a‖₊ ≤ R) ∧ ∀ v, ‖(c : Fv F v) * evFin F v a‖ ≤ 1 := by
  choose R hR using fun w => (hΩ.image (f := fun a => ‖evInf F w a‖₊)
    (Continuous.nnnorm ((continuous_apply w).comp continuous_fst))).bddAbove
  let O : ℕ+ → Set (AF F) := fun c => {a | ∀ v, ‖((c : ℕ) : Fv F v) * evFin F v a‖ ≤ 1}
  have hO : ∀ c, IsOpen (O c) := fun c => by
    have := (RestrictedProduct.isOpen_forall_mem (R := fun v : Pl F => Fv F v) (A := fun v => v.adicCompletionIntegers F)
      fun v => Valued.isOpen_valuationSubring _).preimage
        (show Continuous fun a : AF F => ((c : ℕ) : Af F) * a.2 from continuous_const.mul continuous_snd)
    convert this using 1
    ext a
    refine forall_congr' fun v => ?_
    rw [← map_natCast (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v)]
    exact Valued.toNormedField.norm_le_one_iff
  have mono : ∀ c d : ℕ+, O c ⊆ O (c * d) := fun c d a ha v => by
    rw [PNat.mul_coe, Nat.cast_mul, mul_right_comm, norm_mul]
    exact mul_le_one₀ (ha v) (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)
  have cov : Ω ⊆ ⋃ c, O c := fun a _ => by
    obtain ⟨d, d0, -, hd⟩ := GlobalTheory.SmoothForms.denom_global (fun v => max 1 ‖evFin F v a‖₊) (fun _ => le_max_left _ _)
      ((Filter.eventually_cofinite.1 a.2.2).subset fun v hv h =>
        hv (max_eq_left (by exact_mod_cast Valued.toNormedField.norm_le_one_iff.2 h)))
    exact Set.mem_iUnion.2 ⟨⟨d, d0⟩, fun v => hd v _ (le_max_right _ _)⟩
  obtain ⟨c, hc⟩ := hΩ.elim_directed_cover O hO cov fun c d => ⟨c * d, mono c d, mul_comm d c ▸ mono d c⟩
  exact ⟨c, Finset.univ.sup R, c.2, fun a ha => ⟨fun w => (hR w ⟨a, ha, rfl⟩).trans (Finset.le_sup (Finset.mem_univ w)), hc ha⟩⟩

theorem scale_core {ρ : (AF F)ˣ} (r1 : ∀ w, ‖evInf F w ρ‖₊ = 2⁻¹) (r2 : ∀ v, evFin F v ρ = 1) (ν : (AF F)ˣ) {R : ℝ≥0} (hR : 1 ≤ R)
    (h1 : ∀ w, ‖evInf F w ν‖₊ ≤ R) (h2 : ∀ v, ‖evFin F v ν‖₊ ≤ 1) (hf : (Function.mulSupport fun v => ‖evFin F v ν‖₊).Finite) {i : ℕ}
    (h : R ^ Fintype.card (InfinitePlace F) ≤ 2 ^ i * ((∏ w, ‖evInf F w ν‖₊) * ∏ᶠ v, ‖evFin F v ν‖₊)) :
    ∃ m : ℕ, 0 < m ∧ m ≤ 2 ^ i ∧ (∀ w, ‖evInf F w (m * ρ.1 ^ (2 * i) * (ν⁻¹).1)‖ ≤ 1) ∧
      ∀ v, ‖evFin F v (m * ρ.1 ^ (2 * i) * (ν⁻¹).1)‖ ≤ 1 := by
  classical
  set D := R ^ Fintype.card (InfinitePlace F) with hD
  have D0 : 0 < D := by positivity
  have hP : ∏ w, ‖evInf F w ν‖₊ ≤ D := Finset.prod_le_pow_card _ _ _ fun w _ => h1 w
  have hQ : ∏ᶠ v, ‖evFin F v ν‖₊ ≤ 1 := finprod_induction (· ≤ 1) le_rfl (fun _ _ => mul_le_one') h2
  have n0 : ∀ v, 0 < ‖evFin F v ν‖₊ := fun v => nnnorm_pos.2 (ν.isUnit.map _).ne_zero
  obtain ⟨m, m0, hm, hv⟩ := GlobalTheory.SmoothForms.denom_global (fun v => ‖evFin F v ν‖₊⁻¹) (fun v => (one_le_inv₀ (n0 v)).2 (h2 v))
    (by rwa [Function.mulSupport_fun_inv])
  have a1 : 1 ≤ 2 ^ i * ∏ᶠ v, ‖evFin F v ν‖₊ := le_of_mul_le_mul_left
    ((mul_one D).trans_le (h.trans ((mul_le_mul_right (mul_le_mul_left hP _) _).trans_eq (mul_left_comm _ _ _)))) D0
  have hm' : (m : ℝ≥0) ≤ 2 ^ i := by
    rw [finprod_inv_distrib] at hm
    exact hm.trans (inv_le_of_inv_le₀ (by positivity) ((inv_le_iff_one_le_mul₀' (by positivity)).2 a1))
  refine ⟨m, m0, by exact_mod_cast hm', fun w => ?_, fun v => ?_⟩
  · have a2 : ∏ w, ‖evInf F w ν‖₊ ≤ ‖evInf F w ν‖₊ * D := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w)]
      exact mul_le_mul_right ((Finset.prod_le_pow_card _ _ _ fun w _ => h1 w).trans
        (pow_le_pow_right₀ hR (Finset.card_le_univ _))) _
    have a3 : 1 ≤ 2 ^ i * ‖evInf F w ν‖₊ := le_of_mul_le_mul_left
      ((mul_one D).trans_le (h.trans ((mul_le_mul_right (mul_le_mul' a2 hQ) _).trans_eq (by ring)))) D0
    have a4 : ‖evInf F w ν‖₊⁻¹ ≤ 2 ^ i := (inv_le_iff_one_le_mul₀ (nnnorm_pos.2 (ν.isUnit.map _).ne_zero)).2 a3
    rw [← coe_nnnorm, NNReal.coe_le_one]
    rw [map_mul, map_mul, map_pow, map_natCast, map_units_inv, nnnorm_mul, nnnorm_mul, nnnorm_pow, nnnorm_inv, nnnorm_nat, r1]
    refine (mul_le_mul' (mul_le_mul_left hm' _) a4).trans_eq ?_
    rw [inv_pow, two_mul, pow_add]; field_simp
  · rw [map_mul, map_mul, map_pow, map_natCast, map_units_inv, r2, one_pow, mul_one]
    exact hv v _ (nnnorm_inv _).le

theorem scale_ad (hF : IsTotallyReal F) {ρ : (AF F)ˣ} (r1 : ∀ w, ‖evInf F w ρ‖₊ = 2⁻¹) (r2 : ∀ v, evFin F v ρ = 1) {Ω : Set (AF F)}
    (hΩ : IsCompact Ω) : ∃ (i₀ : ℕ) (C : Set (AF F)), IsCompact C ∧ (∀ i m : ℕ, m ≤ 2 ^ i → m * ρ.1 ^ (2 * i) ∈ C) ∧
      ∀ u : (AE F E)ˣ, Algebra.norm (AF F) u.1 ∈ Ω → absE F E u ≤ 2 ^ i₀ ∧ ∀ j : ℕ, (1 / 2 : ℝ) ^ j ≤ absE F E u →
        ∃ m : ℕ, 0 < m ∧ m ≤ 2 ^ (j + i₀) ∧ ∃ x ∈ C, m * ρ.1 ^ (2 * (j + i₀)) = x * Algebra.norm (AF F) u.1 := by
  obtain ⟨c, R₀, c0, hc⟩ := compact_bound hΩ
  obtain ⟨k, hk⟩ : ∃ k, Module.finrank F E = k + 1 := Nat.exists_eq_succ_of_ne_zero Module.finrank_pos.ne'
  obtain ⟨c', R, -, hR⟩ := compact_bound (hΩ.image (continuous_const_mul ((c : AF F) ^ (k + 1))))
  obtain ⟨C, hC, hC'⟩ := HeightProper.exists_compact_adeles (F := F) (fun _ => 1) 1
  have mem : ∀ a : AF F, (∀ w, ‖evInf F w a‖ ≤ 1) → (∀ v, ‖evFin F v a‖ ≤ 1) → a ∈ C := fun a h1 h2 =>
    hC' a h1 1 one_pos (by simp) (by simpa using h2)
  obtain ⟨i₀, hi⟩ := pow_unbounded_of_one_lt (max 1 R ^ Fintype.card (InfinitePlace F)) (one_lt_two (α := ℝ≥0))
  refine ⟨i₀, C ∪ (· * (c : AF F) ^ (k + 1)) '' C, hC.union (hC.image (continuous_mul_const _)), fun i m hm => .inl (mem _
    (fun w => ?_) fun v => ?_), fun u hu => ?_⟩
  · rw [← coe_nnnorm, NNReal.coe_le_one]
    rw [map_mul, map_pow, map_natCast, nnnorm_mul, nnnorm_pow, nnnorm_nat, r1, inv_pow, mul_inv_le_iff₀ (by positivity), one_mul]
    exact_mod_cast hm.trans (Nat.pow_le_pow_right two_pos (by omega))
  · rw [map_mul, map_pow, map_natCast, r2, one_pow, mul_one]
    exact IsUltrametricDist.norm_natCast_le_one _ _
  set u' := Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 (c : E) (Nat.cast_ne_zero.2 c0.ne')) * u with hu'
  have e1 : absE F E u = absE F E u' := by rw [hu', map_mul, absE_inclR, one_mul]
  set ν : (AF F)ˣ := Units.map (Algebra.norm (AF F)) u'
  have e2 : ν.1 = (c : AF F) ^ (k + 1) * Algebra.norm (AF F) u.1 := by
    change Algebra.norm (AF F) (inclR (F := F) (AF F) (c : E) * u.1) = _
    rw [map_mul, norm_inclR, ← map_natCast (algebraMap F E), Algebra.norm_algebraMap, hk, map_pow, map_natCast]
  have e3 : absE F E u' = (∏ w, ‖evInf F w ν‖₊) * ∏ᶠ v, ‖evFin F v ν‖₊ := by
    simp only [absE_apply, absEv_unitFin, absEw_unitInf, IsTotallyReal.mult_eq, pow_one]; rfl
  have h1 : ∀ w, ‖evInf F w ν‖₊ ≤ max 1 R := fun w => ((hR _ ⟨_, hu, e2.symm⟩).1 w).trans (le_max_right _ _)
  have h2 : ∀ v, ‖evFin F v ν‖₊ ≤ 1 := fun v => by
    rw [← NNReal.coe_le_one, coe_nnnorm]
    rw [e2, map_mul, map_pow, map_natCast, pow_succ, mul_assoc, norm_mul, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)) (norm_nonneg _) ((hc _ hu).2 v)
  refine ⟨?_, fun j hj => ?_⟩
  · rw [e1, e3]
    exact (mul_le_of_le_one_right' (finprod_induction (· ≤ 1) le_rfl (fun _ _ => mul_le_one') h2)).trans
      ((Finset.prod_le_pow_card _ _ _ fun w _ => h1 w).trans hi.le)
  · obtain ⟨m, m0, m1, m2, m3⟩ := scale_core r1 r2 ν (le_max_left _ _) h1 h2
      (by have := finite_mulSupport_absEv u'; simp only [absEv_unitFin] at this; exact this) (i := j + i₀) (by
        rw [← e3, ← e1, pow_add, mul_right_comm]
        refine hi.le.trans (le_mul_of_one_le_left' ?_)
        rw [one_div, inv_pow, inv_le_iff_one_le_mul₀' (by positivity)] at hj
        exact_mod_cast hj)
    exact ⟨m, m0, m1, _, .inr ⟨_, mem _ m2 m3, rfl⟩, by
      beta_reduce
      rw [mul_assoc _ _ (Algebra.norm _ _), ← e2, Units.inv_mul_cancel_right]⟩

theorem count_ad (hF : IsTotallyReal F) {B κ : Type} [Ring B] [Algebra (AF F) B] [TopologicalSpace B] [IsTopologicalRing B] [T2Space B]
    [ContinuousSMul (AF F) B] [Fintype κ] (c : B ≃ₗ[AF F] (κ → AF F)) (hc : Continuous c) (hc' : Continuous c.symm)
    (H : Subgroup Bˣ) (hH : IsClosed (H : Set Bˣ)) {Ω : Set B} (hΩ : IsCompact Ω) {Ω₀ : Set (AF F)} (h₀ : IsCompact Ω₀)
    [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsHaarMeasure] :
    ∃ (R : ℝ≥0) (C : ℝ≥0∞) (b : ℝ≥0), 1 ≤ R ∧ C ≠ ⊤ ∧ (∀ u : (AE F E)ˣ, Algebra.norm (AF F) u.1 ∈ Ω₀ → absE F E u ≤ R) ∧ ∀ j : ℕ,
      μ {g | ∃ u : (AE F E)ˣ, Algebra.norm (AF F) u.1 ∈ Ω₀ ∧ (1 / 2 : ℝ) ^ j ≤ absE F E u ∧
        Algebra.norm (AF F) u.1 • g.1.1 ∈ Ω ∧ Algebra.norm (AF F) u.1 • (g⁻¹).1.1 ∈ Ω} ≤ C * b ^ j := by
  have := t2Space_adeleRing' (F := F)
  obtain ⟨ρ, r1, r2⟩ := exists_rho (F := F)
  obtain ⟨i₀, C, hC, c1, c2⟩ := scale_ad (E := E) hF r1 r2 h₀
  obtain ⟨V, hV, hV0⟩ := exists_compact_mem_nhds (0 : AF F)
  obtain ⟨X, U, hX, hU, hcount⟩ := count_grp c hc hc' H hH (hC.smul_set hΩ) (hV.add hV.neg)
  have : BorelSpace (AF F) := ⟨rfl⟩
  let ν : Measure (AF F) := Measure.addHaar
  have : ν.Regular := Measure.regular_of_isAddLeftInvariant hV ⟨0, mem_interior_iff_mem_nhds.2 hV0⟩ hV.measure_lt_top.ne
  have v0 : ν V ≠ 0 := (Measure.measure_pos_of_mem_nhds ν hV0).ne'
  have hZ := (hX.add ((hC.mul hC).mul hV)).measure_lt_top (μ := ν)
  set Z := X + C * C * V
  set δ := distribHaarChar (AF F) ρ⁻¹
  set A := ν Z / ν V
  have hA : A ≠ ⊤ := ENNReal.div_ne_top hZ.ne v0
  set q := Fintype.card κ
  have key : ∀ i m : ℕ, 0 < m → m ≤ 2 ^ i → μ {g | ((m : AF F) * ρ.1 ^ (2 * i)) • g.1.1 ∈ C • Ω ∧
      ((m : AF F) * ρ.1 ^ (2 * i)) • (g⁻¹).1.1 ∈ C • Ω} ≤ (A * (δ ^ 4) ^ i) ^ q * μ U := fun i m m0 hm => by
    let l : (AF F)ˣ := Units.map (algebraMap F (AF F) : F →* AF F) (Units.mk0 (m : F) (Nat.cast_ne_zero.2 m0.ne')) * ρ ^ (2 * i)
    have el : l.1 = m * ρ.1 ^ (2 * i) := by simp [l]
    have dl : distribHaarChar (AF F) (l * l) * (δ ^ 4) ^ i = 1 := by
      have p := GlobalTheory.CompanionTheory.AdeleModule.distribHaarChar_principal F (Units.mk0 (m : F) (Nat.cast_ne_zero.2 m0.ne'))
      simp only [l, δ, map_mul]
      rw [p, one_mul]
      rw [← map_pow, ← map_pow, ← map_mul, ← map_mul, ← map_one (distribHaarChar (G := (AF F)ˣ) (AF F))]
      congr 1; group
    have ev := distribHaarChar_mul ν (l * l) V
    obtain ⟨s, hs, hs'⟩ := exists_cover ν (X := X) (V := (l * l) • V) (Z := Z) (hV.smul _).measurableSet
      (ev ▸ mul_ne_zero (ENNReal.coe_ne_zero.2 (distribHaarChar_pos (g := l * l)).ne') v0) hZ.ne (by
        rintro x hx _ ⟨v, hv, rfl⟩
        exact Set.add_mem_add hx (Set.mul_mem_mul (Set.mul_mem_mul (el ▸ c1 i m hm) (el ▸ c1 i m hm)) hv))
    rw [← el]
    refine (hcount l s (fun x hx => ?_) μ).trans (mul_le_mul_left (pow_le_pow_left' ?_ _) _)
    · obtain ⟨y, hy, _, ⟨v, hv, rfl⟩, _, ⟨v', hv', rfl⟩, e⟩ := hs' x hx
      exact ⟨y, hy, v + -v', Set.add_mem_add hv (Set.neg_mem_neg.2 hv'), e.trans (by rw [← sub_eq_add_neg, mul_sub]; rfl)⟩
    · have : (s.card : ℝ≥0∞) * distribHaarChar (AF F) (l * l) ≤ A := by
        rw [ENNReal.le_div_iff_mul_le (.inl v0) (.inl hV.measure_lt_top.ne), mul_assoc, ev]; exact hs
      refine le_of_eq_of_le ?_ (mul_le_mul_left this _)
      rw [mul_assoc]
      norm_cast
      rw [dl, mul_one]
  refine ⟨2 ^ i₀, A ^ q * μ U * (2 * (δ ^ 4) ^ q : ℝ≥0) ^ i₀, 2 * (δ ^ 4) ^ q, one_le_pow₀ one_le_two,
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top hA) hU.measure_lt_top.ne) (ENNReal.pow_ne_top ENNReal.coe_ne_top),
    fun u hu => (c2 u hu).1, fun j => ?_⟩
  refine (measure_mono (t := ⋃ m ∈ Finset.Icc 1 (2 ^ (j + i₀)), _) ?_).trans ((measure_biUnion_finset_le _ _).trans
    ((Finset.sum_le_card_nsmul _ _ _ fun m hm => key (j + i₀) m (Finset.mem_Icc.1 hm).1 (Finset.mem_Icc.1 hm).2).trans_eq ?_))
  · rintro g ⟨u, h1, h2, h3, h4⟩
    obtain ⟨m, m0, m1, x, hx, e⟩ := (c2 u h1).2 j h2
    refine Set.mem_iUnion₂.2 ⟨m, Finset.mem_Icc.2 ⟨m0, m1⟩, ?_⟩
    rw [Set.mem_ofPred_eq, e, mul_smul, mul_smul]
    exact ⟨Set.smul_mem_smul hx h3, Set.smul_mem_smul hx h4⟩
  · simp only [Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul]
    push_cast
    ring

end GlobalTheory.ThK.Dbl.Hgt

end
