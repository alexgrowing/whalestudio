import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset

open MeasureTheory Set GlobalTheory.AdelicU GlobalTheory.OpTrace NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open scoped ENNReal NNReal Topology ComplexConjugate ContDiff InnerProductSpace Matrix

noncomputable section

namespace GlobalTheory.Orb

section Operators

variable {H H' V W : Type} [Group H] [Group H'] [MeasurableSpace H] [MeasurableSpace H']
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]

theorem repOp_congr {π : H →* (V →L[ℂ] V)} {π' : H' →* (V →L[ℂ] V)} {μ : Measure H} {μ' : Measure H'} {f : H → ℂ}
    {f' : H' → ℂ} (h : ∀ T, IsRepOp π μ f T ↔ IsRepOp π' μ' f' T) : repOp π μ f = repOp π' μ' f' := by
  by_cases hT : ∃ T, IsRepOp π μ f T
  · obtain ⟨T, hT⟩ := hT
    rw [hT.repOp_eq, ((h T).1 hT).repOp_eq]
  · rw [repOp, repOp, dif_neg hT, dif_neg fun ⟨T, h'⟩ => hT ⟨T, (h T).2 h'⟩]

theorem repOp_smul_measure (π : H →* (V →L[ℂ] V)) (μ : Measure H) (f : H → ℂ) {c : ℝ≥0} (hc : c ≠ 0) :
    repOp π (c • μ) f = repOp π μ ((c : ℂ) • f) := by
  refine repOp_congr fun T => forall_congr' fun v => ?_
  simp only [Pi.smul_apply, smul_assoc]
  refine and_congr ?_ ?_
  · rw [show c • μ = (c : ℝ≥0∞) • μ from rfl, integrable_smul_measure (by simpa using hc) ENNReal.coe_ne_top]
    exact (integrable_fun_smul_iff (by simpa using hc) _).symm
  · rw [integral_smul_nnreal_measure, integral_smul, NNReal.smul_def, Complex.coe_smul]

theorem IsUnitEquiv.symm {π : H →* (V →L[ℂ] V)} {π' : H →* (W →L[ℂ] W)} (h : IsUnitEquiv π π') :
    IsUnitEquiv π' π := by
  obtain ⟨A, hA⟩ := h
  exact ⟨A.symm, fun g v => A.injective (by simp [hA])⟩

theorem IsUnitEquiv.trans {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] {π : H →* (V →L[ℂ] V)}
    {π' : H →* (W →L[ℂ] W)} {π'' : H →* (U →L[ℂ] U)} (h : IsUnitEquiv π π') (h' : IsUnitEquiv π' π'') :
    IsUnitEquiv π π'' := by
  obtain ⟨A, hA⟩ := h
  obtain ⟨B, hB⟩ := h'
  exact ⟨A.trans B, fun g v => by simp [hA, hB]⟩

variable [CompleteSpace V] [CompleteSpace W]

theorem isRepOp_conj {π : H →* (V →L[ℂ] V)} {π' : H →* (W →L[ℂ] W)} (A : V ≃ₗᵢ[ℂ] W)
    (hA : ∀ g v, A (π g v) = π' g (A v)) {μ : Measure H} {f : H → ℂ} {T : V →L[ℂ] V} (h : IsRepOp π μ f T) :
    IsRepOp π' μ f ((A.toContinuousLinearEquiv : V →L[ℂ] W) ∘L T ∘L
      (A.toContinuousLinearEquiv.symm : W →L[ℂ] V)) := fun w => by
  obtain ⟨h1, h2⟩ := h (A.symm w)
  have e : ∀ g, f g • π' g w = (A.toContinuousLinearEquiv : V →L[ℂ] W) (f g • π g (A.symm w)) := fun g => by
    simp [hA]
  simp only [e]
  refine ⟨ContinuousLinearMap.integrable_comp _ h1, ?_⟩
  rw [ContinuousLinearMap.integral_comp_comm _ h1, ← h2]
  rfl

theorem IsUnitEquiv.hasTrace {π : H →* (V →L[ℂ] V)} {π' : H →* (W →L[ℂ] W)} (h : IsUnitEquiv π π') {μ : Measure H}
    {f : H → ℂ} {c : ℂ} (ht : HasTrace (repOp π μ f) c) : HasTrace (repOp π' μ f) c := by
  by_cases hT : ∃ T, IsRepOp π μ f T
  · obtain ⟨T, hT⟩ := hT
    obtain ⟨A, hA⟩ := h
    rw [hT.repOp_eq] at ht
    rw [(isRepOp_conj A hA hT).repOp_eq]
    exact ⟨ht.1.comp_comp _ _, (ht.1.trace_conj _).trans ht.2⟩
  · obtain ⟨A, hA⟩ := h.symm
    rw [repOp, dif_neg hT] at ht
    rw [repOp, dif_neg fun ⟨T, h'⟩ => hT ⟨_, isRepOp_conj A hA h'⟩]
    exact ⟨isTraceClass_zero, trace_zero.trans (trace_zero.symm.trans ht.2)⟩

end Operators

section Transport

variable {H H' n V W : Type} [Group H] [Group H'] [TopologicalSpace H] [TopologicalSpace H'] [Fintype n]
  [DecidableEq n] [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (e : H ≃ₜ* H') {ι : H →* Matrix n n ℂ} {ι' : H' →* Matrix n n ℂ} {a : Matrix n n ℂ}

theorem IsBiFinite.comp {K' : Subgroup H'} {f' : H' → ℂ} (h : IsBiFinite K' f') :
    IsBiFinite (K'.comap (e : H →* H')) (f' ∘ e) := by
  haveI : FiniteDimensional ℂ _ := h
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.map (LinearMap.funLeft ℂ ℂ e)
    (Submodule.span ℂ {φ : H' → ℂ | ∃ k ∈ K', ∃ k' ∈ K', φ = fun g => f' (k * g * k')})) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, hk, k', hk', rfl⟩
  exact ⟨_, Submodule.subset_span ⟨e k, hk, e k', hk', rfl⟩, funext fun g => by simp [LinearMap.funLeft]⟩

variable {e}

theorem conj_symm (ha : IsUnit a) (hι : ∀ g, ι' (e g) = a * ι g * a⁻¹) (g : H') :
    ι (e.symm g) = a⁻¹ * ι' g * a⁻¹⁻¹ := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 ha
  obtain ⟨g, rfl⟩ := e.surjective g
  rw [hι, e.symm_apply_apply, Matrix.nonsing_inv_nonsing_inv _ hd]
  simp only [mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.nonsing_inv_mul_cancel_left _ _ hd, mul_one]

theorem comp_mem_ccMat (hι : ∀ g, ι' (e g) = a * ι g * a⁻¹) {f' : H' → ℂ} (h : f' ∈ CcMat ι') :
    f' ∘ e ∈ CcMat ι := by
  obtain ⟨hc, Φ, hΦ, hf⟩ := h
  refine ⟨hc.comp_homeomorph e.toHomeomorph, Φ ∘ fun y i j => ∑ l, (∑ k, a i k * y k l) * a⁻¹ l j,
    hΦ.comp (by fun_prop), fun g => (hf _).trans (congrArg Φ ?_)⟩
  funext i j
  simp only [matCoord, hι, Matrix.mul_apply]

theorem isRegSS_conj_iff (ha : IsUnit a) (hι : ∀ g, ι' (e g) = a * ι g * a⁻¹) (s : H) :
    IsRegSS (ι' (e s)) ↔ IsRegSS (ι s) := by
  rw [IsRegSS, IsRegSS, hι, Matrix.charpoly_mul_comm,
    Matrix.nonsing_inv_mul_cancel_left _ _ ((Matrix.isUnit_iff_isUnit_det _).1 ha)]

variable (e) in

theorem isCompact_cent_iff (s : H) : IsCompact (cent (e s) : Set H') ↔ IsCompact (cent s : Set H) := by
  rw [isCompact_iff_compactSpace, isCompact_iff_compactSpace]
  exact ⟨fun _ => (centEquiv e s rfl).toHomeomorph.symm.compactSpace,
    fun _ => (centEquiv e s rfl).toHomeomorph.compactSpace⟩

variable [MeasurableSpace H] [BorelSpace H] [MeasurableSpace H'] [BorelSpace H'] (e)

theorem measurableEmbedding_equiv : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding

theorem map_symm_map (μ' : Measure H') : (μ'.map e.symm).map e = μ' := by
  rw [Measure.map_map (map_continuous e).measurable (map_continuous e.symm).measurable]
  convert Measure.map_id using 2
  ext x; simp

theorem repOp_map (π' : H' →* (V →L[ℂ] V)) (μ : Measure H) (f' : H' → ℂ) :
    repOp π' (μ.map e) f' = repOp (π'.comp (e : H →* H')) μ (f' ∘ e) :=
  repOp_congr fun T => forall_congr' fun v => and_congr (measurableEmbedding_equiv e).integrable_map_iff
    (by rw [(measurableEmbedding_equiv e).integral_map]; rfl)

theorem isTempered_map_iff (π' : H' →* (V →L[ℂ] V)) (μ : Measure H) :
    IsTempered (μ.map e) π' ↔ IsTempered μ (π'.comp (e : H →* H')) :=
  exists_congr fun _ => and_congr_right fun _ => forall₂_congr fun _ _ =>
    (measurableEmbedding_equiv e).integrable_map_iff

variable {e} [CompleteSpace V]

theorem IsCharFn.of_map (ha : IsUnit a) (hι : ∀ g, ι' (e g) = a * ι g * a⁻¹) {μ : Measure H}
    {π' : H' →* (V →L[ℂ] V)} {Θ : H' → ℂ} (h : IsCharFn ι' (μ.map e) π' Θ) :
    IsCharFn ι μ (π'.comp (e : H →* H')) (Θ ∘ e) := by
  refine ⟨(locallyIntegrable_map_homeomorph e.toHomeomorph).1 h.1, fun s hs =>
    ContinuousAt.comp (h.2.1 _ ((isRegSS_conj_iff ha hι s).2 hs)) (map_continuous e).continuousAt, fun f hf => ?_⟩
  have := h.2.2 _ (comp_mem_ccMat (conj_symm ha hι) hf)
  rw [repOp_map, (measurableEmbedding_equiv e).integral_map] at this
  convert this using 2 <;> ext x <;> simp

variable [IsTopologicalGroup H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H]
  [IsTopologicalGroup H'] [SecondCountableTopology H'] [LocallyCompactSpace H'] [T2Space H']

theorem IsPseudoCoeff.of_map (ha : IsUnit a) (hι : ∀ g, ι' (e g) = a * ι g * a⁻¹) {μ : Measure H} [μ.IsHaarMeasure]
    {D' : H' →* (V →L[ℂ] V)} {f' : H' → ℂ} (h : IsPseudoCoeff ι' (μ.map e) D' f') :
    IsPseudoCoeff ι μ (D'.comp (e : H →* H')) (f' ∘ e) := by
  obtain ⟨Θ, hΘ, hO⟩ := h.orb_compact
  refine ⟨comp_mem_ccMat hι h.mem, repOp_map e D' μ f' ▸ h.trace_self, fun U _ _ _ π h1 h2 h3 h4 => ?_,
    fun s hs hT dt _ _ => ?_, Θ ∘ e, hΘ.of_map ha hι, fun s hs hT dt _ _ => ?_⟩
  · obtain ⟨π', rfl⟩ : ∃ π' : H' →* (U →L[ℂ] U), π = π'.comp (e : H →* H') :=
      ⟨π.comp (e.symm : H' →* H), MonoidHom.ext fun x => by simp⟩
    rw [← repOp_map]
    refine h.trace_other U π' ⟨fun g v => ?_, fun v => ?_⟩ ⟨h2.1, fun S hS => h2.2 S ⟨hS.1, fun g => hS.2 _⟩⟩
      ((isTempered_map_iff e π' μ).2 h3) fun ⟨A, hA⟩ => h4 ⟨A, fun g => hA _⟩
    · simpa using h1.1 (e.symm g) v
    · simpa [Function.comp_def] using (h1.2 v).comp (map_continuous e.symm)
  · exact (hasOrbInt_map e rfl f' _).1.1 (h.orb_noncompact _ ((isRegSS_conj_iff ha hι s).2 hs)
      (mt (isCompact_cent_iff e s).1 hT) _)
  · have := hO _ ((isRegSS_conj_iff ha hι s).2 hs) ((isCompact_cent_iff e s).2 hT) (dt.map (centEquiv e s rfl))
    rw [map_measureReal_apply (map_continuous _).measurable MeasurableSet.univ, preimage_univ] at this
    exact (hasOrbInt_map e rfl f' _).1.1 this

theorem IsPseudoCoeff.comp (ha : IsUnit a) (hι : ∀ g, ι' (e g) = a * ι g * a⁻¹) {μ' : Measure H'} [μ'.IsHaarMeasure]
    {D' : H' →* (V →L[ℂ] V)} {f' : H' → ℂ} (h : IsPseudoCoeff ι' μ' D' f') :
    IsPseudoCoeff ι (μ'.map e.symm) (D'.comp (e : H →* H')) (f' ∘ e) :=
  IsPseudoCoeff.of_map ha hι (by rwa [map_symm_map])

theorem isPseudoCoeff_map_iff (ha : IsUnit a) (hι : ∀ g, ι' (e g) = a * ι g * a⁻¹) {μ : Measure H} [μ.IsHaarMeasure]
    {D' : H' →* (V →L[ℂ] V)} {f' : H' → ℂ} :
    IsPseudoCoeff ι' (μ.map e) D' f' ↔ IsPseudoCoeff ι μ (D'.comp (e : H →* H')) (f' ∘ e) := by
  refine ⟨IsPseudoCoeff.of_map ha hι, fun h => ?_⟩
  convert h.comp (e := e.symm) (Matrix.isUnit_nonsing_inv_iff.2 ha) (conj_symm ha hι) using 1
  · rfl
  · exact MonoidHom.ext fun x => by simp
  · ext x; simp

end Transport

section Scaling

variable {H n V W : Type} [Group H] [TopologicalSpace H] [Fintype n] [DecidableEq n] [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [MeasurableSpace H]
  {ι : H →* Matrix n n ℂ} {μ : Measure H} {c : ℝ≥0}

omit [TopologicalSpace H] in

theorem isTempered_smul_iff (hc : c ≠ 0) {π : H →* (V →L[ℂ] V)} : IsTempered (c • μ) π ↔ IsTempered μ π :=
  exists_congr fun _ => and_congr_right fun _ => forall₂_congr fun _ _ =>
    integrable_smul_measure (c := c) (by simpa using hc) ENNReal.coe_ne_top

variable [CompleteSpace V] [CompleteSpace W]

theorem IsCharFn.smul_measure (hc : c ≠ 0) {π : H →* (V →L[ℂ] V)} {Θ : H → ℂ} (h : IsCharFn ι μ π Θ) :
    IsCharFn ι (c • μ) π Θ := by
  refine ⟨fun x => ?_, h.2.1, fun f hf => ?_⟩
  · obtain ⟨s, hs, hi⟩ := h.1 x
    refine ⟨s, hs, ?_⟩
    rw [IntegrableOn, Measure.restrict_smul]
    exact hi.smul_measure_nnreal
  · have := h.2.2 _ ((CcMat ι).smul_mem (c : ℂ) hf)
    rw [repOp_smul_measure _ _ _ hc, integral_smul_nnreal_measure]
    simpa [mul_assoc, integral_const_mul, NNReal.smul_def] using this

theorem IsCharFn.of_isUnitEquiv {π : H →* (V →L[ℂ] V)} {π' : H →* (W →L[ℂ] W)} (hπ : IsUnitEquiv π π') {Θ : H → ℂ}
    (h : IsCharFn ι μ π Θ) : IsCharFn ι μ π' Θ := ⟨h.1, h.2.1, fun f hf => hπ.hasTrace (h.2.2 f hf)⟩

theorem IsPseudoCoeff.of_isUnitEquiv {D : H →* (V →L[ℂ] V)} {D' : H →* (W →L[ℂ] W)} (hD : IsUnitEquiv D D')
    {f : H → ℂ} (h : IsPseudoCoeff ι μ D f) : IsPseudoCoeff ι μ D' f := by
  obtain ⟨Θ, hΘ, hO⟩ := h.orb_compact
  exact ⟨h.mem, hD.hasTrace h.trace_self,
    fun U _ _ _ π h1 h2 h3 h4 => h.trace_other U π h1 h2 h3 fun h5 => h4 (h5.trans hD), h.orb_noncompact,
    Θ, hΘ.of_isUnitEquiv hD, hO⟩

variable [BorelSpace H] [IsTopologicalGroup H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H]
  [μ.IsHaarMeasure]

theorem HasOrbInt.smul_measure {γ : H} {dt : Measure (cent γ)} [dt.IsHaarMeasure] [dt.IsMulRightInvariant]
    {f : H → ℂ} {x : ℂ} (h : HasOrbInt μ γ dt f x) (c : ℝ≥0) : HasOrbInt (c • μ) γ dt f (c * x) := by
  refine ⟨?_, (orbInt_smul_left c).trans (congrArg _ h.2)⟩
  rw [show c • μ = (c : ℝ≥0∞) • μ from rfl, quotMeas_smul_left (isClosed_cent γ)]
  exact h.1.smul_measure ENNReal.coe_ne_top

theorem IsPseudoCoeff.smul_measure (hc : c ≠ 0) {D : H →* (V →L[ℂ] V)} {f : H → ℂ} (h : IsPseudoCoeff ι μ D f) :
    IsPseudoCoeff ι (c • μ) D ((c : ℂ)⁻¹ • f) := by
  have hc' : (c : ℂ) ≠ 0 := by simpa using hc
  obtain ⟨Θ, hΘ, hO⟩ := h.orb_compact
  refine ⟨(CcMat ι).smul_mem _ h.mem, ?_, fun U _ _ _ π h1 h2 h3 h4 => ?_, fun s hs hT dt _ _ => ?_,
    Θ, hΘ.smul_measure hc, fun s hs hT dt _ _ => ?_⟩
  · rw [repOp_smul_measure _ _ _ hc, smul_inv_smul₀ hc']
    exact h.trace_self
  · rw [repOp_smul_measure _ _ _ hc, smul_inv_smul₀ hc']
    exact h.trace_other U π h1 h2 ((isTempered_smul_iff hc).1 h3) h4
  · simpa using ((h.orb_noncompact s hs hT dt).smul (c : ℂ)⁻¹).smul_measure c
  · simpa only [mul_inv_cancel_left₀ hc'] using ((hO s hs hT dt).smul (c : ℂ)⁻¹).smul_measure c

theorem IsPseudoCoeff.exists_smul {D : H →* (V →L[ℂ] V)} {f : H → ℂ} (h : IsPseudoCoeff ι μ D f) (ν : Measure H)
    [ν.IsHaarMeasure] : ∃ c : ℝ≥0, c ≠ 0 ∧ IsPseudoCoeff ι ν D ((c : ℂ)⁻¹ • f) := by
  have hc := (Measure.haarScalarFactor_pos_of_isHaarMeasure ν μ).ne'
  refine ⟨_, hc, ?_⟩
  have := h.smul_measure hc
  rwa [← Measure.isMulLeftInvariant_eq_smul ν μ] at this

end Scaling

section Record

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)

theorem exists_frameMat_eq (ρ : D.what₂.Tau) {x : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hx : x ∈ UJset (M.ε ρ)) :
    ∃ g, frameMat M ρ g = x := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit ρ)
  have e : M.fr ρ * ((M.fr ρ)⁻¹ * x * M.fr ρ) * (M.fr ρ)⁻¹ = x := by
    rw [← mul_assoc, ← mul_assoc, Matrix.mul_nonsing_inv _ hd, one_mul, mul_assoc, Matrix.mul_nonsing_inv _ hd, mul_one]
  obtain ⟨g, hg⟩ := exists_archEquiv_eq V (embOverOf D ρ) rfl ((conj_mem_UJset_iff M ρ _).1 (e.symm ▸ hx))
  exact ⟨g, (congrArg (M.fr ρ * · * (M.fr ρ)⁻¹) hg).trans e⟩

theorem isEmbedding_frameMat (ρ : D.what₂.Tau) : Topology.IsEmbedding (frameMat M ρ) := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit ρ)
  have h : Topology.IsEmbedding fun x : Matrix (Fin V.rank) (Fin V.rank) ℂ => M.fr ρ * x * (M.fr ρ)⁻¹ :=
    Function.LeftInverse.isEmbedding (f := fun x => (M.fr ρ)⁻¹ * x * M.fr ρ) (fun x => by
      simp only [mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.nonsing_inv_mul_cancel_left _ _ hd, mul_one])
      ((continuous_const.mul continuous_id).mul continuous_const)
      ((continuous_const.mul continuous_id).mul continuous_const)
  exact h.comp (isEmbedding_archMat V.gram (isCMExt_host D) (embOverOf D ρ))

def frameHom (ρ : D.what₂.Tau) : GArch D.sp.cm.sig V.gram (placeOf D ρ) →* Formalism.REAL.UJ (M.ε ρ) :=
  (frameMat M ρ).toHomUnits.codRestrict _ (frameMat_mem M ρ)

theorem frameHom_bijective (ρ : D.what₂.Tau) : Function.Bijective (frameHom M ρ) :=
  ⟨fun _ _ h => (isEmbedding_frameMat M ρ).injective (congrArg (ujMat (M.ε ρ)) h), fun x => by
    obtain ⟨g, hg⟩ := exists_frameMat_eq M ρ (x := ujMat (M.ε ρ) x) x.2
    exact ⟨g, Subtype.ext (Units.ext hg)⟩⟩

theorem isEmbedding_ujMat {m : ℕ} (ε : Fin m → Bool) : Topology.IsEmbedding (ujMat ε) :=
  (Formalism.REAL.isClosedEmbeddingMatrix m ε).1.isEmbedding

def frameEquiv (ρ : D.what₂.Tau) : GArch D.sp.cm.sig V.gram (placeOf D ρ) ≃ₜ* Formalism.REAL.UJ (M.ε ρ) :=
  { MulEquiv.ofBijective _ (frameHom_bijective M ρ) with
    continuous_toFun := (isEmbedding_ujMat _).continuous_iff.2 (isEmbedding_frameMat M ρ).continuous
    continuous_invFun := (isEmbedding_frameMat M ρ).continuous_iff.2 ((isEmbedding_ujMat _).continuous.congr
      fun x => congrArg (ujMat (M.ε ρ))
        ((MulEquiv.ofBijective _ (frameHom_bijective M ρ)).apply_symm_apply x).symm) }

theorem ujMat_frameEquiv_eq_conj (ρ : D.what₂.Tau) (g : GArch D.sp.cm.sig V.gram (placeOf D ρ)) :
    ujMat (M.ε ρ) (frameEquiv M ρ g) = M.fr ρ * matAt V ρ g * (M.fr ρ)⁻¹ := rfl

theorem dsRep_eq_comp (ρ : D.what₂.Tau) :
    dsRep M ρ = (ujRep (M.ds ρ).2.2.1).comp (frameEquiv M ρ : _ →* Formalism.REAL.UJ (M.ε ρ)) := rfl

theorem isPseudoCoeff_dsRep_iff (ρ : D.what₂.Tau) (μ : Measure (GArch D.sp.cm.sig V.gram (placeOf D ρ)))
    [μ.IsHaarMeasure] (f : Formalism.REAL.UJ (M.ε ρ) → ℂ) : haveI := (M.ds ρ).1
    IsPseudoCoeff (ujMat (M.ε ρ)) (μ.map (frameEquiv M ρ)) (ujRep (M.ds ρ).2.2.1) f ↔
      IsPseudoCoeff (matAt V ρ) μ (dsRep M ρ) (f ∘ frameEquiv M ρ) :=
  haveI := (M.ds ρ).1
  isPseudoCoeff_map_iff (M.fr_unit ρ) (ujMat_frameEquiv_eq_conj M ρ)

theorem exists_isTestArchG
    (h : ∀ ρ, haveI := (M.ds ρ).1
      ∃ (μ : Measure (Formalism.REAL.UJ (M.ε ρ))) (_ : μ.IsHaarMeasure) (f : Formalism.REAL.UJ (M.ε ρ) → ℂ),
        IsPseudoCoeff (ujMat (M.ε ρ)) μ (ujRep (M.ds ρ).2.2.1) f)
    (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) [∀ w, (μa w).IsHaarMeasure] : ∃ fa, IsTestArchG M μa fa := by
  have h1 : ∀ ρ, haveI := (M.ds ρ).1
      ∃ f, IsPseudoCoeff (matAt V ρ) (μa (placeOf D ρ)) (dsRep M ρ) f := fun ρ => by
    haveI := (M.ds ρ).1
    obtain ⟨μ, _, f, hf⟩ := h ρ
    obtain ⟨c, -, hc⟩ := hf.exists_smul ((μa (placeOf D ρ)).map (frameEquiv M ρ))
    exact ⟨_, (isPseudoCoeff_dsRep_iff M ρ _ _).1 hc⟩
  choose f hf using h1
  let p := Equiv.ofBijective _ (placeOf_bijective D)
  refine ⟨Equiv.piCongrLeft (fun w => GArch D.sp.cm.sig V.gram w → ℂ) p f, fun ρ => ?_⟩
  exact (Equiv.piCongrLeft_apply_apply (fun w => GArch D.sp.cm.sig V.gram w → ℂ) p f ρ).symm ▸ hf ρ

end Record

end GlobalTheory.Orb
