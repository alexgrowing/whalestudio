import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.DenseRangeUnitsR
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.AlgCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusEigenvaluesTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsQuadraticSignCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusSignCompatibility
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepIrreducibilityCriterion
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSSRepTraceNondegenerate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusRestrictScalarsPowModInertia

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
open GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Sd UpperTheory.V.Base
open scoped Pointwise

private def IndCh {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] (e : Γ' →* Γ) (r : Γ' →* GL (Fin 2) k)
    (R : Γ →* GL (Fin 4) k) : Prop :=
  ∀ t : Γ, t ∉ e.range →
    (∀ g g' : Γ', e g' = t⁻¹ * e g * t → (R (e g) : Matrix (Fin 4) (Fin 4) k).charpoly =
      (r g : Matrix (Fin 2) (Fin 2) k).charpoly * (r g' : Matrix (Fin 2) (Fin 2) k).charpoly) ∧
    ∀ g : Γ', e g = t * t →
      (R t : Matrix (Fin 4) (Fin 4) k).charpoly = (r g : Matrix (Fin 2) (Fin 2) k).charpoly.comp (X ^ 2)

section Grp

variable {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] {e : Γ' →* Γ} {δ : Γ →* kˣ}

private theorem conj_mem (h : ∀ s, δ s = 1 ↔ s ∈ e.range) (g : Γ') (t : Γ) : ∃ g', e g' = t⁻¹ * e g * t := by
  refine (h _).1 ?_
  rw [map_mul, map_mul, (h _).2 ⟨g, rfl⟩, mul_one, ← map_mul, inv_mul_cancel, map_one]

private theorem sq_mem (h : ∀ s, δ s = 1 ↔ s ∈ e.range) (h' : ∀ s, δ s = 1 ∨ δ s = -1) (t : Γ) : ∃ g, e g = t * t := by
  refine (h _).1 ?_
  rw [map_mul]
  rcases h' t with h1 | h1 <;> simp [h1]

private theorem ker_ind [CharZero k] (h : ∀ s, δ s = 1 ↔ s ∈ e.range) (h' : ∀ s, δ s = 1 ∨ δ s = -1) {t : Γ}
    (ht : t ∉ e.range) {r : Γ' →* GL (Fin 2) k} {R : Γ →* GL (Fin 4) k} (hR : IsSSRep R) (H : IndCh e r R) (s : Γ')
    (hs : ∀ u s', e s' = u⁻¹ * e s * u → r s' = 1) : R (e s) = 1 := by
  have hs1 : r s = 1 := hs 1 s (by simp)
  have key : ∀ g, (R (e s * g) : Matrix (Fin 4) (Fin 4) k).charpoly = (R g : Matrix (Fin 4) (Fin 4) k).charpoly := by
    intro g
    by_cases hg : g ∈ e.range
    · obtain ⟨g, rfl⟩ := hg
      obtain ⟨g', hg'⟩ := conj_mem h g t
      obtain ⟨s', hs'⟩ := conj_mem h s t
      rw [← map_mul e, (H t ht).1 (s * g) (s' * g') (by rw [map_mul, map_mul, hg', hs']; group), (H t ht).1 g g' hg',
        map_mul, map_mul, hs1, hs t s' hs', one_mul, one_mul]
    · obtain ⟨g2, hg2⟩ := sq_mem h h' g
      obtain ⟨s', hs'⟩ := conj_mem h s g⁻¹
      have hg' : e s * g ∉ e.range := fun h0 => hg ((Subgroup.mul_mem_cancel_left _ (MonoidHom.mem_range.2 ⟨s, rfl⟩)).1 h0)
      rw [(H _ hg').2 (s * s' * g2) (by rw [map_mul, map_mul, hg2, hs']; group), (H g hg).2 g2 hg2,
        map_mul, map_mul, hs1, hs _ s' hs', one_mul, one_mul]
  have h0 := GlobalTheory.isSSRep_trace_nondegenerate Γ k 4 R hR ((R (e s) : Matrix (Fin 4) (Fin 4) k) - (R 1 : GL (Fin 4) k))
    (Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)) fun g => by
      rw [sub_mul, Matrix.trace_sub, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, one_mul,
        Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff, key, sub_self]
  rw [← map_one R]
  exact Units.ext (sub_eq_zero.1 h0)

end Grp

section Places

variable {F E Ω : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω]
  [IsScalarTower F E Ω]

omit [NumberField F] in
private theorem val_lt (A : ValuationSubring Ω) (t : G F Ω) (y : Ω) :
    (t⁻¹ • A).valuation y < 1 ↔ A.valuation (t y) < 1 := by
  have hm : ∀ x, x ∈ t⁻¹ • A ↔ t x ∈ A := fun x => ValuationSubring.mem_inv_pointwise_smul_iff
  rw [valuation_lt_one_iff', valuation_lt_one_iff', hm, hm, map_inv₀, map_eq_zero_iff _ t.injective]

private theorem place_conj {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A v) (t : G F Ω) :
    IsPlaceOver (t⁻¹ • A) v := fun x => by
  rw [val_lt, AlgEquiv.commutes]
  exact h x

private theorem frob_conj {A : ValuationSubring Ω} {q : ℕ} {σ : G F Ω} (hσ : IsFrob (F := F) A q σ) (t : G F Ω) :
    IsFrob (F := F) (t⁻¹ • A) q (t⁻¹ * σ * t) := by
  refine ⟨?_, fun x hx => ?_⟩
  · have h1 : σ • A = A := hσ.1
    show (t⁻¹ * σ * t) • t⁻¹ • A = t⁻¹ • A
    rw [mul_smul, mul_smul, smul_inv_smul, h1]
  · have h1 := hσ.2 (t x) (by
      rwa [ValuationSubring.valuation_le_one_iff, ← AlgEquiv.smul_def, ← ValuationSubring.mem_inv_pointwise_smul_iff,
        ← ValuationSubring.valuation_le_one_iff])
    rwa [val_lt, map_sub, map_pow, AlgEquiv.mul_apply, AlgEquiv.mul_apply, mul_inv_apply]

private theorem ine_iff {A : ValuationSubring Ω} {σ : G F Ω} : σ ∈ Ine (F := F) A ↔ IsFrob (F := F) A 1 σ := by
  simp only [IsFrob, pow_one]
  rfl

omit [NumberField F] [NumberField E] in
private theorem frob_emb {A : ValuationSubring Ω} {q : ℕ} {g : G E Ω} (h : IsFrob (F := F) A q (galEmb F E Ω g)) :
    IsFrob (F := E) A q g := ⟨h.1, h.2⟩

private theorem place_between {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A v) :
    ∃ w : HeightOneSpectrum (𝓞 E), IsPlaceOver A w ∧ w.under (𝓞 F) = v := by
  have hint : ∀ x : 𝓞 E, algebraMap E Ω (x : E) ∈ A := fun x => by
    have h : IsIntegral A (algebraMap E Ω (x : E)) := (x.isIntegral_coe.map (algebraMap E Ω).toIntAlgHom).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    rw [← hy]
    exact y.2
  let f : 𝓞 E →+* A := ((algebraMap E Ω).comp (algebraMap (𝓞 E) E)).codRestrict A hint
  let P : Ideal (𝓞 E) := (IsLocalRing.maximalIdeal A).comap f
  have hP : ∀ x : 𝓞 E, A.valuation (algebraMap E Ω (x : E)) < 1 ↔ x ∈ P := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  have hu : v.asIdeal = P.under (𝓞 F) := by
    ext x
    rw [← hA x, Ideal.under, Ideal.mem_comap, ← hP, IsScalarTower.algebraMap_apply F E Ω]
    rfl
  have hne : P ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [hu, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  exact ⟨⟨P, inferInstance, hne⟩, hP, HeightOneSpectrum.ext hu.symm⟩

private theorem ev_over {P : HeightOneSpectrum (𝓞 E) → Prop} (h : ∀ᶠ w in Filter.cofinite, P w) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → P w := by
  rw [Filter.eventually_cofinite] at h ⊢
  refine (h.image fun w => w.under (𝓞 F)).subset fun v hv => ?_
  by_contra h0
  exact hv fun w hw => not_not.1 fun hP => h0 ⟨w, hP, hw⟩

private theorem ev_notMem {a : 𝓞 E} (ha : a ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 E) in Filter.cofinite, a ∉ v.asIdeal := by
  have h0 : Ideal.span {a} ≠ 0 := by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)

private theorem normV_sq (h2 : Module.finrank F E = 2) (w : HeightOneSpectrum (𝓞 E)) (h : normV w ≠ normV (w.under (𝓞 F))) :
    normV w = normV (w.under (𝓞 F)) ^ 2 := by
  have : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 F)).isMaximal
  have e : normV w = normV (w.under (𝓞 F)) ^ w.asIdeal.inertiaDeg (𝓞 F) :=
    (Ideal.absNorm_pow_inertiaDeg (w.under (𝓞 F)).asIdeal w.asIdeal).symm
  have h1 : 1 < normV w := NumberField.HeightOneSpectrum.one_lt_absNorm w
  have h3 : w.asIdeal.inertiaDeg (𝓞 F) ≤ 2 := by
    haveI : NoZeroSMulDivisors (𝓞 F) (𝓞 E) := ⟨fun {c x} h => by
      rwa [Algebra.smul_def, mul_eq_zero, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)] at h⟩
    rw [← h2, ← Ideal.inertiaDeg'_eq_inertiaDeg (w.under (𝓞 F)).asIdeal]
    exact Ideal.inertiaDeg_le_finrank (𝓞 E) F E w.asIdeal (w.under (𝓞 F)).ne_bot
  generalize w.asIdeal.inertiaDeg (𝓞 F) = f at e h3
  interval_cases f
  · simp [e] at h1
  · exact absurd (by simpa using e) h
  · exact e

private theorem res_surj (w : HeightOneSpectrum (𝓞 E)) (h : normV w = normV (w.under (𝓞 F))) (x : 𝓞 E) :
    ∃ c : 𝓞 F, x - algebraMap (𝓞 F) (𝓞 E) c ∈ w.asIdeal := by
  have : Finite (𝓞 E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  have hi : Function.Injective (Ideal.quotientMap (I := (w.under (𝓞 F)).asIdeal) w.asIdeal (algebraMap (𝓞 F) (𝓞 E)) le_rfl) :=
    Ideal.quotientMap_injective
  obtain ⟨c, hc⟩ := (hi.bijective_of_nat_card_le h.le).2 (Ideal.Quotient.mk _ x)
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  exact ⟨c, Ideal.Quotient.eq.1 hc.symm⟩

private theorem exists_moved (h2 : Module.finrank F E = 2) {t : G F Ω} (ht : t ∉ galOf F E Ω) :
    ∃ x y : 𝓞 E, y - x ≠ 0 ∧ t (algebraMap E Ω x) = algebraMap E Ω y := by
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  by_contra h
  push Not at h
  have h1 : ∀ x : 𝓞 E, t (algebraMap E Ω x) = algebraMap E Ω x := fun x => by
    have e : algebraMap E Ω ((AlgEquiv.restrictNormalHom E t • x : 𝓞 E) : E) = t (algebraMap E Ω (x : E)) :=
      AlgEquiv.restrictNormal_commutes t E (x : E)
    by_contra h0
    refine h x _ (fun h3 => h0 ?_) e.symm
    rw [← e, sub_eq_zero.1 h3]
  refine ht fun x => ?_
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  rw [map_div₀, map_div₀]
  exact congrArg₂ _ (h1 a) (h1 b)

private theorem place_ne {t : G F Ω} {x y : 𝓞 E} (hxy : t (algebraMap E Ω x) = algebraMap E Ω y) {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} (h : normV w = normV (w.under (𝓞 F))) (hA : IsPlaceOver A w) (hA' : IsPlaceOver (t⁻¹ • A) w) :
    y - x ∈ w.asIdeal := by
  obtain ⟨c, hc⟩ := res_surj w h x
  have e : ∀ z : 𝓞 E, algebraMap E Ω ((z - algebraMap (𝓞 F) (𝓞 E) c : 𝓞 E) : E) = algebraMap E Ω z - algebraMap F Ω c := fun z => by
    rw [IsScalarTower.algebraMap_apply F E Ω, ← map_sub]
    rfl
  have h1 := (hA' _).2 hc
  rw [val_lt, e, map_sub, hxy, AlgEquiv.commutes, ← e, hA] at h1
  simpa using w.asIdeal.sub_mem h1 hc

end Places

private theorem algSat_eq (n q : ℕ) (B : Multiset ℂˣ) :
    algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := by
  simp [algSat, Multiset.bind_singleton, Multiset.map_map]

private theorem algSat_four (q : ℕ) (B : Multiset ℂˣ) : algSat 4 q B = (algSat 2 q B).map (· * (q : ℂ)) := by
  have e : (q : ℝ) ^ ((((4 : ℕ) : ℝ) - 1) / 2) = (q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) * q := by
    rw [← Real.rpow_add_one' (Nat.cast_nonneg q) (by norm_num)]
    norm_num
  simp only [algSat_eq, Multiset.map_map, e]
  refine Multiset.map_congr rfl fun b _ => ?_
  simp only [Function.comp_apply]
  push_cast
  ring

private theorem prod_inert (q : ℕ) (B : Multiset ℂˣ) :
    ((algSat 2 (q ^ 2) (B.map (· ^ 2))).map fun b => X - C b).prod.comp (X ^ 2) =
      ((algSat 2 q (B + B.map fun b => -b)).map fun b => X - C b).prod := by
  have e : ((q ^ 2 : ℕ) : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) = ((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2)) ^ 2 := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q),
      ← Real.rpow_mul (Nat.cast_nonneg q), mul_comm]
  simp only [algSat_eq, e, Multiset.map_add, Multiset.map_map, Multiset.prod_add, ← Multiset.prod_map_mul, multiset_prod_comp]
  refine congrArg _ (Multiset.map_congr rfl fun b _ => ?_)
  generalize (q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) = c
  simp only [Function.comp_apply, sub_comp, mul_comp, pow_comp, X_comp, C_comp, Complex.ofReal_pow, Units.val_pow_eq_pow_val, Units.val_neg, map_mul,
    map_pow, map_neg]
  ring

private theorem loc {F E Ω : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Field Ω] [Algebra F E] [Algebra F Ω]
    [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (h2 : Module.finrank F E = 2) {δ : G F Ω →* (Qbar l)ˣ} (hδ : IsSign E δ) {t : G F Ω} (ht : t ∉ (galEmb F E Ω).range)
    {x y : 𝓞 E} (hxy : t (algebraMap E Ω x) = algebraMap E Ω y) {r : G E Ω →* GL (Fin 2) (Qbar l)}
    {R : G F Ω →* GL (Fin 4) (Qbar l)} (hR : IsSSRep R) (H : IndCh (galEmb F E Ω) r R)
    {sat : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ → Prop} (hu : ∀ w B B', sat w B → sat w B' → B = B')
    {satP : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop} {v : HeightOneSpectrum (𝓞 F)}
    (ha : ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ s ∈ Ine (F := F) A, δ s = 1)
    (hb : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → ∃ B, sat w B ∧ FrobEig ι r w (algSat 2 (normV w) B))
    (hc : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v →
      (∀ w' : HeightOneSpectrum (𝓞 E), w' ≠ w → w'.under (𝓞 F) = w.under (𝓞 F) →
        ∃ B B', sat w B ∧ sat w' B' ∧ satP (w.under (𝓞 F)) (B + B')) ∧
      (normV w = normV (w.under (𝓞 F)) ^ 2 → ∃ B B' : Multiset ℂˣ, sat w (B'.map (· ^ 2)) ∧
        B = B' + B'.map (fun b => -b) ∧ satP (w.under (𝓞 F)) B))
    (hd : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → y - x ∉ w.asIdeal)
    (A : ValuationSubring Ω) (hA : IsPlaceOver A v) :
    (∀ s ∈ Ine (F := F) A, R s = 1) ∧ ∀ σ : G F Ω, IsFrob A (normV v) σ → ∃ B, satP v B ∧
      (R σ⁻¹ : Matrix (Fin 4) (Fin 4) (Qbar l)).charpoly.map ι.toRingHom =
        ((algSat 2 (normV v) B).map fun b => X - C b).prod := by
  have h1 : ∀ s, δ s = 1 ↔ s ∈ (galEmb F E Ω).range := hδ.1
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · obtain ⟨s, rfl⟩ := (h1 s).1 (ha A hA s hs)
    refine ker_ind h1 hδ.2 ht hR H s fun u s' hs' => ?_
    obtain ⟨w, hw, hwv⟩ := place_between (E := E) (place_conj hA u)
    obtain ⟨B, -, hB⟩ := hb w hwv
    exact (hB _ hw).1 s' (ine_iff.2 (frob_emb (F := F) (hs' ▸ frob_conj (ine_iff.1 hs) u)))
  obtain ⟨w, hw, rfl⟩ := place_between (E := E) hA
  have hsg : ∀ w' : HeightOneSpectrum (𝓞 E), w'.under (𝓞 F) = w.under (𝓞 F) →
      (δ σ⁻¹ = 1 ↔ normV w' = normV (w.under (𝓞 F))) := fun w' hw' => by
    have h3 := UpperTheory.frobenius_sign_compatibility F E Ω l ι δ hδ w' (hw' ▸ ha)
    rw [hw'] at h3
    have h4 := (h3 A hA).2 σ hσ
    refine ⟨fun h5 => ?_, fun h5 => ?_⟩
    · by_contra h6
      rw [if_neg h6, h5] at h4
      norm_num at h4
    · rw [if_pos h5] at h4
      exact Units.ext (ι.injective (by rw [h4]; simp))
  obtain ⟨B, hB, hE⟩ := hb w rfl
  by_cases hs : δ σ⁻¹ = 1
  · have hs' : δ σ = 1 := by rwa [map_inv, inv_eq_one] at hs
    obtain ⟨g, rfl⟩ := (h1 σ).1 hs'
    obtain ⟨g', hg'⟩ := conj_mem h1 g t
    obtain ⟨w', hw', hwv⟩ := place_between (E := E) (place_conj hA t)
    have hq := (hsg w rfl).1 hs
    have hq' := (hsg w' hwv).1 hs
    have hne : w' ≠ w := by
      rintro rfl
      exact hd w' rfl (place_ne hxy hq hw hw')
    obtain ⟨B', hB', hE'⟩ := hb w' hwv
    obtain ⟨B₁, B₂, k1, k2, k3⟩ := (hc w rfl).1 w' hne hwv
    obtain rfl := hu _ _ _ k1 hB
    obtain rfl := hu _ _ _ k2 hB'
    refine ⟨_, k3, ?_⟩
    have e1 := (hE A hw).2 g (hq ▸ frob_emb (F := F) hσ)
    have e2 := (hE' _ hw').2 g' (hq' ▸ frob_emb (F := F) (hg' ▸ frob_conj hσ t))
    rw [← map_inv (galEmb F E Ω), (H t ht).1 g⁻¹ g'⁻¹ (by rw [map_inv, map_inv, hg']; group), Polynomial.map_mul, e1, e2, hq, hq']
    simp only [algSat_eq, Multiset.map_add, Multiset.prod_add]
  · have hq := normV_sq h2 w fun h => hs ((hsg w rfl).2 h)
    obtain ⟨_, B', k1, rfl, k3⟩ := (hc w rfl).2 hq
    obtain rfl := hu _ _ _ k1 hB
    refine ⟨_, k3, ?_⟩
    obtain ⟨g, hg⟩ := sq_mem h1 hδ.2 σ
    have hf := GlobalTheory.FrobRestrict.isFrob_pow hσ 2
    rw [pow_two σ, ← hg, ← hq] at hf
    have e1 := (hE A hw).2 g (frob_emb (F := F) hf)
    rw [(H σ⁻¹ fun h => hs ((h1 _).2 h)).2 g⁻¹ (by rw [map_inv, hg, mul_inv_rev]), Polynomial.map_comp, e1, hq,
      Polynomial.map_pow, map_X, prod_inert]

private theorem charEig_cyc_inv {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (w : HeightOneSpectrum (𝓞 F)) (hw : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) :
    CharEig ι (cycBar F Ω l)⁻¹ w (normV w : ℂ) := by
  intro A hA
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · have h1 : cycZ F Ω l s = 1 := Units.ext (PadicInt.ext_of_toZModPow.mp fun n => by
      rw [cycZ_toZModPow_eq hw hA (q := 1) (fun x hx => by simpa using hs.2 x hx) n]
      simp)
    rw [MonoidHom.inv_apply, cycBar, MonoidHom.comp_apply, h1, map_one, inv_one]
  · have h2 : ((cycBar F Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : ℕ) := by
      change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _
      rw [cycZ_of_isFrob hw hA hσ, map_natCast, map_natCast]
    rw [MonoidHom.inv_apply, map_inv, inv_inv, h2, map_natCast]

private theorem infOf_two (m : Fin 2 → ℤ) : infOf m = {1 / 2 + (m 0 : ℂ), 1 / 2 + (m 1 : ℂ)} := by
  have e : (((2 : ℕ) : ℂ) - 1) / 2 = 1 / 2 := by norm_num
  rw [infOf, e]
  rfl

private theorem infOf_add {m m' : Fin 2 → ℤ} (h : Function.Injective ![m 0, m 1, m' 0, m' 1]) :
    (infOf m + infOf m').Nodup ∧ ∀ z ∈ infOf m + infOf m', ∃ n : ℤ, z = (n : ℂ) + (((4 : ℕ) : ℂ) - 1) / 2 := by
  have e : infOf m + infOf m' = Finset.univ.val.map fun i => 1 / 2 + ((![m 0, m 1, m' 0, m' 1] i : ℤ) : ℂ) := by
    rw [infOf_two, infOf_two]
    rfl
  rw [e]
  refine ⟨Finset.univ.nodup.map fun i j hij => h (Int.cast_injective (add_left_cancel hij)), fun z hz => ?_⟩
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
  exact ⟨![m 0, m 1, m' 0, m' 1] i - 1, by push_cast; ring⟩

theorem UpperTheory.V.Sd.indAut :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Published.QuadInduction → UpperTheory.V.Sd.IndAut := by
  intro hP hQ E Ω _ _ _ _ _ _ _ h2 l _ ι π r m m' hatt ⟨v, v', hvv, hv, hv'⟩ hinj R hR H
  haveI : IsAlgClosure E Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) E⟩
  obtain ⟨hnd, hint⟩ := infOf_add hinj
  rcases hQ ℚ E h2 2 one_le_two π with ⟨h, -⟩ | ⟨P, hinf, hfin⟩
  · have e := (h v v' _ (Subsingleton.elim _ _) hv).unique hv'
    rw [← e, Multiset.nodup_add] at hnd
    exact (Multiset.disjoint_left.1 hnd.2.2 (show 1 / 2 + (m 0 : ℂ) ∈ _ by simp [infOf_two]) (by simp [infOf_two])).elim
  obtain ⟨δ, -, hδ1, hδ, hδu⟩ := UpperTheory.exists_quadratic_sign_character ℚ E Ω l h2
  obtain ⟨t, ht⟩ : ∃ t, t ∉ (galEmb ℚ E Ω).range := by
    by_contra h
    exact hδ1 (MonoidHom.ext fun s => (hδ.1 s).2 (not_not.1 fun hs => h ⟨s, hs⟩))
  obtain ⟨x, y, hne, hxy⟩ := exists_moved h2 (range_galEmb ℚ E Ω ▸ ht)
  have H' : IndCh (galEmb ℚ E Ω) r R := fun u hu => H u (range_galEmb ℚ E Ω ▸ hu)
  have key : IsAutR ι (tw R (cycBar ℚ Ω l)⁻¹) := by
    refine ⟨P, fun u => ⟨_, ?_, hnd, hint⟩, (UpperTheory.galoisRep_irreducibility_criterion.1 _ (G ℚ Ω) _ 4 R).2.2 _ hR, ?_⟩
    · rw [Subsingleton.elim u (v.comap (algebraMap ℚ E))]
      exact hinf v v' _ _ hvv (Subsingleton.elim _ _) hv hv'
    · filter_upwards [hδu, ev_over (F := ℚ) hatt.2, ev_over (F := ℚ) hfin, ev_over (F := ℚ) (ev_notMem hne),
        ev_notMem (E := ℚ) (a := (l : 𝓞 ℚ)) (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)] with u ha hb hc hd hl
      have h3 := loc ι h2 hδ ht hxy hR H' (sat := π.HasSat) (fun _ _ _ => TR.CuspSub.HasSat.unique) (satP := P.HasSat) ha hb hc hd
      obtain ⟨A₀, hA₀⟩ := exists_isPlaceOver Ω u
      obtain ⟨σ₀, hσ₀⟩ := ReciprocityTheory.Gal.exists_isFrob hA₀
      obtain ⟨B, hB, -⟩ := (h3 A₀ hA₀).2 σ₀ hσ₀
      refine ⟨B, hB, ?_⟩
      rw [algSat_four]
      refine UpperTheory.frobenius_eigenvalues_twist ℚ Ω l ι 4 _ _ u _ _ (fun A hA => ⟨(h3 A hA).1, fun σ hσ => ?_⟩) (charEig_cyc_inv ι u hl)
      obtain ⟨B', hB', e⟩ := (h3 A hA).2 σ hσ
      rw [hB.unique hB', e]
  have h4 := UpperTheory.V.Sd.twR hP ℚ Ω l ι 4 _ _ ((UpperTheory.V.Sd.algCyc hP ℚ Ω l ι).1 1 1 (by simp)) key
  convert h4 using 1
  refine MonoidHom.ext fun s => Units.ext ?_
  rw [tw_val, tw_val, smul_smul, ← Units.val_mul]
  simp
