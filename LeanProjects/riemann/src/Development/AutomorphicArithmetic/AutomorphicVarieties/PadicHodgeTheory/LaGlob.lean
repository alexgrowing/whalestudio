import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsTotallyImaginaryPadicSqrt
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsLocallyAlgebraicTransferOfPlaceIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaHecke
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaArtin
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExPlaceIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceEqOfContEmbCompEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamAndJumpsRankOneLAdicCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOddPrimeGtTwoBounds
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

namespace UpperTheory.V.Loc

theorem natCast_mem_of_induces {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : GlobalTheory.Pst.Induces Bw) :
    ((l : ℕ) : 𝓞 F) ∈ w.asIdeal := by
  rw [← h, hj.valuation_lt_one_iff]
  have : Bw.j (algebraMap F Ω (((l : ℕ) : 𝓞 F) : F)) = algebraMap ℚ_[l] (Om l) (l : ℚ_[l]) := by simp
  rw [this, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

private theorem mem_of_norm {R : Type} [CommRing R] {l : ℕ} [Fact l.Prime] (f : R →+* Om l) (I : Ideal R) (hI : I.IsMaximal)
    (hl : (l : R) ∈ I) (h1' : ∀ y ∈ I, ‖f y‖ < 1) (x : R) (hx' : ‖f x‖ < 1) : x ∈ I := by
  have h2 : ∀ a, ‖f a‖ ≤ 1 := fun a => by
    by_contra ha
    have h0 : 0 < ‖f (l : R)‖ := by
      rw [map_natCast, norm_pos_iff]
      exact Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (‖f (l : R)‖⁻¹) (not_le.1 ha)
    have := h1' _ (I.mul_mem_right (a ^ k) hl)
    rw [map_mul, map_pow, norm_mul, norm_pow] at this
    rw [inv_lt_iff_one_lt_mul₀' h0] at hk
    linarith
  by_contra hxw
  obtain ⟨a, b, hb, e⟩ := hI.exists_inv hxw
  have h3 := congrArg (fun y => ‖f y‖) e
  simp only [map_add, map_mul, map_one, norm_one] at h3
  have h4 := IsUltrametricDist.norm_add_le_max (f a * f x) (f b)
  have h5 : ‖f a * f x‖ < 1 := by
    rw [norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right (h2 a) (norm_nonneg _) hx'
  rw [h3] at h4
  exact absurd h4 (not_le.2 (max_lt h5 (h1' b hb)))

theorem exists_isInduced_emb {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : GlobalTheory.Pst.Induces Bw) (τ : Emb l w) :
    ∃ τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥Bw.LL.1,
      GlobalTheory.Pst.IsInduced Bw (τ.1.comp (algebraMap F (w.adicCompletion F))) τ' := by
  have hl := natCast_mem_of_induces h Bw hj
  have hl' : w ∈ placesOver F l := by simpa [placesOver] using hl
  obtain ⟨j, hjc⟩ := τ
  have h1 := norm_lt_one_of_contEmb w j hjc
  have h2 := mem_of_norm ((j.comp (algebraMap F (w.adicCompletion F))).comp (algebraMap (𝓞 F) F)) _ w.isMaximal hl
    (fun y hy => by rw [RingHom.comp_apply, RingHom.comp_apply]; exact h1 y hy)
  refine GlobalTheory.CharAboveRead.exists_isInduced_of (j.comp (algebraMap F (w.adicCompletion F))) w hl' (fun x => ?_) A h O Bw hj
  rw [RingOfIntegers.coe_eq_algebraMap]
  refine ⟨fun hx => h2 x ?_, fun hx => ?_⟩
  · rw [RingHom.comp_apply]
    exact hx
  · rw [RingHom.comp_apply]
    exact h1 x hx

private theorem ex_place {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] {A : ValuationSubring Ω} {p : ℕ}
    (hp0 : p ≠ 0) (hp : A.valuation (p : Ω) < 1) : ∃ w : Plc L, IsPlaceOver A w := by
  have hint : ∀ x : 𝓞 L, algebraMap L Ω (x : L) ∈ A := fun x => by
    have h : IsIntegral A (algebraMap L Ω (x : L)) :=
      (x.isIntegral_coe.map (algebraMap L Ω).toIntAlgHom).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    rw [← hy]
    exact y.2
  let f : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A hint
  let P : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal A).comap f
  have hP : ∀ x : 𝓞 L, A.valuation (algebraMap L Ω (x : L)) < 1 ↔ x ∈ P := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  have hne : P ≠ ⊥ := by
    intro h
    have := (hP (p : 𝓞 L)).1 (by simpa using hp)
    rw [h, Ideal.mem_bot] at this
    exact hp0 (Nat.cast_eq_zero.1 this)
  exact ⟨⟨P, inferInstance, hne⟩, hP⟩

private theorem ex_comp (F E Ω : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] [Algebra E Ω] :
    ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : Algebra F M) (_ : Algebra E M) (_ : Algebra M Ω)
      (_ : IsScalarTower F M Ω) (_ : IsScalarTower E M Ω) (_ : IsAlgClosure M Ω),
      ∀ S : Subfield Ω, (∀ x : F, algebraMap F Ω x ∈ S) → (∀ x : E, algebraMap E Ω x ∈ S) →
        ∀ x : M, algebraMap M Ω x ∈ S := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ E
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  let M := IntermediateField.adjoin F {algebraMap E Ω α}
  haveI : FiniteDimensional F M := IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
  haveI : NumberField M := NumberField.of_module_finite F M
  have hE : ∀ x : E, algebraMap E Ω x ∈ M := fun x => by
    let T : IntermediateField ℚ E := (M.toSubfield.comap (algebraMap E Ω)).toIntermediateField fun q => by
      simpa using SubfieldClass.ratCast_mem (M.toSubfield.comap (algebraMap E Ω)) q
    have : IntermediateField.adjoin ℚ {α} ≤ T :=
      IntermediateField.adjoin_simple_le_iff.2 (IntermediateField.mem_adjoin_simple_self F _)
    rw [hα] at this
    exact this (IntermediateField.mem_top (x := x))
  letI : Algebra E M := ((algebraMap E Ω).codRestrict M hE).toAlgebra
  refine ⟨M, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    IsScalarTower.of_algebraMap_eq fun _ => rfl, ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := F) M⟩,
    fun S hF hS x => ?_⟩
  have : M ≤ S.toIntermediateField hF := IntermediateField.adjoin_simple_le_iff.2 (hS α)
  exact this x.2

theorem laGlob (hG : GlobalArtinReciprocity) (hH : HeckeLAdicCharacter) {F Ω : Type} [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w)
    (wt : Emb l w → ℤ) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : GlobalTheory.Pst.Induces Bw) (ι : Qbar l ≃+* ℂ) :
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : Algebra E Ω) (_ : IsAlgClosure E Ω) (u : Plc E)
      (_ : IsPlaceOver A u) (Bw' : LocBridge l E Ω (Dec (F := E) A) O) (art : Neutral.B1.Ideles E →* Gab E Ω)
      (χ : Formalism.L2.Host.HChar E) (n : (E →+* ℂ) → ℤ) (μ : G E Ω →* (Qbar l)ˣ) (ν : ↥(Dec (F := F) A) →* (Qbar l)ˣ),
      Bw'.Kw = Bw.Kw ∧ Bw'.j = Bw.j ∧ Bw'.LL = Bw.LL ∧ IsGlobalArtin art ∧ IsAlgPos χ n ∧ Continuous μ ∧
      IsLAdicOf art ι χ n μ ∧ Continuous ν ∧
      (∀ (g : ↥(Dec (F := F) A)) (g' : G E Ω), (∀ z, (g : G F Ω) z = g' z) → ν g = μ g') ∧ IsLocAlg h ν wt ∧
      ∀ (τ : Emb l w) (s : ↥Bw.Kw.1 →ₐ[ℚ_[l]] Om l) (τE : E →+* Qbar l),
        (∀ x : F, τ.1 (algebraMap F _ x) = s ⟨Bw.j (algebraMap F Ω x), Bw.j_E x⟩) →
        (∀ (x : E) (hx : Bw.j (algebraMap E Ω x) ∈ Bw.Kw.1), τE x = s ⟨Bw.j (algebraMap E Ω x), hx⟩) →
        n (ι.toRingHom.comp τE) = -wt τ := by
  classical
  have hl := natCast_mem_of_induces h Bw hj
  obtain ⟨E, _, _, _, _, _, hK, δ, hδ0, hδ, c, hc⟩ := UpperTheory.exists_totally_imaginary_padic_sqrt F Ω l Bw.j Bw.Kw
  have hE : ∀ x : E, Bw.j (algebraMap E Ω x) ∈ Bw.Kw.1 := fun x => hK ▸ IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : Plc E, IsPlaceOver A u :=
    ex_place (Fact.out : l.Prime).ne_zero (by simpa using (h _).2 hl)
  obtain ⟨e, he, he', hec⟩ := GlobalTheory.PlaceBridge.exists_mulEquiv (E := E) hj Bw.Kw hK.symm
  let Bw' : LocBridge l E Ω (Dec (F := E) A) O :=
    { Bw with
      j_E := hE
      j_dense := hK ▸ GlobalTheory.PlaceBridge.adjoin_range_subset_closure (Bw.j.comp (algebraMap E Ω))
      e := e
      e_cont := he
      e_symm_cont := he'
      e_comm := hec }
  have hj' : GlobalTheory.Pst.Induces Bw' := hj
  let R : (E →+* Om l) → Emb l w → Prop := fun τE τ => ∃ s : ↥Bw.Kw.1 →ₐ[ℚ_[l]] Om l,
    (∀ x : F, τ.1 (algebraMap F _ x) = s ⟨Bw.j (algebraMap F Ω x), Bw.j_E x⟩) ∧
      ∀ x : E, τE x = s ⟨Bw.j (algebraMap E Ω x), hE x⟩
  have hR1 : ∀ τE τ τ₂, R τE τ → R τE τ₂ → τ = τ₂ := by
    rintro τE τ τ₂ ⟨s, h1, h2⟩ ⟨s', h1', h2'⟩
    have : s = s' := IntermediateField.algHom_ext_of_eq_adjoin ℚ_[l] hK.symm (by
      rintro _ ⟨x, rfl⟩
      exact (h2 x).symm.trans (h2' x))
    subst this
    refine Subtype.ext (DFunLike.coe_injective ?_)
    refine (HeightOneSpectrum.denseRange_algebraMap (K := F) (v := w)).equalizer τ.2 τ₂.2 ?_
    funext x
    exact (h1 x).trans (h1' x).symm
  have hR2 : ∀ τE τ, R τE τ → τE δ = algebraMap ℚ_[l] (Om l) c := by
    rintro τE τ ⟨s, -, h2⟩
    rw [h2, ← s.commutes]
    exact congrArg s (Subtype.ext hc.symm)
  have hc0 : algebraMap ℚ_[l] (Om l) c ≠ 0 := by
    rw [hc]
    exact (map_ne_zero _).2 ((map_ne_zero _).2 hδ0)
  let m : (E →+* ℂ) → ℤ := fun φ => if H : ∃ τ, R (ι.symm.toRingHom.comp φ) τ then -wt H.choose else 0
  let n : (E →+* ℂ) → ℤ := fun φ => m φ - m (ComplexEmbedding.conjugate φ)
  have hn : ∀ τE τ, R τE τ → n (ι.toRingHom.comp τE) = -wt τ := fun τE τ H => by
    have e1 : ι.symm.toRingHom.comp (ι.toRingHom.comp τE) = τE := RingHom.ext fun x => ι.symm_apply_apply _
    have H1 : ∃ τ, R (ι.symm.toRingHom.comp (ι.toRingHom.comp τE)) τ := ⟨τ, e1.symm ▸ H⟩
    have H2 : ¬ ∃ τ, R (ι.symm.toRingHom.comp (ComplexEmbedding.conjugate (ι.toRingHom.comp τE))) τ := by
      rintro ⟨τ₂, H₂⟩
      have a1 := hR2 _ _ H
      have a2 : ι.symm (starRingEnd ℂ ((ι.toRingHom.comp τE) δ)) = _ := hR2 _ _ H₂
      rw [hδ, map_neg] at a2
      have a3 : ι.symm ((ι.toRingHom.comp τE) δ) = τE δ := ι.symm_apply_apply _
      rw [a3, a1] at a2
      exact hc0 (neg_eq_self.1 a2)
    show m _ - m _ = _
    simp only [m]
    rw [dif_pos H1, dif_neg H2, sub_zero, hR1 _ _ _ H1.choose_spec (e1.symm ▸ H)]
  obtain ⟨χ, hχ, -⟩ := GlobalTheory.AlgCharUnr.exists_algChar_unr E l Fact.out n 0 (fun φ => by
    have : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ := star_star φ
    simp only [n, this]
    ring)
  obtain ⟨art, hart, H⟩ := hH E Ω
  obtain ⟨μ, ⟨hμ, hL⟩, -⟩ := H l ι χ n hχ
  let ν : ↥(Dec (F := F) A) →* (Qbar l)ˣ :=
    (μ.comp (Dec (F := E) A).subtype).comp (Bw.e.trans e.symm).toMonoidHom
  have hν : ∀ (g : ↥(Dec (F := F) A)) (g' : G E Ω), (∀ z, (g : G F Ω) z = g' z) → ν g = μ g' := fun g g' hg => by
    refine congrArg μ (AlgEquiv.ext fun z => Bw.j.injective ?_)
    show Bw.j (((e.symm (Bw.e g) : ↥(Dec (F := E) A)) : G E Ω) z) = _
    rw [← hec, MulEquiv.apply_symm_apply, Bw.e_comm, hg]
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, u, hu, Bw', art, χ, n, μ, ν, rfl, rfl, rfl,
    hart, hχ, hμ, hL, (hμ.comp continuous_subtype_val).comp (he'.comp Bw.e_cont), hν, ?_,
    fun τ s τE h1 h2 => hn τE τ ⟨s, h1, fun x => h2 x _⟩⟩
  obtain ⟨M, _, _, _, _, _, _, _, _, hM⟩ := ex_comp F E Ω
  have hMK : ∀ x : M, Bw.j (algebraMap M Ω x) ∈ Bw.Kw.1 := hM (Bw.Kw.1.toSubfield.comap Bw.j) Bw.j_E hE
  obtain ⟨t, ht, iF, hF⟩ := Af.Cq.exPlaceIso F M Ω l A w h O Bw hj hMK
  obtain ⟨t', ht', iE, hE'⟩ := Af.Cq.exPlaceIso E M Ω l A u hu O Bw' hj' hMK
  obtain rfl : t = t' := HeightOneSpectrum.ext (Ideal.ext fun x => (ht x).symm.trans (ht' x))
  obtain ⟨BM, b1, b2, b3⟩ := Af.Cq.exBridge F M Ω l A O Bw hMK
  have hjM : GlobalTheory.Pst.Induces BM := fun x => by rw [b2]; exact hj x
  let κM : ↥(Dec (F := M) A) →* (Qbar l)ˣ :=
    (μ.comp (AlgEquiv.restrictScalarsHom E : G M Ω →* G E Ω)).comp (Dec (F := M) A).subtype
  refine (UpperTheory.isLocallyAlgebraic_transfer_of_placeIso hG h ht _ iF hF ν κM (fun g g' hg => hν g _ hg) wt _ (fun _ => rfl)).2 ?_
  refine (UpperTheory.isLocallyAlgebraic_transfer_of_placeIso hG hu ht _ iE hE' (μ.comp (Dec (F := E) A).subtype) κM
    (fun g g' hg => congrArg μ (AlgEquiv.ext hg)) _ _ (fun τ => ?_)).1
    (laHecke hu art hart ι χ n μ hL (laArtin hG hu))
  obtain ⟨τ', hτ'⟩ := exists_isInduced_emb ht BM hjM τ
  let s : ↥Bw.Kw.1 →ₐ[ℚ_[l]] Om l :=
    (BM.LL.1.val.comp τ').comp (IntermediateField.inclusion (le_of_eq (congrArg Subtype.val b1.symm)))
  have hs : ∀ x : M, τ.1 (algebraMap M _ x) = s ⟨Bw.j (algebraMap M Ω x), hMK x⟩ := fun x =>
    (hτ' x).trans (congrArg (fun y => ((τ' y : ↥BM.LL.1) : Om l)) (Subtype.ext (congrArg (fun j : Ω →+* Om l => j _) b2)))
  have := hn ((τ.1.comp iE.toRingHom).comp (algebraMap E _)) ⟨τ.1.comp iF.toRingHom, τ.2.comp hF.cont⟩ ⟨s, fun x => ?_, fun x => ?_⟩
  · rw [← neg_neg (wt _), ← this]
    rfl
  · show τ.1 (iF _) = _
    rw [hF.loc, hs]
    exact congrArg s (Subtype.ext (congrArg Bw.j (IsScalarTower.algebraMap_apply F M Ω x).symm))
  · show τ.1 (iE _) = _
    rw [hE'.loc, hs]
    exact congrArg s (Subtype.ext (congrArg Bw.j (IsScalarTower.algebraMap_apply E M Ω x).symm))

end UpperTheory.V.Loc
