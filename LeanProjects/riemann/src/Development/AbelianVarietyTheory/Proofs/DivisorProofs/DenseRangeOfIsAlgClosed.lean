import Development.AbelianVarietyTheory.Definitions.Divisors.TwoClassFrameHasLevelSetting
import Development.AbelianVarietyTheory.Definitions.Divisors.BlockPairCycPow

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.PlaceBallNormLemmas

variable {l : ℕ} [Fact l.Prime]

theorem denseRange_of_isAlgClosed {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (j : Ω →+* PadicAlgCl l) :
    DenseRange j := by
  rw [Metric.denseRange_iff]
  intro x δ hδ
  have hx : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  set f := minpoly ℚ_[l] x with hf
  have hn : f.natDegree ≠ 0 := (minpoly.natDegree_pos hx).ne'
  have hM : 0 < max ‖x‖ 1 := lt_max_of_lt_right one_pos
  have hq : 0 < δ / max ‖x‖ 1 := div_pos hδ hM
  have hε : 0 < (δ / max ‖x‖ 1) ^ f.natDegree / (f.natDegree + 1) := by positivity
  have hd : DenseRange (algebraMap ℚ ℚ_[l]) := Padic.denseRange_ratCast l
  obtain ⟨g, hg, hdeg, hc⟩ := Polynomial.exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt hd
    (minpoly.monic hx) hε
  obtain ⟨b, hb, hlt⟩ := Polynomial.exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt (L := PadicAlgCl l) hε
    (minpoly.aeval ℚ_[l] x) (minpoly.monic hx) (hg.map _) (by rw [hg.natDegree_map]; exact hdeg.symm) hc
    (IsAlgClosed.splits _)
  rw [← hf, mul_div_cancel₀ _ (by positivity), Real.pow_rpow_inv_natCast hq.le hn, div_mul_cancel₀ _ hM.ne'] at hlt
  have hs : (g.map (algebraMap ℚ Ω)).Splits := IsAlgClosed.splits _
  have e : (g.map (algebraMap ℚ ℚ_[l])).map (algebraMap ℚ_[l] (PadicAlgCl l)) = (g.map (algebraMap ℚ Ω)).map j := by
    rw [Polynomial.map_map, Polynomial.map_map]
    congr 1
    exact Subsingleton.elim _ _
  rw [Polynomial.aroots_def, e, hs.roots_map] at hb
  obtain ⟨y, -, rfl⟩ := Multiset.mem_map.1 hb
  exact ⟨y, by rwa [dist_eq_norm]⟩

theorem norm_aut (σ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (x : PadicAlgCl l) : ‖σ x‖ = ‖x‖ :=
  (spectralNorm_eq_of_equiv σ x).symm

theorem continuous_aut (σ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) : Continuous σ :=
  (AddMonoidHomClass.isometry_of_norm σ (norm_aut σ)).continuous

theorem norm_l : ‖(l : PadicAlgCl l)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap']
  exact Padic.norm_p_lt_one

theorem norm_eq_of_ball {Ω : Type} [Field Ω] (i j : Ω →+* PadicAlgCl l) (h : ∀ x, ‖i x‖ ≤ 1 ↔ ‖j x‖ ≤ 1) (x : Ω) :
    ‖i x‖ = ‖j x‖ := by
  let v : AbsoluteValue Ω ℝ := (NormedField.toAbsoluteValue (PadicAlgCl l)).comp i.injective
  let w : AbsoluteValue Ω ℝ := (NormedField.toAbsoluteValue (PadicAlgCl l)).comp j.injective
  have hv : ∀ x, v x = ‖i x‖ := fun _ => rfl
  have hw : ∀ x, w x = ‖j x‖ := fun _ => rfl
  have he : v.IsEquiv w := by
    rw [AbsoluteValue.isEquiv_iff_lt_one_iff]
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    have := h y⁻¹
    rw [map_inv₀, map_inv₀, norm_inv, norm_inv, inv_le_one₀ (norm_pos_iff.2 ((map_ne_zero i).2 hy)),
      inv_le_one₀ (norm_pos_iff.2 ((map_ne_zero j).2 hy))] at this
    rw [hv, hw, ← not_le, ← not_le, this]
  obtain ⟨c, hc, e⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 he
  have h1 := congrFun e (l : Ω)
  simp only [hv, hw, map_natCast] at h1
  have h0 : 0 < ‖(l : PadicAlgCl l)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hc1 : c = 1 := by
    refine (Real.rpow_right_inj h0 norm_l.ne).1 ?_
    rw [h1, Real.rpow_one]
  have h2 := congrFun e x
  simpa only [hv, hw, hc1, Real.rpow_one] using h2

theorem exists_aut {Ω : Type} [Field Ω] (i j : Ω →+* PadicAlgCl l) (hj : DenseRange j) (h : ∀ x, ‖i x‖ = ‖j x‖) :
    ∃ σ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l, ∀ x, σ (j x) = i x := by
  letI : NormedField Ω := NormedField.induced Ω (PadicAlgCl l) j j.injective
  have hn : ∀ x : Ω, ‖x‖ = ‖j x‖ := fun _ => rfl
  have hji : Isometry j := AddMonoidHomClass.isometry_of_norm j fun x => (hn x).symm
  let f : Ω →+* ℂ_[l] := (algebraMap (PadicAlgCl l) ℂ_[l]).comp i
  have hf : Isometry f := AddMonoidHomClass.isometry_of_norm f fun x => by
    rw [hn, ← h]; exact PadicComplex.norm_extends l (i x)
  let φ : PadicAlgCl l →+* ℂ_[l] := IsDenseInducing.extendRingHom hji.isUniformInducing hj hf.uniformContinuous
  have hφ : ∀ x, φ (j x) = f x := fun x =>
    IsDenseInducing.extend_eq (hji.isUniformInducing.isDenseInducing hj) hf.continuous x
  have hφc : Continuous φ :=
    (uniformContinuous_uniformly_extend hji.isUniformInducing hj hf.uniformContinuous).continuous
  have hcomm : (fun r : ℚ_[l] => φ (algebraMap ℚ_[l] (PadicAlgCl l) r)) = fun r => algebraMap ℚ_[l] ℂ_[l] r := by
    refine (Padic.denseRange_ratCast l).equalizer (hφc.comp (continuous_algebraMap _ _)) (continuous_algebraMap _ _) ?_
    funext q
    simp
  let ψ : PadicAlgCl l →ₐ[ℚ_[l]] ℂ_[l] := { φ with commutes' := fun r => congrFun hcomm r }
  refine ⟨ψ.restrictNormal' (PadicAlgCl l), fun x => (algebraMap (PadicAlgCl l) ℂ_[l]).injective ?_⟩
  exact (ψ.restrictNormal_commutes (PadicAlgCl l) (j x)).trans (hφ x)

section Main

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

def ring (j : Ω →+* PadicAlgCl l) : ValuationSubring Ω :=
  ((NormedField.valuation (K := PadicAlgCl l)).comap j).valuationSubring

theorem mem_ring (j : Ω →+* PadicAlgCl l) (x : Ω) : x ∈ ring j ↔ ‖j x‖ ≤ 1 := by
  rw [ring, Valuation.mem_valuationSubring_iff]
  exact Iff.rfl

theorem valuation_ring_lt (j : Ω →+* PadicAlgCl l) (x : Ω) : (ring j).valuation x < 1 ↔ ‖j x‖ < 1 := by
  rw [ring, ← (Valuation.isEquiv_valuation_valuationSubring _).lt_one_iff_lt_one]
  exact Iff.rfl

theorem norm_int_le (τ : E →+* PadicAlgCl l) (x : 𝓞 E) : ‖τ (x : E)‖ ≤ 1 := by
  have h : IsIntegral ℤ (τ (x : E)) := (RingOfIntegers.isIntegral_coe x).map τ.toIntAlgHom
  have hv := Valuation.integer.integers (NormedField.valuation (K := PadicAlgCl l))
  exact hv.mem_of_integral (h.tower_top (A := (NormedField.valuation (K := PadicAlgCl l)).integer))

def place (τ : E →+* PadicAlgCl l) : HeightOneSpectrum (𝓞 E) where
  asIdeal := (IsLocalRing.maximalIdeal (ring τ)).comap
    ((algebraMap (𝓞 E) E).codRestrict (ring τ) fun x => (mem_ring τ _).2 (norm_int_le τ x))
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    have : ((l : ℕ) : 𝓞 E) ∈ (⊥ : Ideal (𝓞 E)) := by
      rw [← h, Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff, valuation_ring_lt]
      simpa using norm_l (l := l)
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast (Ideal.mem_bot.1 this))

theorem mem_place (τ : E →+* PadicAlgCl l) (x : 𝓞 E) : x ∈ (place τ).asIdeal ↔ ‖τ (x : E)‖ < 1 := by
  rw [place, Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff, valuation_ring_lt]
  exact Iff.rfl

def compl (τ : E →+* PadicAlgCl l) : IntermediateField ℚ_[l] (PadicAlgCl l) :=
  IntermediateField.adjoin ℚ_[l] (Set.range τ)

theorem compl_eq (τ : E →+* PadicAlgCl l) : ∃ α : E, compl τ = IntermediateField.adjoin ℚ_[l] {τ α} := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ E
  refine ⟨α, le_antisymm (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin.mono _ _ _ (by simp))⟩
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ IntermediateField.adjoin ℚ {α} := hα ▸ IntermediateField.mem_top
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy => exact IntermediateField.subset_adjoin _ _ (by rw [Set.mem_singleton_iff.1 hy]; rfl)
  | algebraMap q => simpa using SubfieldClass.ratCast_mem _ q
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | inv a _ ha => rw [map_inv₀]; exact inv_mem ha
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

theorem compl_fin (τ : E →+* PadicAlgCl l) : FiniteDimensional ℚ_[l] (compl τ) := by
  obtain ⟨α, h⟩ := compl_eq τ
  rw [h]
  exact IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)

omit [NumberField E] in
theorem compl_dense (τ : E →+* PadicAlgCl l) : (compl τ : Set (PadicAlgCl l)) ⊆ closure (Set.range τ) := by
  let S : Subfield (PadicAlgCl l) := τ.fieldRange.topologicalClosure
  have hS : ∀ r : ℚ_[l], algebraMap ℚ_[l] (PadicAlgCl l) r ∈ S := fun r => by
    refine (Padic.denseRange_ratCast l).induction_on r ?_ fun q => ?_
    · exact (Subfield.isClosed_topologicalClosure _).preimage (continuous_algebraMap _ _)
    · simpa using SubfieldClass.ratCast_mem S q
  have : compl τ ≤ S.toIntermediateField hS := IntermediateField.adjoin_le_iff.2 fun x hx => subset_closure hx
  exact this

omit [NumberField E] in
theorem mem_fix (τ : E →+* PadicAlgCl l) (σ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) :
    σ ∈ (compl τ).fixingSubgroup ↔ ∀ x, σ (τ x) = τ x := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  refine ⟨fun h x => h _ (IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩), fun h y hy => ?_⟩
  induction hy using IntermediateField.adjoin_induction with
  | mem y hy => obtain ⟨x, rfl⟩ := hy; exact h x
  | algebraMap q => exact σ.commutes q
  | add a b _ _ ha hb => rw [map_add, ha, hb]
  | inv a _ ha => rw [map_inv₀, ha]
  | mul a b _ _ ha hb => rw [map_mul, ha, hb]

omit [NumberField E] in
theorem mem_dec (j : Ω →+* PadicAlgCl l) (g : Ω ≃ₐ[E] Ω) :
    g ∈ ReciprocityTheory.Gal.Dec (F := E) (ring j) ↔ ∀ x, ‖j (g x)‖ = ‖j x‖ := by
  have h0 : g ∈ ReciprocityTheory.Gal.Dec (F := E) (ring j) ↔ ∀ x, g x ∈ ring j ↔ x ∈ ring j := by
    rw [← inv_mem_iff]
    change (open Pointwise in g⁻¹ • ring j) = ring j ↔ _
    rw [SetLike.ext_iff]
    simp only [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, inv_inv, AlgEquiv.smul_def]
  rw [h0]
  simp only [mem_ring]
  exact ⟨fun h => norm_eq_of_ball (j.comp (g : Ω →+* Ω)) j h, fun h x => by rw [h]⟩

omit [NumberField E] in
theorem exists_res [Normal E Ω] (j : Ω →+* PadicAlgCl l) (σ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l)
    (h : ∀ x : E, σ (j (algebraMap E Ω x)) = j (algebraMap E Ω x)) : ∃ g : Ω ≃ₐ[E] Ω, ∀ x, σ (j x) = j (g x) := by
  letI : Algebra Ω (PadicAlgCl l) := j.toAlgebra
  letI : Algebra E (PadicAlgCl l) := (j.comp (algebraMap E Ω)).toAlgebra
  haveI : IsScalarTower E Ω (PadicAlgCl l) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let ψ : PadicAlgCl l →ₐ[E] PadicAlgCl l := { (σ : PadicAlgCl l →+* PadicAlgCl l) with commutes' := h }
  exact ⟨ψ.restrictNormal' Ω, fun x => (ψ.restrictNormal_commutes Ω x).symm⟩

theorem exists_equiv [IsAlgClosure E Ω] (j : Ω →+* PadicAlgCl l) :
    ∃ e : ↥(compl (j.comp (algebraMap E Ω))).fixingSubgroup ≃* ↥(ReciprocityTheory.Gal.Dec (F := E) (ring j)),
      Continuous e ∧ Continuous e.symm ∧
      ∀ σ x, (σ.1 : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (j x) = j (((e σ).1 : Ω ≃ₐ[E] Ω) x) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI := compl_fin (j.comp (algebraMap E Ω))
  have hd := denseRange_of_isAlgClosed j
  set K := compl (j.comp (algebraMap E Ω)) with hK
  choose r hr using fun σ : ↥K.fixingSubgroup => exists_res (E := E) j σ ((mem_fix _ _).1 σ.2)
  let R : ↥K.fixingSubgroup →* (Ω ≃ₐ[E] Ω) := MonoidHom.mk' r fun a b => AlgEquiv.ext fun x => j.injective (by
    rw [← hr, AlgEquiv.mul_apply, ← hr, ← hr]; rfl)
  have hRc : Continuous R := by
    refine continuous_of_continuousAt_one R ?_
    rw [ContinuousAt, map_one]
    intro s hs
    obtain ⟨F, hF, hs⟩ := (krullTopology_mem_nhds_one_iff E Ω s).1 hs
    let b := Module.finBasis E F
    have ho : ∀ᶠ σ : ↥K.fixingSubgroup in nhds 1, ∀ i, (σ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (j (b i)) = j (b i) := by
      refine Filter.eventually_all.2 fun i => ?_
      exact ((stabilizer_isOpen_of_isIntegral (K := ℚ_[l]) (j (b i))).preimage continuous_subtype_val).mem_nhds
        (show (1 : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) ∈ MulAction.stabilizer _ (j (b i)) from one_mem _)
    refine Filter.mem_map.2 (Filter.mem_of_superset ho fun σ hσ => hs ?_)
    refine (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => ?_
    have hl : (r σ).toLinearMap ∘ₗ F.val.toLinearMap = F.val.toLinearMap :=
      b.ext fun i => j.injective ((hr σ _).symm.trans (hσ i))
    exact LinearMap.congr_fun hl ⟨y, hy⟩
  let R' : ↥K.fixingSubgroup →* ↥(ReciprocityTheory.Gal.Dec (F := E) (ring j)) :=
    R.codRestrict _ fun σ => (mem_dec j _).2 fun x => by
      change ‖j (r σ x)‖ = _
      rw [← hr, norm_aut]
  have hbij : Function.Bijective R' := by
    refine ⟨fun a b hab => Subtype.ext (AlgEquiv.ext fun x => ?_), fun g => ?_⟩
    · have hab' : r a = r b := congrArg Subtype.val hab
      refine congrFun (hd.equalizer (continuous_aut a.1) (continuous_aut b.1) (funext fun y => ?_)) x
      change a.1 (j y) = b.1 (j y)
      rw [hr, hr, hab']
    · obtain ⟨σ, hσ⟩ := exists_aut (j.comp (g.1 : Ω →+* Ω)) j hd ((mem_dec j _).1 g.2)
      refine ⟨⟨σ, (mem_fix _ _).2 fun x => (hσ _).trans (congrArg j (g.1.commutes x))⟩,
        Subtype.ext (AlgEquiv.ext fun x => j.injective ?_)⟩
      exact (hr _ x).symm.trans (hσ x)
  have hc : Continuous (MulEquiv.ofBijective R' hbij) := hRc.subtype_mk _
  haveI : CompactSpace ↥K.fixingSubgroup :=
    isCompact_iff_compactSpace.1 (IntermediateField.fixingSubgroup_isClosed K).isCompact
  exact ⟨MulEquiv.ofBijective R' hbij, hc,
    Continuous.continuous_symm_of_equiv_compact_to_t2 (f := (MulEquiv.ofBijective R' hbij).toEquiv) hc, hr⟩

end Main

theorem exists_bridge {E : Type} (Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ}
    [Fact (Nat.Prime l)] (τ : E →+* Formalism.ConjugateSelfDual.Qbar l) :
    ∃ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (_ : Formalism.ConjugateSelfDual.IsPlaceOver A w) (LL : Formalism.BasicNotions.Loc.FinExt l)
      (Bw : Formalism.BasicNotions.LocBridge l E Ω (ReciprocityTheory.Gal.Dec A) ↥(Formalism.BasicNotions.Loc.OL LL)),
      GlobalTheory.Pst.Induces Bw ∧ GlobalTheory.Pst.IsInduced Bw τ (AlgHom.id ℚ_[l] ↥Bw.Kw.1) := by
  obtain ⟨j, hj⟩ : ∃ j : Ω →+* PadicAlgCl l, j.comp (algebraMap E Ω) = τ := by
    letI : Algebra E (PadicAlgCl l) := τ.toAlgebra
    haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
    let j : Ω →ₐ[E] PadicAlgCl l := IsAlgClosed.lift
    exact ⟨j, RingHom.ext fun x => j.commutes x⟩
  subst hj
  obtain ⟨e, h1, h2, h3⟩ := exists_equiv (E := E) j
  haveI := compl_fin (j.comp (algebraMap E Ω))
  let LL : Formalism.BasicNotions.Loc.FinExt l :=
    ⟨IntermediateField.normalClosure ℚ_[l] (compl (j.comp (algebraMap E Ω))) (PadicAlgCl l), inferInstance⟩
  refine ⟨place (j.comp (algebraMap E Ω)), ring j, fun x => ?_, LL,
    { Kw := ⟨compl (j.comp (algebraMap E Ω)), inferInstance⟩
      j := j
      j_E := fun x => IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩
      j_dense := compl_dense _
      e := e.symm
      e_cont := h2
      e_symm_cont := h1
      e_comm := fun g x => (h3 (e.symm g) x).trans (congrArg (fun u : ↥(ReciprocityTheory.Gal.Dec (F := E) (ring j)) => j (u.1 x)) (e.apply_symm_apply g))
      LL := LL
      LL_split := fun t x => t.fieldRange_le_normalClosure ⟨x, rfl⟩
      eO := RingEquiv.refl _
      eO_alg := fun _ => rfl
      eO_cont := continuous_id
      eO_symm_cont := continuous_id }, fun x => mem_ring j x, fun _ => rfl⟩
  rw [valuation_ring_lt, mem_place]
  exact Iff.rfl

end GlobalTheory.PlaceBallNormLemmas

end
