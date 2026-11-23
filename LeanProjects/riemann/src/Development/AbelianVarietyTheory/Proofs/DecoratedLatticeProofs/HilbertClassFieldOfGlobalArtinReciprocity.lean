import Mathlib
import ReciprocityTheory.NeutralLocalFields.HilbertClassField
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsoluteGaloisAbelianizationEqOneOfMemOpenSubgro
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenIdeleSubgroupContainsCongruenceUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusRestrictScalarsPowModInertia
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntValuationNormEqSumResidueDegreeMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormCloseToOneOfCloseAbovePlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinsetPlacesOverFinsetPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIdeleClassGroupHomOpenKernel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertiaElementEqOneOrLiesAboveFinitePlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormNearNegOneAtRealPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InfIdeleNegOneNotMemClosurePrincipalIdentityCompStatement

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.NormCompat Neutral.HilbertClassField

namespace GlobalTheory.HilbertFromArtin

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {art : Ideles E →* Gab E Ω}

omit [IsAlgClosure E Ω] in
theorem art_diag (ha : IsGlobalArtin art) (k : Eˣ) : art (diagUnits E k) = 1 := by
  have hk : diagUnits E k ∈ art.ker := by
    rw [ha.ker]
    exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
  exact hk

theorem chi_norm_local (ha : IsGlobalArtin art) {B : Type} [CommGroup B] (χ : Gab E Ω →* B)
    (K : IntermediateField E Ω) [FiniteDimensional E K] [NumberField K]
    (hK : ∀ σ : G K Ω, χ (GlobalTheory.HeckeGal.toAb E Ω (σ.restrictScalars E)) = 1) (v : HeightOneSpectrum (𝓞 E))
    (hv : ∀ x, IsUnitAt v x → χ (art (localIdele E v x)) = 1) (a : Kˣ) :
    χ (art (locUnit E v (Units.map (Algebra.norm E (S := K)) a))) = 1 := by
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.tower_top (K := E) K⟩
  obtain ⟨k, hk⟩ := exists_unif v
  generalize atFin v k = p at hk
  let θ : (v.adicCompletion E)ˣ →* B := χ.comp (art.comp (localIdele E v))
  have hf : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal →
      θ p ^ w.asIdeal.inertiaDeg (𝓞 E) = 1 := fun w hwv => by
    obtain ⟨A, hAw⟩ := exists_isPlaceOver (F := K) Ω w
    obtain ⟨hAv, -, -, hfrob⟩ := GlobalTheory.FrobRestrict.frob_restrict E Ω K v w hwv A hAw
    obtain ⟨σ, hσ⟩ := exists_isFrob hAw
    obtain ⟨φ, hφ, e'⟩ := (ha.frob v A hAv _).mp ⟨p, hk, rfl⟩
    obtain ⟨u, hu, e⟩ := (ha.ine v A hAv _).mpr ⟨_, hfrob σ φ hσ hφ, rfl⟩
    have hm := hv u hu
    rw [e, map_mul, map_mul, hK, one_mul, map_inv, map_inv, map_pow, map_pow] at hm
    show χ (art (localIdele E v p)) ^ _ = 1
    rw [← e', map_inv, map_inv, inv_pow, hm]
  obtain ⟨s, hs⟩ := GlobalTheory.PlacesOver.places_over_finset E K {v}
  have hsum := GlobalTheory.NormValuation.log_valuation_norm_eq_sum E K v a s (fun w => by simp [hs])
  set x : (v.adicCompletion E)ˣ := Units.map (algebraMap E (v.adicCompletion E)).toMonoidHom
    (Units.map (Algebra.norm E (S := K)) a) with hx
  have hxv : Valued.v (x : v.adicCompletion E) = v.valuation E (Algebra.norm E (a : K)) :=
    GlobalTheory.RayFromArtin.valued_algebraMap v _
  have hx0 : Valued.v (x : v.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).mpr x.ne_zero
  have hk' : Valued.v (p : v.adicCompletion E) = WithZero.exp (-1 : ℤ) := hk
  have hu : IsUnitAt v (x * p ^ WithZero.log (Valued.v (x : v.adicCompletion E))) := by
    show Valued.v _ = _
    rw [Units.val_mul, map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, hk', ← WithZero.exp_zsmul]
    nth_rewrite 1 [← WithZero.exp_log hx0]
    rw [← WithZero.exp_add]
    simp
  have h1 : θ (x * p ^ WithZero.log (Valued.v (x : v.adicCompletion E))) = 1 := hv _ hu
  have h2 : θ p ^ WithZero.log (Valued.v (x : v.adicCompletion E)) = 1 := by
    rw [← orderOf_dvd_iff_zpow_eq_one, hxv, hsum]
    refine Finset.dvd_sum fun w hw => Dvd.dvd.mul_right ?_ _
    rw [Int.natCast_dvd_natCast, orderOf_dvd_iff_pow_eq_one]
    exact hf w (by simpa [hs] using hw)
  rwa [map_mul, map_zpow, h2, mul_one] at h1

omit [IsAlgClosure E Ω] in
theorem infPart_mul_finPart (a : Ideles E) : Units.map (infPart E) a * Units.map (finPart E) a = a :=
  Units.ext (Prod.ext (mul_one _) (one_mul _))

theorem art_sign_mem (ha : IsGlobalArtin art) (U : Subgroup (Gab E Ω)) (hU : IsOpen (U : Set (Gab E Ω)))
    (j : Ω →+* ℂ) (c : G E Ω) (hc : ∀ x, j (c x) = starRingEnd ℂ (j x)) (hcU : GlobalTheory.HeckeGal.toAb E Ω c ∈ U) :
    art (infIdele E (InfinitePlace.mk (j.comp (algebraMap E Ω))) (-1)) ∈ U := by
  haveI : DiscreteTopology (Gab E Ω ⧸ U) := QuotientGroup.discreteTopology hU
  let χ : Gab E Ω →* Gab E Ω ⧸ U := QuotientGroup.mk' U
  have hχ : ∀ g, χ g = 1 ↔ g ∈ U := fun g => QuotientGroup.eq_one_iff g
  let ψ : Ideles E →* Gab E Ω ⧸ U := χ.comp art
  have hψ : Continuous ψ := QuotientGroup.continuous_mk.comp ha.quot.continuous
  obtain ⟨L, _, _, hL⟩ := GlobalTheory.RayFromArtin.exists_field (χ.comp (GlobalTheory.HeckeGal.toAb E Ω))
    ((isOpen_discrete {1}).preimage (QuotientGroup.continuous_mk.comp QuotientGroup.continuous_mk))
  haveI : NumberField L := NumberField.of_module_finite E L
  have hK : ∀ σ : G L Ω, χ (GlobalTheory.HeckeGal.toAb E Ω (σ.restrictScalars E)) = 1 := fun σ =>
    (hL _).1 (AlgEquiv.ext fun x => (algebraMap L Ω).injective
      (((σ.restrictScalars E).restrictNormal_commutes L x).trans (σ.commutes x)))
  have hj : ComplexEmbedding.IsReal (j.comp (algebraMap L Ω)) := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have := c.restrictNormal_commutes L x
    rw [show c.restrictNormal L = 1 from (hL c).2 ((hχ _).2 hcU)] at this
    rw [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, ← hc, ← this]
    rfl
  obtain ⟨S, M, -, hSu, hSc⟩ := GlobalTheory.OpenIdeleCongr.open_subgroup_contains_congr E ψ.ker
    ((isOpen_discrete {1}).preimage hψ) ∅
  obtain ⟨T, hT⟩ := GlobalTheory.PlacesOver.places_over_finset E L S
  choose M' hM' using fun v : HeightOneSpectrum (𝓞 E) => GlobalTheory.NormCompat.NormCont.norm_close_to_one E L v M
  have e0 : (j.comp (algebraMap L Ω)).comp (algebraMap E L) = j.comp (algebraMap E Ω) := RingHom.ext fun _ => rfl
  obtain ⟨a, ha1, ha2⟩ := GlobalTheory.T.exists_norm_near_neg_one_at_real_place E L _ hj T (S.sup M') (ψ ⁻¹' {ψ _})
    (hψ.continuousAt.preimage_mem_nhds ((isOpen_discrete _).mem_nhds rfl))
  rw [e0, Set.mem_preimage, Set.mem_singleton_iff] at ha2
  have hfin : ψ (Units.map (finPart E) (diagUnits E (Units.map (Algebra.norm E (S := L)) a))) = 1 := by
    refine GlobalTheory.FrobDense.eq_one_of_local ψ hψ _ rfl fun v => ?_
    change ψ (locUnit E v (Units.map (Algebra.norm E (S := L)) a)) = 1
    by_cases hv : v ∈ S
    · refine hSc v hv _ (hM' v (a : L) fun w hw => (ha1 w ((hT w).2 ⟨v, hv, hw⟩)).trans ?_)
      have : M' v ≤ S.sup M' := Finset.le_sup hv
      rw [WithZero.exp_le_exp]
      omega
    · exact chi_norm_local ha χ L hK v (hSu v hv) a
  have h := congrArg ψ (infPart_mul_finPart (diagUnits E (Units.map (Algebra.norm E (S := L)) a)))
  rw [map_mul, hfin, mul_one, ha2] at h
  refine (hχ _).1 (h.trans ?_)
  show χ (art _) = 1
  rw [art_diag ha, map_one]

omit [NumberField E] [IsAlgClosure E Ω] in
theorem isReal_of_conj (j : Ω →+* ℂ) (c : G E Ω) (hc : ∀ x, j (c x) = starRingEnd ℂ (j x)) :
    (InfinitePlace.mk (j.comp (algebraMap E Ω))).IsReal := by
  rw [InfinitePlace.isReal_mk_iff, ComplexEmbedding.isReal_iff]
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, ← hc, c.commutes]

theorem art_sign_eq (ha : IsGlobalArtin art) (j : Ω →+* ℂ) (c : G E Ω) (hc : ∀ x, j (c x) = starRingEnd ℂ (j x)) :
    art (infIdele E (InfinitePlace.mk (j.comp (algebraMap E Ω))) (-1)) = GlobalTheory.HeckeGal.toAb E Ω c := by
  have hg1 : art (infIdele E (InfinitePlace.mk (j.comp (algebraMap E Ω))) (-1)) ≠ 1 := fun h =>
    GlobalTheory.T.infIdele_neg_one_not_mem_closure_principal_identityComponent E _ (isReal_of_conj j c hc) (ha.ker ▸ h)
  have hmem := fun U hU => art_sign_mem ha U hU j c hc
  generalize art (infIdele E (InfinitePlace.mk (j.comp (algebraMap E Ω))) (-1)) = g at hg1 hmem
  have hcc : c * c = 1 := AlgEquiv.ext fun x => j.injective (by
    rw [AlgEquiv.mul_apply, hc, hc, Complex.conj_conj, AlgEquiv.one_apply])
  have hd : GlobalTheory.HeckeGal.toAb E Ω c * GlobalTheory.HeckeGal.toAb E Ω c = 1 := by rw [← map_mul, hcc, map_one]
  generalize GlobalTheory.HeckeGal.toAb E Ω c = d at hd hmem
  by_contra hne
  have hg2 : g * d ≠ 1 := fun h => hne (mul_right_cancel (h.trans hd.symm))
  obtain ⟨U₁, h₁, g₁⟩ : ∃ U : Subgroup (Gab E Ω), IsOpen (U : Set (Gab E Ω)) ∧ g ∉ U := by
    by_contra! h
    exact hg1 (GlobalTheory.GabSep.eq_one_of_forall_isOpen_subgroup E Ω g h)
  obtain ⟨U₂, h₂, g₂⟩ : ∃ U : Subgroup (Gab E Ω), IsOpen (U : Set (Gab E Ω)) ∧ g * d ∉ U := by
    by_contra! h
    exact hg2 (GlobalTheory.GabSep.eq_one_of_forall_isOpen_subgroup E Ω _ h)
  let V := U₁ ⊓ U₂
  let U : Subgroup (Gab E Ω) :=
    { carrier := {x | x ∈ V ∨ x * d ∈ V}
      one_mem' := Or.inl V.one_mem
      mul_mem' := by
        rintro a b (ha | ha) (hb | hb)
        · exact Or.inl (V.mul_mem ha hb)
        · exact Or.inr (mul_assoc a b d ▸ V.mul_mem ha hb)
        · exact Or.inr (mul_right_comm a d b ▸ V.mul_mem ha hb)
        · refine Or.inl ?_
          have := V.mul_mem ha hb
          rwa [mul_mul_mul_comm, hd, mul_one] at this
      inv_mem' := by
        rintro a (ha | ha)
        · exact Or.inl (V.inv_mem ha)
        · refine Or.inr ?_
          have := V.inv_mem ha
          rwa [mul_inv, inv_eq_of_mul_eq_one_right hd] at this }
  have hU : IsOpen (U : Set (Gab E Ω)) := Subgroup.isOpen_mono (H₁ := V) (fun _ h => Or.inl h) (h₁.inter h₂)
  rcases hmem U hU (Or.inr (hd ▸ V.one_mem)) with h | h
  · exact g₁ h.1
  · exact g₂ h.2

theorem exists_conj (w : InfinitePlace E) (hw : w.IsReal) : ∃ (j : Ω →+* ℂ) (c : G E Ω),
    (∀ x, j (c x) = starRingEnd ℂ (j x)) ∧ InfinitePlace.mk (j.comp (algebraMap E Ω)) = w := by
  haveI : IsGalois E Ω := {}
  let j : Ω →+* ℂ := ComplexEmbedding.lift Ω w.embedding
  have hj : j.comp (algebraMap E Ω) = w.embedding := ComplexEmbedding.lift_comp_algebraMap _ _
  obtain ⟨σ, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := E) j (ComplexEmbedding.conjugate j) (by
    rw [ComplexEmbedding.conjugate_comp, hj, ComplexEmbedding.isReal_iff.1 (InfinitePlace.isReal_iff.1 hw)])
  exact ⟨j, σ.symm, fun x => DFunLike.congr_fun hσ x, by rw [hj, InfinitePlace.mk_embedding]⟩

theorem art_mem_of_class (ha : IsGlobalArtin art) (U : Subgroup (Gab E Ω)) (hU : IsOpen (U : Set (Gab E Ω)))
    (hI : ∀ (A : ValuationSubring Ω), ∀ σ ∈ Ine (F := E) A, GlobalTheory.HeckeGal.toAb E Ω σ ∈ U)
    (hC : ∀ c : G E Ω, IsComplexConjugation c → GlobalTheory.HeckeGal.toAb E Ω c ∈ U)
    (x : Ideles E) (hx : GlobalTheory.Mem.UnitIndex.classHom E x = 1) : art x ∈ U := by
  haveI : IsGalois E Ω := {}
  haveI : DiscreteTopology (Gab E Ω ⧸ U) := QuotientGroup.discreteTopology hU
  haveI : Finite (Gab E Ω ⧸ U) := U.quotient_finite_of_isOpen hU
  let ψ : Ideles E →* Gab E Ω ⧸ U := (QuotientGroup.mk' U).comp art
  have hψU : ∀ y, ψ y = 1 ↔ art y ∈ U := fun y => QuotientGroup.eq_one_iff _
  have hψ : Continuous ψ := QuotientGroup.continuous_mk.comp ha.quot.continuous
  refine (hψU x).1 ((sup_le (fun u hu => ?_) ?_ : _ ≤ ψ.ker) (GlobalTheory.Mem.UnitIndex.ker_classHom_le E hx))
  · rw [← infPart_mul_finPart u]
    refine mul_mem (mem_of_pow E ψ.ker (Nat.card (Gab E Ω ⧸ U)) Nat.card_pos (fun y => ?_) (fun w hw => ?_) _ rfl) ?_
    · rw [MonoidHom.mem_ker, map_pow, pow_card_eq_one']
    · obtain ⟨j, c, hc, rfl⟩ := exists_conj (Ω := Ω) w hw
      rw [MonoidHom.mem_ker, hψU, art_sign_eq ha j c hc]
      exact hC c ⟨j, hc⟩
    · refine GlobalTheory.FrobDense.eq_one_of_local ψ hψ _ rfl fun v => ?_
      obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
      obtain ⟨σ, hσ, e⟩ := (ha.ine v A hA _).1 ⟨Units.map (GlobalTheory.Mem.LocTriv.ev v) (Units.map (finPart E) u), hu v, rfl⟩
      rw [hψU, ← e]
      exact hI A σ hσ
  · rintro _ ⟨k, rfl⟩
    rw [MonoidHom.mem_ker, hψU, art_diag ha]
    exact U.one_mem

theorem classHom_surjective : Function.Surjective (GlobalTheory.Mem.UnitIndex.classHom E) := by
  have key : (QuotientGroup.mk' (GlobalTheory.Mem.UnitIndex.classHom E).range).comp (MonoidHom.id _) = 1 := by
    refine ReciprocityTheory.Neutral.Bridge.HCF.classGroup_hom_ext _ _ fun v => ?_
    obtain ⟨k, hk⟩ := exists_unif v
    rw [MonoidHom.comp_apply, MonoidHom.id_apply, MonoidHom.one_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact ⟨_, GlobalTheory.IdeleClass.classHom_localIdele_unif E v _ hk⟩
  intro c
  have := DFunLike.congr_fun key c
  rw [MonoidHom.comp_apply, MonoidHom.id_apply, MonoidHom.one_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at this
  exact this

omit [IsAlgClosure E Ω] in
theorem mem_ine_iff (A : ValuationSubring Ω) (σ : G E Ω) :
    σ ∈ (A.inertiaSubgroup E).map (A.decompositionSubgroup E).subtype ↔ σ ∈ Ine (F := E) A := by
  rw [ReciprocityTheory.Neutral.Bridge.HCF.mem_inertia_map_iff]
  exact ⟨fun h => ⟨h.1, fun x hx => A.mem_nonunits_iff.1 (h.2 x ((A.valuation_le_one_iff x).1 hx))⟩,
    fun h => ⟨h.1, fun x hx => A.mem_nonunits_iff.2 (h.2 x ((A.valuation_le_one_iff x).2 hx))⟩⟩

theorem mem_hilbertSubgroup (ha : IsGlobalArtin art) (σ : G E Ω) (x : Ideles E)
    (hσ : art x = GlobalTheory.HeckeGal.toAb E Ω σ) (hx : GlobalTheory.Mem.UnitIndex.classHom E x = 1) : σ ∈ hilbertSubgroup E Ω := by
  haveI : IsGalois E Ω := {}
  let N : ClosedSubgroup (G E Ω) := ⟨hilbertSubgroup E Ω, Subgroup.isClosed_topologicalClosure _⟩
  have hN : (IntermediateField.fixedField (hilbertSubgroup E Ω)).fixingSubgroup = hilbertSubgroup E Ω :=
    InfiniteGalois.fixingSubgroup_fixedField N
  rw [← hN, IntermediateField.mem_fixingSubgroup_iff]
  intro y hy
  let V := MulAction.stabilizer (G E Ω) y
  have hV : IsOpen (V : Set (G E Ω)) := stabilizer_isOpen_of_isIntegral y
  have hHV : hilbertSubgroup E Ω ≤ V := fun g hg => (IntermediateField.mem_fixedField_iff _ y).1 hy g hg
  have hgen : ∀ g ∈ ((commutator (G E Ω) : Set (G E Ω)) ∪
      {σ | ∃ A : ValuationSubring Ω, σ ∈ (A.inertiaSubgroup E).map (A.decompositionSubgroup E).subtype} ∪
      {c | IsComplexConjugation c}), g ∈ V := fun g hg =>
    hHV (Subgroup.le_topologicalClosure _ (Subgroup.subset_closure hg))
  have hker : (GlobalTheory.HeckeGal.toAb E Ω).ker ≤ V := by
    rw [GlobalTheory.HeckeGal.toAb, QuotientGroup.ker_mk']
    exact Subgroup.topologicalClosure_minimal _ (fun g hg => hgen g (Or.inl (Or.inl hg))) (V.isClosed_of_isOpen hV)
  have h := art_mem_of_class ha (V.map (GlobalTheory.HeckeGal.toAb E Ω)) (QuotientGroup.isOpenMap_coe _ hV)
    (fun A τ hτ => ⟨τ, hgen τ (Or.inl (Or.inr ⟨A, (mem_ine_iff A τ).2 hτ⟩)), rfl⟩)
    (fun c hc => ⟨c, hgen c (Or.inr hc), rfl⟩) x hx
  rw [hσ, ← Subgroup.mem_comap, Subgroup.comap_map_eq_self hker] at h
  exact h

end GlobalTheory.HilbertFromArtin

open GlobalTheory.HilbertFromArtin in

theorem GlobalTheory.Published.GlobalArtinReciprocity.hilbertClassField :
    GlobalTheory.Published.GlobalArtinReciprocity → Neutral.HilbertClassField.Statement := by
  intro H E Ω _ _ _ _ _
  obtain ⟨art, ha⟩ := H E Ω
  let cl := GlobalTheory.Mem.UnitIndex.classHom E
  have hclo : IsOpen (cl.ker : Set (Ideles E)) :=
    Subgroup.isOpen_mono (GlobalTheory.IdeleClass.unitIdl_le_ker E) GlobalTheory.Mem.UnitOpen.isOpen_unitIdl
  have hker : art.ker ≤ cl.ker := by
    rw [ha.ker]
    exact Subgroup.topologicalClosure_minimal _ (sup_le (GlobalTheory.IdeleClass.diagUnits_range_le_ker E)
      ((GlobalTheory.IdeleClass.infConn_le_unitIdl E).trans (GlobalTheory.IdeleClass.unitIdl_le_ker E)))
      (Subgroup.isClosed_of_isOpen _ hclo)
  let ρ := art.liftOfSurjective ha.quot.surjective ⟨cl, hker⟩
  have hρ : ∀ x, ρ (art x) = cl x := fun x => art.liftOfRightInverse_comp_apply _ _ ⟨cl, hker⟩ x
  have hρo : IsOpen (ρ.ker : Set (Gab E Ω)) := by
    rw [← ha.quot.isQuotientMap.isOpen_preimage]
    convert hclo using 1
    ext x
    rw [Set.mem_preimage, SetLike.mem_coe, SetLike.mem_coe, MonoidHom.mem_ker, hρ, MonoidHom.mem_ker]
  let ψ : (Ω ≃ₐ[E] Ω) →* ClassGroup (𝓞 E) := ρ.comp (GlobalTheory.HeckeGal.toAb E Ω)
  have hlies : ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), LiesAbove A v → IsPlaceOver A v :=
    fun v A h x => by rw [← h x, A.mem_nonunits_iff]
  have hk : ∀ σ, σ ∈ (ψ⁻¹).ker ↔ ρ (GlobalTheory.HeckeGal.toAb E Ω σ) = 1 := fun σ => by
    rw [MonoidHom.mem_ker, MonoidHom.inv_apply, inv_eq_one]
    rfl
  refine ⟨ψ⁻¹, fun b => ?_, le_antisymm (fun σ hσ => ?_) ?_, fun v A φ hv hφ => ?_⟩
  · obtain ⟨x, hx⟩ := classHom_surjective (E := E) b⁻¹
    obtain ⟨σ, hσ⟩ := toAb_surjective (art x)
    refine ⟨σ, ?_⟩
    rw [MonoidHom.inv_apply, inv_eq_iff_eq_inv, ← hx, MonoidHom.comp_apply, hσ, hρ]
  · obtain ⟨x, hx⟩ := ha.quot.surjective (GlobalTheory.HeckeGal.toAb E Ω σ)
    refine mem_hilbertSubgroup ha σ x hx ?_
    rw [hk, ← hx, hρ] at hσ
    exact hσ
  · have ho : IsOpen ((ψ⁻¹).ker : Set (Ω ≃ₐ[E] Ω)) := by
      convert hρo.preimage (QuotientGroup.continuous_mk (N := (commutator (G E Ω)).topologicalClosure)) using 1
      exact Set.ext hk
    refine Subgroup.topologicalClosure_minimal _ ((Subgroup.closure_le _).2 ?_) (Subgroup.isClosed_of_isOpen _ ho)
    rintro g ((hg | ⟨A, hg⟩) | ⟨j, hg⟩)
    · exact Abelianization.commutator_subset_ker _ hg
    · have hg' := (ReciprocityTheory.Neutral.Bridge.HCF.mem_inertia_map_iff E A g).1 hg
      rcases GlobalTheory.inertiaEl_eq_one_or_liesAbove E Ω A g hg' with rfl | ⟨v, hv⟩
      · exact one_mem _
      obtain ⟨x, hu, hx⟩ := (ha.ine v A (hlies v A hv) _).2 ⟨g, (mem_ine_iff A g).1 hg, rfl⟩
      rw [SetLike.mem_coe, hk, ← hx, hρ]
      exact GlobalTheory.IdeleClass.classHom_eq_one_of_mem_unitIdl E (GlobalTheory.IdeleClass.localIdele_mem_unitIdl E v x hu)
    · rw [SetLike.mem_coe, hk, ← art_sign_eq ha j g hg, hρ]
      exact GlobalTheory.IdeleClass.classHom_eq_one_of_mem_unitIdl E fun v =>
        map_one (Valued.v : Valuation (v.adicCompletion E) _)
  · have hF : IsFrob (F := E) A (normV v) φ := ⟨hφ.1, fun x hx => by
      rw [← A.mem_nonunits_iff]
      exact hφ.2 x ((A.valuation_le_one_iff x).1 hx)⟩
    obtain ⟨x, hxu, hx⟩ := (ha.frob v A (hlies v A hv) (GlobalTheory.HeckeGal.toAb E Ω φ⁻¹)).2 ⟨φ, hF, rfl⟩
    rw [MonoidHom.inv_apply, ← map_inv]
    show ρ (GlobalTheory.HeckeGal.toAb E Ω φ⁻¹) = _
    rw [← hx, hρ]
    exact GlobalTheory.IdeleClass.classHom_localIdele_unif E v x hxu

end
