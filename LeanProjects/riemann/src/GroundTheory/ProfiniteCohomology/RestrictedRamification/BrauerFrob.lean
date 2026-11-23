import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerLocalVal
import GroundTheory.ProfiniteCohomology.Characters
import GroundTheory.ProfiniteCohomology.CupProducts.ExistsCocycleMapFEqD
import GroundTheory.LocalFields.MaximalUnramified
import GroundTheory.LocalFields.TameExtension
import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeRangeNormUnits
import GroundTheory.LocalFields.LocalArtinTransport
import GroundTheory.LocalFields.Uniqueness
import GroundTheory.LocalFields.SeparableClosure
import GroundTheory.GlobalFields.CompletionAtPlace.Integers
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain IntermediateField GroundTheory.Global groupCohomology

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

section Characters

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

instance isDiscreteRep_uliftIntToIntRep_trivRep : IsDiscreteRep (uliftIntToIntRep (trivRep G ℤ)) :=
  isDiscreteRep_uliftIntToIntRep _

def trivRepToTrivial : uliftIntToIntRep (trivRep G ℤ) ⟶ Rep.trivial ℤ G ℤ :=
  Rep.ofHom ⟨LinearMap.id, fun _ => LinearMap.ext fun _ => rfl⟩

def trivialToTrivRep : Rep.trivial ℤ G ℤ ⟶ uliftIntToIntRep (trivRep G ℤ) :=
  Rep.ofHom ⟨LinearMap.id, fun _ => LinearMap.ext fun _ => rfl⟩

def trivRepCohomologyEquiv (n : ℕ) :
    cohomology (uliftIntToIntRep (trivRep G ℤ)) n ≃+ cohomology (Rep.trivial ℤ G ℤ) n where
  toFun := (cohomologyMap (trivRepToTrivial G) n).hom
  invFun := (cohomologyMap (trivialToTrivRep G) n).hom
  left_inv x := by
    rw [← ConcreteCategory.comp_apply, ← cohomologyMap_comp]
    have : trivRepToTrivial G ≫ trivialToTrivRep G = 𝟙 _ := by
      ext; rfl
    rw [this, cohomologyMap_id]
    rfl
  right_inv x := by
    rw [← ConcreteCategory.comp_apply, ← cohomologyMap_comp]
    have : trivialToTrivRep G ≫ trivRepToTrivial G = 𝟙 _ := by
      ext; rfl
    rw [this, cohomologyMap_id]
    rfl
  map_add' := map_add _

def gvChar : cohomology (trivRep G ℤ) 2 ≃+ (Additive G →ₜ+ QZ) :=
  ((cohomologyULiftIntAddEquiv (trivRep G ℤ) 2).trans (trivRepCohomologyEquiv G 2)).trans
    (cohomologyTwoIntAddEquiv G)

variable {G}

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
theorem isLocallyConstant_ratModInt (q : G → ℚ) (hq : IsLocallyConstant q) :
    IsLocallyConstant (fun g : Fin 1 → G =>
      (((q (g 0) : ℚ) : AddCircle (1 : ℚ)) : Rep.trivial ℤ G (AddCircle (1 : ℚ)))) :=
  (hq.comp_continuous (continuous_apply 0)).comp
    (fun x : ℚ => ((x : AddCircle (1 : ℚ)) : Rep.trivial ℤ G (AddCircle (1 : ℚ))))

def ratModIntCocycle (q : G → ℚ) (hq : IsLocallyConstant q)
    (hint : ∀ g h : G, ∃ n : ℤ, (n : ℚ) = q h - q (g * h) + q g) :
    cocycles (Rep.trivial ℤ G (AddCircle (1 : ℚ))) 1 :=
  (cochainsComplex (Rep.trivial ℤ G (AddCircle (1 : ℚ)))).cyclesMk
    (mkCochain _ _ (isLocallyConstant_ratModInt q hq)) 2 (by simp) (by
      change ((cochainsComplex (Rep.trivial ℤ G (AddCircle (1 : ℚ)))).d 1 2).hom _ = 0
      apply cochainOf_injective
      rw [cochainOf_d, cochainOf_zero]
      funext u
      rw [inhomogeneousCochains_d_one_apply, cochainOf_mkCochain]
      obtain ⟨n, hn⟩ := hint (u 0) (u 1)
      change ((q (u 1) : ℚ) : AddCircle (1 : ℚ)) - ((q (u 0 * u 1) : ℚ) : AddCircle (1 : ℚ)) +
        ((q (u 0) : ℚ) : AddCircle (1 : ℚ)) = 0
      rw [← AddCircle.coe_sub, ← AddCircle.coe_add, ← hn, AddCircle.coe_eq_zero_iff]
      exact ⟨n, by simp⟩)

theorem cochainOf_ratModIntCocycle (q : G → ℚ) (hq : IsLocallyConstant q)
    (hint : ∀ g h : G, ∃ n : ℤ, (n : ℚ) = q h - q (g * h) + q g) (g : Fin 1 → G) :
    cochainOf _ (cocycleι _ 1 (ratModIntCocycle q hq hint)) g = ((q (g 0) : ℚ) : AddCircle (1 : ℚ)) := by
  have h : cocycleι _ 1 (ratModIntCocycle q hq hint) =
      mkCochain _ _ (isLocallyConstant_ratModInt q hq) :=
    (cochainsComplex (Rep.trivial ℤ G (AddCircle (1 : ℚ)))).i_cyclesMk _ _ _ _
  rw [h, cochainOf_mkCochain]

theorem gvChar_cohomologyπ (z : cocycles (trivRep G ℤ) 2) (q : G → ℚ) (hq : IsLocallyConstant q)
    (hzq : ∀ g h : G, ((cochainOf _ (cocycleι _ 2 z) ![g, h] : ℤ) : ℚ) = q h - q (g * h) + q g)
    (g : G) : gvChar G (cohomologyπ _ 2 z) (Additive.ofMul g) = QZ.mk (q g) := by

  let z₂ := cocyclesMapAlong (MonoidHom.id G) continuous_id (trivRepToTrivial G) 2
    (cocyclesULiftInt _ z)
  have hz₂ : ∀ u, cochainOf _ (cocycleι _ 2 z₂) u = cochainOf _ (cocycleι _ 2 z) u := by
    intro u
    rw [cochainOf_cocycleι_cocyclesMapAlong, cochainOf_cocycleι_cocyclesULiftInt]
    rfl
  have h1 : gvChar G (cohomologyπ _ 2 z) = cohomologyTwoIntAddEquiv G (cohomologyπ _ 2 z₂) := by
    change cohomologyTwoIntAddEquiv G ((cohomologyMap (trivRepToTrivial G) 2).hom
      (cohomologyULiftIntAddEquiv (trivRep G ℤ) 2 (cohomologyπ _ 2 z))) = _
    rw [cohomologyULiftIntAddEquiv_cohomologyπ', ← cohomologyMapAlong_id_eq_cohomologyMap]
    exact congrArg _ (cohomologyMapAlong_cohomologyπ _ _ _ _)
  have hint : ∀ g h : G, ∃ n : ℤ, (n : ℚ) = q h - q (g * h) + q g := fun g h => ⟨_, hzq g h⟩
  have hqloc : IsLocallyConstant (fun g : Fin 1 → G => (q (g 0) : (GroundTheory.GroupCoh.ratSES G).X₂)) :=
    hq.comp_continuous (continuous_apply 0)

  have hδ : (δ (GroundTheory.GroupCoh.ratSES_shortExact G) 1 2 rfl).hom
      (cohomologyπ _ 1 (ratModIntCocycle q hq hint)) = cohomologyπ _ 2 z₂ := by
    refine δ_cohomologyπ_of_lift (GroundTheory.GroupCoh.ratSES_shortExact G) rfl _
      (mkCochain (GroundTheory.GroupCoh.ratSES G).X₂ _ hqloc) ?_ z₂ ?_
    · apply cochainOf_injective
      funext u
      exact (cochainOf_ratModIntCocycle q hq hint u).symm
    · apply cochainOf_injective
      funext u
      have e1 := congrFun (cochainOf_d (A := (GroundTheory.GroupCoh.ratSES G).X₂)
        (mkCochain (GroundTheory.GroupCoh.ratSES G).X₂ _ hqloc)) u
      rw [inhomogeneousCochains_d_one_apply] at e1
      have hu : u = ![u 0, u 1] := by
        funext i
        fin_cases i <;> rfl
      have e := hzq (u 0) (u 1)
      rw [← hu, ← hz₂] at e
      exact e.trans e1.symm
  have h2 : cohomologyTwoIntAddEquiv G (cohomologyπ _ 2 z₂) =
      locallyConstantHomQZEquiv G ((cohomologyOneIsoOfIsTrivial G (AddCircle (1 : ℚ))).hom.hom
        (cohomologyπ _ 1 (ratModIntCocycle q hq hint))) := by
    have hδ' : (cohomologyOneRatModIntIsoTwoInt G).inv.hom (cohomologyπ _ 2 z₂) =
        cohomologyπ _ 1 (ratModIntCocycle q hq hint) := by
      rw [← hδ]
      exact (cohomologyOneRatModIntIsoTwoInt G).hom_inv_id_apply _
    change (cohomologyOneRatModIntIso G).hom.hom ((cohomologyOneRatModIntIsoTwoInt G).inv.hom
      (cohomologyπ _ 2 z₂)) = _
    rw [hδ']
    rfl
  rw [h1, h2, locallyConstantHomQZEquiv_apply, cohomologyOneIsoOfIsTrivial_hom_cohomologyπ]
  exact congrArg QZ.toAddCircle.symm (cochainOf_ratModIntCocycle q hq hint fun _ => g)

theorem exists_rat_coboundary (z : cocycles (trivRep G ℤ) 2) :
    ∃ q : G → ℚ, IsLocallyConstant q ∧
      ∀ g h : G, ((cochainOf _ (cocycleι _ 2 z) ![g, h] : ℤ) : ℚ) = q h - q (g * h) + q g := by
  let zq := cocyclesMapAlong (MonoidHom.id G) continuous_id
    (trivRepToTrivial G ≫ GroundTheory.GroupCoh.intToRat G) 2 (cocyclesULiftInt _ z)
  have hz : cohomologyπ _ 2 zq = 0 :=
    (ModuleCat.isZero_iff_subsingleton.1 (isZero_cohomology_trivial_rat (G := G) (by norm_num))).elim _ _
  obtain ⟨w, hw, hwz⟩ := (cohomologyπ_two_eq_zero_iff_locallyConstant _ zq).1 hz
  refine ⟨fun g => w fun _ => g, hw.comp_continuous (continuous_pi fun _ => continuous_id), fun g h => ?_⟩
  have e := hwz ![g, h]
  rw [cochainOf_cocycleι_cocyclesMapAlong, cochainOf_cocycleι_cocyclesULiftInt] at e
  exact e

theorem gvChar_cohomologyMapAlong_eq_zero {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (φ : G →* H) (hφ : Continuous φ) {A : Rep.{0} (ULift.{0} ℤ) H} [IsDiscreteRep A]
    (y : cohomology A 2) (f : Rep.res φ A ⟶ trivRep G ℤ) (g : G) (hg : φ g = 1) :
    gvChar G ((cohomologyMapAlong φ hφ f 2).hom y) (Additive.ofMul g) = 0 := by
  obtain ⟨y', rfl⟩ := cohomologyπ_surjective A 2 y
  rw [cohomologyMapAlong_cohomologyπ]
  obtain ⟨q, hq, hzq⟩ := exists_rat_coboundary (cocyclesMapAlong φ hφ f 2 y')
  rw [gvChar_cohomologyπ _ q hq hzq g, QZ.mk_eq_zero_iff]

  set κ : ℚ := ((cochainOf _ (cocycleι _ 2 (cocyclesMapAlong φ hφ f 2 y')) ![1, 1] : ℤ) : ℚ) with hκ
  have hconst : ∀ a b : G, φ a = 1 → φ b = 1 →
      ((cochainOf _ (cocycleι _ 2 (cocyclesMapAlong φ hφ f 2 y')) ![a, b] : ℤ) : ℚ) = κ := by
    intro a b ha hb
    rw [hκ, cochainOf_cocycleι_cocyclesMapAlong]
    have : (⇑φ ∘ ![a, b]) = ⇑φ ∘ ![(1 : G), 1] := by
      funext i
      fin_cases i
      · simp [ha]
      · simp [hb]
    simp only [this]
  have h1 : q 1 = κ := by
    have := hzq 1 1
    rw [hconst 1 1 (map_one φ) (map_one φ), mul_one] at this
    linarith
  have hpow : ∀ m : ℕ, q (g ^ m) - κ = m * (q g - κ) := by
    intro m
    induction m with
    | zero => simp [h1]
    | succ m ih =>
      have := hzq (g ^ m) g
      rw [hconst _ _ (by rw [map_pow, hg, one_pow]) hg, ← pow_succ] at this
      push_cast
      linarith
  have hfin : (Set.range q).Finite := hq.range_finite
  by_contra hne
  have hne' : q g - κ ≠ 0 := by
    intro h
    exact hne ⟨(cochainOf _ (cocycleι _ 2 (cocyclesMapAlong φ hφ f 2 y')) ![1, 1] : ℤ), by
      rw [← hκ]; linarith⟩
  have hinj : Function.Injective fun m : ℕ => q (g ^ m) := by
    intro m m' hmm
    have e1 := hpow m
    have e2 := hpow m'
    simp only at hmm
    rw [hmm] at e1
    have : (m : ℚ) * (q g - κ) = m' * (q g - κ) := by rw [← e1, ← e2]
    exact_mod_cast mul_right_cancel₀ hne' this
  exact Set.infinite_range_of_injective hinj (hfin.subset (Set.range_comp_subset_range _ _))

end Characters

section Unramified

open GroundTheory.LocalField ValuativeRel FiniteSubfield GroundTheory.Global.SemiLocal

variable {K : FiniteSubfield} {v : HeightOneSpectrum (𝓞 K.1)}
  (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1))

set_option maxHeartbeats 4000000 in

theorem compField_le_maximalUnramifiedExtension (N : FiniteSubfield) [Fact (K ≤ N)] [Normal K.1 N.1]
    (he : (placeOfEmbedding ι N).1.asIdeal.ramificationIdx (𝓞 K.1) = 1) :
    compField ι N ≤ maximalUnramifiedExtension (v.adicCompletion K.1)
      (AlgebraicClosure (v.adicCompletion K.1)) := by
  let := algebraicValuativeRel (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))
  let := algebraicTopology (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))
  have := algebraicTopology_isValuativeTopology (v.adicCompletion K.1)
    (AlgebraicClosure (v.adicCompletion K.1))
  have := algebraicValuativeRel_valuativeExtension (v.adicCompletion K.1)
    (AlgebraicClosure (v.adicCompletion K.1))
  refine ((isUnramifiedSubextension_iff' (compField ι N)).2 ?_).le_maximalUnramifiedExtension
  have hM : ramificationIndex (v.adicCompletion K.1)
      ((placeOfEmbedding ι N).1.adicCompletion N.1) = 1 :=
    (ramificationIdx_integer v (placeOfEmbedding ι N).1).trans he
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[v.adicCompletion K.1]
  have h1 := ord_algebraMap_uniformizer (K := v.adicCompletion K.1)
    (L := (placeOfEmbedding ι N).1.adicCompletion N.1) hϖ
  have h2 := ord_algebraMap_uniformizer (K := v.adicCompletion K.1) (L := compField ι N) hϖ
  have hj : ∀ x y : (placeOfEmbedding ι N).1.adicCompletion N.1,
      (compEquiv ι N).toRingEquiv x ≤ᵥ (compEquiv ι N).toRingEquiv y ↔ x ≤ᵥ y :=
    vle_map_iff (compEquiv ι N).toAlgHom
  have hϖ0 : algebraMap (v.adicCompletion K.1) ((placeOfEmbedding ι N).1.adicCompletion N.1)
      (ϖ : v.adicCompletion K.1) ≠ 0 :=
    (map_ne_zero _).2 (by exact_mod_cast hϖ.ne_zero)
  have h3 := ord_apply_of_vle (compEquiv ι N).toRingEquiv hj (Units.mk0 _ hϖ0)
  have h4 : (compEquiv ι N).toRingEquiv (algebraMap (v.adicCompletion K.1)
      ((placeOfEmbedding ι N).1.adicCompletion N.1) (ϖ : v.adicCompletion K.1)) =
      algebraMap (v.adicCompletion K.1) (compField ι N) (ϖ : v.adicCompletion K.1) :=
    (compEquiv ι N).commutes _
  rw [Units.val_mk0, h4, h2, h1, hM] at h3
  exact_mod_cast h3

end Unramified

section Degree

open GroundTheory.LocalField FiniteSubfield

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) {v : HeightOneSpectrum (𝓞 K.1)}
  (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1)) (hv : v ∉ S)

include hv in

theorem decompHomS_eq_one_of_unramifiedDegree_eq_one
    (g : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1))
    (hg : unramifiedDegree (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) g = 1) :
    decompHomS (v.adicCompletion K.1) S ι g = 1 := by
  have hfix : g ∈ (maximalUnramifiedExtension (v.adicCompletion K.1)
      (AlgebraicClosure (v.adicCompletion K.1))).fixingSubgroup := by
    rw [← ker_unramifiedDegree]
    exact hg
  apply AlgEquiv.ext
  intro y
  obtain ⟨N, hKN, hNG, hN, hyN⟩ := exists_galois_level S y.2
  have hNn : Normal K.1 N.1 := hNG.to_normal
  have hU : Algebra.IsUnramifiedAt (𝓞 K.1) (placeOfEmbedding ι N).1.asIdeal :=
    isUnramifiedIn_of_subset_max S hv N hN _ inferInstance (placeOfEmbedding ι N).2
  have he : (placeOfEmbedding ι N).1.asIdeal.ramificationIdx (𝓞 K.1) = 1 :=
    Ideal.ramificationIdx_eq_one _ _
  have hmem : ι (y : ℚ̄) ∈ maximalUnramifiedExtension (v.adicCompletion K.1)
      (AlgebraicClosure (v.adicCompletion K.1)) :=
    compField_le_maximalUnramifiedExtension ι N he (ι_mem_compField ι N ⟨y, hyN⟩)
  have h1 := decompHom_apply (Kv := v.adicCompletion K.1) (ι.comp (maxUnramifiedOutside K.1 ℚ̄ S).val) g y
  have h2 : g (ι (y : ℚ̄)) = ι (y : ℚ̄) := hfix ⟨_, hmem⟩
  apply Subtype.val_injective
  apply ι.injective
  exact h1.trans h2

set_option maxHeartbeats 2000000 in
include hv in

theorem eq_zero_of_decompHomS_of_unramifiedDegree
    (χ : Additive Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1) →ₜ+ QZ)
    (hχ : ∀ g, decompHomS (v.adicCompletion K.1) S ι g = 1 → χ (Additive.ofMul g) = 0)
    (σ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1))
    (hσ : unramifiedDegree (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) σ =
      Multiplicative.ofAdd 1)
    (h0 : χ (Additive.ofMul σ) = 0) : χ = 0 := by
  let Z : Set Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1) :=
    {g | χ (Additive.ofMul g) = 0}
  have hZc : IsClosed Z :=
    (isClosed_discrete ({0} : Set QZ)).preimage (χ.continuous.comp continuous_ofMul)
  have hT : IsClosed (unramifiedDegree (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) '' Z) :=
    (hZc.isCompact.image continuous_unramifiedDegree).isClosed
  have hpow : (Subgroup.zpowers (Multiplicative.ofAdd (1 : GroundTheory.LocalField.Abstract.ProfiniteInteger)) :
      Set (Multiplicative GroundTheory.LocalField.Abstract.ProfiniteInteger)) ⊆
      unramifiedDegree (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) '' Z := by
    rintro _ ⟨n, rfl⟩
    refine ⟨σ ^ n, ?_, ?_⟩
    · change χ (Additive.ofMul (σ ^ n)) = 0
      rw [ofMul_zpow, map_zsmul, h0, smul_zero]
    · rw [map_zpow, hσ]
  have huniv : unramifiedDegree (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) '' Z =
      Set.univ := by
    have hd := dense_zpowers_ofAdd_one.mono hpow
    rw [← hT.closure_eq, hd.closure_eq]
  ext x
  obtain ⟨k, hk, hdk⟩ : unramifiedDegree (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))
      (Additive.toMul x) ∈ unramifiedDegree (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) '' Z := by
    rw [huniv]
    exact Set.mem_univ _
  have h1 : unramifiedDegree (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))
      (k⁻¹ * Additive.toMul x) = 1 := by
    have e1 := map_mul (unramifiedDegree (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)))
      k⁻¹ (Additive.toMul x)
    have e2 := map_inv (unramifiedDegree (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))) k
    rw [e1, e2, hdk, inv_mul_cancel]
  have h2 := hχ _ (decompHomS_eq_one_of_unramifiedDegree_eq_one S ι hv _ h1)
  have hx : x = Additive.ofMul k + Additive.ofMul (k⁻¹ * Additive.toMul x) := by
    rw [← ofMul_mul, mul_inv_cancel_left, ofMul_toMul]
  rw [hx, map_add, h2, add_zero]
  exact hk

theorem gvChar_decompHomS_eq_zero {A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)} [IsDiscreteRep A]
    (y : cohomology A 2)
    (f : Rep.res (decompHomS (v.adicCompletion K.1) S ι) A ⟶
      trivRep Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1) ℤ)
    (g : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1))
    (hg : decompHomS (v.adicCompletion K.1) S ι g = 1) :
    gvChar _ ((cohomologyMapAlong (decompHomS (v.adicCompletion K.1) S ι)
      (continuous_decompHomS (Kv := v.adicCompletion K.1) S ι) f 2).hom y) (Additive.ofMul g) = 0 :=
  gvChar_cohomologyMapAlong_eq_zero _ _ y f g hg

theorem exists_unramifiedDegree_eq_one :
    ∃ σ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1),
      unramifiedDegree (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) σ =
        Multiplicative.ofAdd 1 :=
  unramifiedDegree_surjective _

end Degree

end

end GroundTheory.ProfCoh
