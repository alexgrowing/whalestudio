import Mathlib
import GroundTheory.GlobalFields.NormResidueSymbol.CyclotomicCompositum
import GroundTheory.GlobalFields.IdeleGroups.NormOneCompact
import GroundTheory.GlobalFields.CyclotomicCharacters.Degree
import GroundTheory.GlobalFields.NormResidueSymbol.RationalContinuous

namespace GroundTheory.Global

open NumberField IntermediateField IdeleGroup
open scoped GroundTheory.LocalField.Abstract

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

namespace CyclotomicSymbol

open FiniteSubfield RationalSymbol _root_.GroundTheory.Global.Cyclotomic

abbrev layer (m : ℕ+) : FiniteSubfield :=
  ⟨rootsOfUnityField m, inferInstance⟩

theorem rootsOfUnityField_le_mul (m n : ℕ+) :
    rootsOfUnityField m ≤ rootsOfUnityField (m * n : ℕ+) :=
  adjoin.mono ℚ _ _ fun x (hx : x ^ (m : ℕ) = 1) ↦ by
    change x ^ ((m * n : ℕ+) : ℕ) = 1
    rw [PNat.mul_coe, pow_mul, hx, one_pow]

def AgreesOn (m : ℕ+) (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) (τ : maxCyclotomic ≃ₐ[ℚ] maxCyclotomic) : Prop :=
  ∀ z (hz : z ∈ rootsOfUnityField m), g z = (τ ⟨z, rootsOfUnityField_le_maxCyclotomic m hz⟩ : ℚ̄)

theorem AgreesOn.of_mul {m n : ℕ+} {g : ℚ̄ ≃ₐ[ℚ] ℚ̄} {τ : maxCyclotomic ≃ₐ[ℚ] maxCyclotomic}
    (h : AgreesOn (m * n) g τ) : AgreesOn m g τ :=
  fun z hz ↦ h z (rootsOfUnityField_le_mul m n hz)

theorem agreesOn_iff (m : ℕ+) (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) (x : IdeleGroup ℚ) :
    AgreesOn m g (reciprocityMap (IdeleClassGroup.mk ℚ x)) ↔
      g.restrictNormal (rootsOfUnityField m) = ideleSymbol ℚ (rootsOfUnityField m) x := by
  constructor
  · intro h
    refine AlgEquiv.ext fun y ↦ Subtype.ext ?_
    rw [coe_ideleSymbol_apply]
    exact (AlgEquiv.restrictNormal_commutes g (rootsOfUnityField m) y).trans (h y y.2)
  · intro h z hz
    have h1 := AlgEquiv.restrictNormal_commutes g (rootsOfUnityField m) ⟨z, hz⟩
    rw [h] at h1
    exact h1.symm.trans (coe_ideleSymbol_apply m x ⟨z, hz⟩)

theorem cycRestrict_eq_of_forall_agreesOn {g : ℚ̄ ≃ₐ[ℚ] ℚ̄} {τ : maxCyclotomic ≃ₐ[ℚ] maxCyclotomic}
    (h : ∀ m, AgreesOn m g τ) : cycRestrict g = τ := by
  obtain ⟨σ, rfl⟩ := cycRestrict_surjective τ
  have hfix : σ⁻¹ * g ∈ maxCyclotomic.fixingSubgroup := by
    rw [maxCyclotomic, mem_fixingSubgroup_adjoin_iff]
    rintro ζ ⟨n, hn, hζ⟩
    have h1 := h ⟨n, hn⟩ ζ (subset_adjoin ℚ _ hζ)
    rw [coe_cycRestrict_apply] at h1
    rw [AlgEquiv.mul_apply, h1, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  refine AlgEquiv.ext fun y ↦ Subtype.ext ?_
  rw [coe_cycRestrict_apply, coe_cycRestrict_apply]
  have h2 := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hfix y y.2
  calc g y = σ ((σ⁻¹ * g) y) := by rw [← AlgEquiv.mul_apply, mul_inv_cancel_left]
    _ = σ y := by rw [h2]

theorem isClosed_setOf_restrictNormal_eq (F : FiniteSubfield) [IsGalois ℚ F.1]
    (t : F.1 ≃ₐ[ℚ] F.1) : IsClosed {g : ℚ̄ ≃ₐ[ℚ] ℚ̄ | g.restrictNormal F.1 = t} := by
  by_cases h : ∃ g₀ : ℚ̄ ≃ₐ[ℚ] ℚ̄, g₀.restrictNormal F.1 = t
  · obtain ⟨g₀, hg₀⟩ := h
    have e : {g : ℚ̄ ≃ₐ[ℚ] ℚ̄ | g.restrictNormal F.1 = t} =
        (fun g ↦ g₀⁻¹ * g) ⁻¹' (F.1.fixingSubgroup : Set (ℚ̄ ≃ₐ[ℚ] ℚ̄)) := by
      ext g
      change g.restrictNormal F.1 = t ↔ g₀⁻¹ * g ∈ F.1.fixingSubgroup
      rw [mem_fixingSubgroup_iff_restrictNormal_eq_one]
      change _ ↔ AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := ℚ̄) F.1 (g₀⁻¹ * g) = 1
      rw [map_mul, map_inv]
      change _ ↔ (g₀.restrictNormal F.1)⁻¹ * g.restrictNormal F.1 = 1
      rw [hg₀, inv_mul_eq_one, eq_comm]
    rw [e]
    exact F.1.fixingSubgroup_isClosed.preimage (continuous_const.mul continuous_id)
  · push Not at h
    have e : {g : ℚ̄ ≃ₐ[ℚ] ℚ̄ | g.restrictNormal F.1 = t} = ∅ :=
      Set.eq_empty_of_forall_notMem fun g hg ↦ h g hg
    rw [e]
    exact isClosed_empty

variable (K : FiniteSubfield)

def cycSymbol : IdeleClassGroup K.1 →* (maxCyclotomic ≃ₐ[ℚ] maxCyclotomic) :=
  reciprocityMap.comp (ideleClassNorm ℚ K.1)

theorem cycSymbol_mk (x : IdeleGroup K.1) :
    cycSymbol K (IdeleClassGroup.mk K.1 x) =
      reciprocityMap (IdeleClassGroup.mk ℚ (ideleNorm ℚ K.1 x)) := by
  rw [cycSymbol, MonoidHom.comp_apply, ideleClassNorm_mk]

theorem continuous_cycSymbol : Continuous (cycSymbol K) :=
  continuous_reciprocityMap.comp (continuous_ideleClassNorm (K := ℚ) (L := K.1))

theorem range_diagonal_le_ker_layer (m : ℕ+) :
    (diagonal ℚ).range ≤ (ideleSymbol ℚ (rootsOfUnityField m)).ker := by
  rintro _ ⟨a, rfl⟩
  exact RationalSymbol.ideleSymbol_diagonal_eq_one _ {(m : ℕ)} a

def layerSymbol (m : ℕ+) :
    IdeleClassGroup K.1 →* (rootsOfUnityField m ≃ₐ[ℚ] rootsOfUnityField m) :=
  (ideleClassSymbol (K := ℚ) (rootsOfUnityField m) (range_diagonal_le_ker_layer m)).comp
    (ideleClassNorm ℚ K.1)

theorem layerSymbol_mk (m : ℕ+) (x : IdeleGroup K.1) :
    layerSymbol K m (IdeleClassGroup.mk K.1 x) =
      ideleSymbol ℚ (rootsOfUnityField m) (ideleNorm ℚ K.1 x) := by
  rw [layerSymbol, MonoidHom.comp_apply, ideleClassNorm_mk, ideleClassSymbol_mk]

theorem continuous_layerSymbol (m : ℕ+) : Continuous (layerSymbol K m) :=
  (continuous_ideleClassSymbol (range_diagonal_le_ker_layer m)).comp
    (continuous_ideleClassNorm (K := ℚ) (L := K.1))

theorem agreesOn_cycSymbol_iff (m : ℕ+) (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) (c : IdeleClassGroup K.1) :
    AgreesOn m g (cycSymbol K c) ↔ g.restrictNormal (rootsOfUnityField m) = layerSymbol K m c := by
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K.1 c
  rw [cycSymbol_mk, layerSymbol_mk, agreesOn_iff]

section Positive

variable {F : Type*} [Field F] [NumberField F]

theorem exists_infiniteEmbedding_ideleModule_eq (t : {r : ℝ // 0 < r}) :
    ∃ (w : InfinitePlace F) (z : (w.Completion)ˣ),
      IdeleGroup.ideleModule F (infiniteEmbedding w z) = t ∧
        ∀ hw : w.IsReal, 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (z : w.Completion) := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨t, ht⟩ := t
  rcases w.isReal_or_isComplex with hw | hw
  · let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
    have hz0 : e.symm t ≠ 0 := (map_ne_zero_iff _ e.symm.injective).2 ht.ne'
    have he : InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (e.symm t) = t := by
      rw [← InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
      exact e.apply_symm_apply t
    refine ⟨w, Units.mk0 (e.symm t) hz0, Subtype.ext ?_, fun _ ↦ ?_⟩
    · rw [ideleModule_infiniteEmbedding, Units.val_mk0]
      have hn : ‖e.symm t‖ = ‖e (e.symm t)‖ := by
        rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
        exact ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
          (map_zero _) _).symm
      rw [hn, RingEquiv.apply_symm_apply, Real.norm_of_nonneg ht.le]
      simp [InfinitePlace.mult, hw]
    · rw [Units.val_mk0, he]
      exact ht
  · let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
    have hz0 : e.symm (Real.sqrt t : ℂ) ≠ 0 :=
      (map_ne_zero_iff _ e.symm.injective).2 (Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 ht))
    have hw' : ¬ w.IsReal := InfinitePlace.not_isReal_iff_isComplex.2 hw
    refine ⟨w, Units.mk0 _ hz0, Subtype.ext ?_, fun h ↦ absurd h hw'⟩
    rw [ideleModule_infiniteEmbedding, Units.val_mk0]
    have hn : ‖e.symm (Real.sqrt t : ℂ)‖ = ‖e (e.symm (Real.sqrt t : ℂ))‖ := by
      rw [InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply]
      exact ((InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
        (map_zero _) _).symm
    rw [hn, RingEquiv.apply_symm_apply, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg t)]
    simp [InfinitePlace.mult, hw', Real.sq_sqrt ht.le]

theorem ideleSymbol_infiniteEmbedding_eq_one (L : Type*) [Field L] [NumberField L] [Algebra F L]
    [IsGalois F L] [IsMulCommutative (L ≃ₐ[F] L)] (w : InfinitePlace F) (z : (w.Completion)ˣ)
    (hz : ∀ hw : w.IsReal, 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (z : w.Completion)) :
    ideleSymbol F L (infiniteEmbedding w z) = 1 := by
  rw [ideleSymbol_infiniteEmbedding]
  by_cases hw : w.IsReal
  · obtain ⟨w'⟩ := IdeleNorm.nonempty_infinitePlacesOver L w
    rw [infiniteLocalSymbol_apply L w hw w' z, if_neg (not_lt.2 (hz hw).le)]
  · rw [infiniteLocalSymbol_of_not_isReal L w hw, MonoidHom.one_apply]

end Positive

theorem ideleSymbol_ideleNorm_eq_one (F : FiniteSubfield) [IsGalois ℚ F.1]
    [IsMulCommutative (F.1 ≃ₐ[ℚ] F.1)] {x : IdeleGroup K.1}
    (h : ideleSymbol K.1 (compositum K F).1 x = 1) : ideleSymbol ℚ F.1 (ideleNorm ℚ K.1 x) = 1 := by
  rw [ideleSymbol_ideleNorm, h]
  exact map_one (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := (compositum K F).1) F.1)

theorem exists_mem_fixingSubgroup_cycRestrict_eq (c : IdeleClassGroup K.1) :
    ∃ g ∈ K.1.fixingSubgroup, cycRestrict g = cycSymbol K c := by
  have : IsGalois ℚ ℚ̄ := IsAlgClosure.isGalois ℚ ℚ̄
  let t : ℕ+ → Set (ℚ̄ ≃ₐ[ℚ] ℚ̄) := fun m ↦ (K.1.fixingSubgroup : Set (ℚ̄ ≃ₐ[ℚ] ℚ̄)) ∩
    {g | g.restrictNormal (rootsOfUnityField m) = layerSymbol K m c}
  have hcl : ∀ m, IsClosed (t m) := fun m ↦ K.1.fixingSubgroup_isClosed.inter
    (isClosed_setOf_restrictNormal_eq (layer m) _)
  have hne : ∀ m, (t m).Nonempty := fun m ↦ by
    obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K.1 c
    obtain ⟨g, hg, h⟩ := exists_restrictNormal_eq_ideleSymbol K (layer m) x
    refine ⟨g, hg, ?_⟩
    change g.restrictNormal (rootsOfUnityField m) = _
    rw [layerSymbol_mk]
    exact h
  have hdir : Directed (· ⊇ ·) t := fun m n ↦ by
    refine ⟨m * n, fun g hg ↦ ⟨hg.1, ?_⟩, fun g hg ↦ ⟨hg.1, ?_⟩⟩
    · exact (agreesOn_cycSymbol_iff K m g c).1 ((agreesOn_cycSymbol_iff K _ g c).2 hg.2).of_mul
    · have h := (agreesOn_cycSymbol_iff K _ g c).2 hg.2
      rw [mul_comm] at h
      exact (agreesOn_cycSymbol_iff K n g c).1 h.of_mul
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t hdir hne
    (fun m ↦ (hcl m).isCompact) hcl
  rw [Set.mem_iInter] at hg
  exact ⟨g, (hg 1).1,
    cycRestrict_eq_of_forall_agreesOn fun m ↦ (agreesOn_cycSymbol_iff K m g c).2 (hg m).2⟩

theorem exists_cycSymbol_eq {g : ℚ̄ ≃ₐ[ℚ] ℚ̄} (hg : g ∈ K.1.fixingSubgroup) :
    ∃ c : IdeleClassGroup K.1, cycSymbol K c = cycRestrict g := by
  let s : ℕ+ → Set (IdeleClassGroup K.1) := fun m ↦
    (IdeleClassGroup.normOneSubgroup K.1 : Set (IdeleClassGroup K.1)) ∩
      layerSymbol K m ⁻¹' {g.restrictNormal (rootsOfUnityField m)}
  have hone : IsClosed (IdeleClassGroup.normOneSubgroup K.1 : Set (IdeleClassGroup K.1)) :=
    isClosed_singleton.preimage (IdeleClassGroup.continuous_ideleModule K.1)
  have hcl : ∀ m, IsClosed (s m) := fun m ↦
    hone.inter (isClosed_singleton.preimage (continuous_layerSymbol K m))
  have hco : ∀ m, IsCompact (s m) := fun m ↦
    (IdeleClassGroup.isCompact_normOneSubgroup K.1).inter_right
      (isClosed_singleton.preimage (continuous_layerSymbol K m))
  have hne : ∀ m, (s m).Nonempty := fun m ↦ by
    obtain ⟨x, hx⟩ := exists_ideleSymbol_eq_restrictNormal K (layer m) hg
    obtain ⟨w, z, hmod, hpos⟩ := exists_infiniteEmbedding_ideleModule_eq (F := K.1)
      (IdeleGroup.ideleModule K.1 x)
    have he : ideleSymbol ℚ (rootsOfUnityField m) (ideleNorm ℚ K.1 (infiniteEmbedding w z)) = 1 :=
      ideleSymbol_ideleNorm_eq_one K (layer m) (ideleSymbol_infiniteEmbedding_eq_one _ w z hpos)
    refine ⟨IdeleClassGroup.mk K.1 (x * (infiniteEmbedding w z)⁻¹), ?_, ?_⟩
    · change IdeleClassGroup.ideleModule K.1 (IdeleClassGroup.mk K.1 _) = 1
      rw [IdeleClassGroup.ideleModule_mk, map_mul, map_inv, hmod, mul_inv_cancel]
    · change layerSymbol K m _ = _
      rw [layerSymbol_mk, map_mul, map_inv, map_mul, map_inv, he, inv_one, mul_one]
      exact hx
  have hdir : Directed (· ⊇ ·) s := fun m n ↦ by
    refine ⟨m * n, fun c hc ↦ ⟨hc.1, ?_⟩, fun c hc ↦ ⟨hc.1, ?_⟩⟩
    · have h := (agreesOn_cycSymbol_iff K _ g c).2 (Set.mem_singleton_iff.1 hc.2).symm
      exact Set.mem_singleton_iff.2 ((agreesOn_cycSymbol_iff K m g c).1 h.of_mul).symm
    · have h := (agreesOn_cycSymbol_iff K _ g c).2 (Set.mem_singleton_iff.1 hc.2).symm
      rw [mul_comm] at h
      exact Set.mem_singleton_iff.2 ((agreesOn_cycSymbol_iff K n g c).1 h.of_mul).symm
  obtain ⟨c, hc⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed s hdir hne
    hco hcl
  rw [Set.mem_iInter] at hc
  exact ⟨c, (cycRestrict_eq_of_forall_agreesOn fun m ↦
    (agreesOn_cycSymbol_iff K m g c).2 (Set.mem_singleton_iff.1 (hc m).2).symm).symm⟩

theorem range_cycSymbol : (cycSymbol K).range = K.1.fixingSubgroup.map cycRestrict := by
  ext τ
  constructor
  · rintro ⟨c, rfl⟩
    obtain ⟨g, hg, h⟩ := exists_mem_fixingSubgroup_cycRestrict_eq K c
    exact ⟨g, hg, h⟩
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨c, hc⟩ := exists_cycSymbol_eq K hg
    exact ⟨c, hc⟩

def cycDegree : (maxCyclotomic ≃ₐ[ℚ] maxCyclotomic) →* Multiplicative ℤ̂ :=
  unitsDegree.comp cycCharacter.toMonoidHom

theorem cycDegree_comp_cycRestrict : cycDegree.comp cycRestrict = degree := by
  refine MonoidHom.ext fun σ ↦ ?_
  change unitsDegree (cycCharacter (cycRestrict σ)) = degree σ
  rw [degree_apply, cycCharacter_cycRestrict]

theorem map_cycDegree_range_cycSymbol :
    (cycSymbol K).range.map cycDegree = K.1.fixingSubgroup.map degree := by
  rw [range_cycSymbol, Subgroup.map_map, cycDegree_comp_cycRestrict]

end CyclotomicSymbol

end

end GroundTheory.Global
