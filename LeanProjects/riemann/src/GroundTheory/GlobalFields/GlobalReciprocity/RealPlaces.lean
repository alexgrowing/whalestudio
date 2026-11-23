import Mathlib
import GroundTheory.GlobalFields.GlobalReciprocity.NormSquare
import GroundTheory.GlobalFields.GlobalReciprocity.RealPlacesQuadratic
import GroundTheory.GlobalFields.NormResidueSymbol.Functorial

namespace GroundTheory.Global

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion IntermediateField
  GroundTheory.LocalField.Abstract IdeleGroup
open scoped GroundTheory.LocalField.Abstract ComplexConjugate NumberField.LiesOver

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

section SqrtNegOne

theorem conj_eq_neg_of_sq_eq_neg_one {z : ℂ} (hz : z ^ 2 = -1) : conj z = -z := by
  have h : z ^ 2 = Complex.I ^ 2 := by rw [hz, Complex.I_sq]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with rfl | rfl
  · rw [Complex.conj_I]
  · rw [map_neg, Complex.conj_I, neg_neg]

variable {F k : Type*} [Field F] [Field k] [Algebra k F]

theorem isComplex_of_mul_self_eq_neg_one {i : F} (hi : i * i = -1) (w : InfinitePlace F) :
    w.IsComplex := by
  rw [← not_isReal_iff_isComplex]
  intro hw
  have hφ : w.embedding i ^ 2 = -1 := by rw [sq, ← map_mul, hi, map_neg, map_one]
  have h1 := conj_eq_neg_of_sq_eq_neg_one hφ
  have h2 : conj (w.embedding i) = w.embedding i :=
    RingHom.congr_fun (ComplexEmbedding.isReal_iff.1 (isReal_iff.1 hw)) i
  have h3 : w.embedding i = 0 := by
    have h4 : w.embedding i + w.embedding i = 0 := by
      nth_rw 2 [← h2]
      rw [h1, add_neg_cancel]
    rwa [← two_mul, mul_eq_zero, or_iff_right two_ne_zero] at h4
  rw [h3] at hφ
  norm_num at hφ

theorem apply_eq_neg_of_isConj {φ : F →+* ℂ} {σ : F ≃ₐ[k] F} (h : ComplexEmbedding.IsConj φ σ)
    {i : F} (hi : i * i = -1) : σ i = -i := by
  apply φ.injective
  rw [isConj_iff_forall.1 h, map_neg, ← starRingEnd_apply]
  exact conj_eq_neg_of_sq_eq_neg_one (by rw [sq, ← map_mul, hi, map_neg, map_one])

end SqrtNegOne

section FixedField

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

theorem mem_fixedField_zpowers (τ : E ≃ₐ[F] E) (x : E) :
    x ∈ fixedField (Subgroup.zpowers τ) ↔ τ x = x := by
  rw [mem_fixedField_iff]
  refine ⟨fun h ↦ h τ (Subgroup.mem_zpowers τ), fun h f hf ↦ ?_⟩
  have hle : Subgroup.zpowers τ ≤ MulAction.stabilizer (E ≃ₐ[F] E) x :=
    Subgroup.zpowers_le.2 (by rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]; exact h)
  have h' := hle hf
  rwa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at h'

end FixedField

namespace IdeleClassLimit

open FiniteSubfield

section Fixed

variable {K E : FiniteSubfield} [Fact (K ≤ E)] (τ : E.1 ≃ₐ[K.1] E.1)

def fixedSubfield : FiniteSubfield :=
  ⟨IntermediateField.lift ((fixedField (Subgroup.zpowers τ)).restrictScalars ℚ),
    FiniteDimensional.of_injective
      (IntermediateField.inclusion (IntermediateField.lift_le _)).toLinearMap
      fun _ _ h ↦ (IntermediateField.inclusion (IntermediateField.lift_le _)).injective h⟩

theorem mem_fixedSubfield {x : ℚ̄} :
    x ∈ (fixedSubfield τ).1 ↔ ∃ h : x ∈ E.1, τ ⟨x, h⟩ = ⟨x, h⟩ := by
  change x ∈ IntermediateField.lift ((fixedField (Subgroup.zpowers τ)).restrictScalars ℚ) ↔ _
  constructor
  · intro hx
    have h : x ∈ E.1 := IntermediateField.lift_le _ hx
    refine ⟨h, (mem_fixedField_zpowers τ _).1 ?_⟩
    have h' := (IntermediateField.mem_lift (E := (fixedField (Subgroup.zpowers τ)).restrictScalars ℚ)
      (⟨x, h⟩ : E.1)).1 hx
    exact (IntermediateField.mem_restrictScalars ℚ).1 h'
  · rintro ⟨h, hx⟩
    exact (IntermediateField.mem_lift (E := (fixedField (Subgroup.zpowers τ)).restrictScalars ℚ)
      (⟨x, h⟩ : E.1)).2 ((IntermediateField.mem_restrictScalars ℚ).2
        ((mem_fixedField_zpowers τ _).2 hx))

theorem fixedSubfield_le : fixedSubfield τ ≤ E :=
  show (fixedSubfield τ).1 ≤ E.1 from IntermediateField.lift_le _

theorem le_fixedSubfield : K ≤ fixedSubfield τ := fun x hx ↦
  (mem_fixedSubfield τ).2 ⟨(Fact.out : K ≤ E) hx, τ.commutes (⟨x, hx⟩ : K.1)⟩

instance fact_fixedSubfield_le : Fact (fixedSubfield τ ≤ E) :=
  ⟨fixedSubfield_le τ⟩

instance fact_le_fixedSubfield : Fact (K ≤ fixedSubfield τ) :=
  ⟨le_fixedSubfield τ⟩

theorem apply_algebraMap_fixedSubfield (s : (fixedSubfield τ).1) :
    τ (algebraMap (fixedSubfield τ).1 E.1 s) = algebraMap (fixedSubfield τ).1 E.1 s := by
  obtain ⟨_, hs⟩ := (mem_fixedSubfield τ).1 s.2
  exact hs

theorem exists_algebraMap_eq_of_apply_eq {e : E.1} (he : τ e = e) :
    ∃ s : (fixedSubfield τ).1, algebraMap (fixedSubfield τ).1 E.1 s = e :=
  ⟨⟨e.1, (mem_fixedSubfield τ).2 ⟨e.2, he⟩⟩, rfl⟩

variable {τ} (hτ : τ * τ = 1) {i : E.1} (hi : i * i = -1) (hτi : τ i = -i)
include hτ hi hτi

theorem exists_eq_add_mul (e : E.1) : ∃ s t : (fixedSubfield τ).1,
    algebraMap (fixedSubfield τ).1 E.1 s + i * algebraMap (fixedSubfield τ).1 E.1 t = e := by
  have hττ : ∀ x, τ (τ x) = x := fun x ↦ by rw [← AlgEquiv.mul_apply, hτ, AlgEquiv.one_apply]
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [mul_zero, zero_eq_neg] at hi
    exact one_ne_zero hi
  have h2 : (2 : E.1) ≠ 0 := two_ne_zero
  obtain ⟨s, hs⟩ := exists_algebraMap_eq_of_apply_eq τ (e := (e + τ e) / 2) (by
    rw [map_div₀, map_add, hττ, map_ofNat, add_comm])
  obtain ⟨t, ht⟩ := exists_algebraMap_eq_of_apply_eq τ (e := (e - τ e) / (2 * i)) (by
    rw [map_div₀, map_sub, map_mul, hττ, hτi, map_ofNat]
    field_simp
    ring)
  refine ⟨s, t, ?_⟩
  rw [hs, ht]
  field_simp
  ring

theorem apply_eq_or_eq_neg (σ : E.1 ≃ₐ[(fixedSubfield τ).1] E.1) : σ i = i ∨ σ i = -i := by
  have h : σ i * σ i = i * i := by rw [← map_mul, hi, map_neg, map_one]
  exact mul_self_eq_mul_self_iff.1 h

theorem galFixed_ext {σ ρ : E.1 ≃ₐ[(fixedSubfield τ).1] E.1} (h : σ i = ρ i) : σ = ρ := by
  ext e
  obtain ⟨s, t, rfl⟩ := exists_eq_add_mul hτ hi hτi e
  simp only [map_add, map_mul, AlgEquiv.commutes, h]

theorem natCard_galFixed_le_two : Nat.card (E.1 ≃ₐ[(fixedSubfield τ).1] E.1) ≤ 2 := by
  classical
  have hinj : Function.Injective
      (fun σ : E.1 ≃ₐ[(fixedSubfield τ).1] E.1 ↦ decide (σ i = i)) := by
    intro σ ρ h
    apply galFixed_ext hτ hi hτi
    by_cases hσ : σ i = i
    · have hρ : ρ i = i := by simpa [hσ] using h.symm
      rw [hσ, hρ]
    · have hρ : ¬ ρ i = i := by simpa [hσ] using h.symm
      rw [(apply_eq_or_eq_neg hτ hi hτi σ).resolve_left hσ,
        (apply_eq_or_eq_neg hτ hi hτi ρ).resolve_left hρ]
  have h := Nat.card_le_card_of_injective _ hinj
  simpa using h

theorem isMulCommutative_galFixed : IsMulCommutative (E.1 ≃ₐ[(fixedSubfield τ).1] E.1) :=
  ⟨⟨fun σ ρ ↦ galFixed_ext hτ hi hτi (by
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply]
    rcases apply_eq_or_eq_neg hτ hi hτi σ with h1 | h1 <;>
      rcases apply_eq_or_eq_neg hτ hi hτi ρ with h2 | h2 <;>
      simp only [h1, h2, map_neg, neg_neg])⟩⟩

theorem le_fixedSubfield_sup_maxCyclotomic :
    E.1 ≤ (fixedSubfield τ).1 ⊔ Cyclotomic.maxCyclotomic := by
  intro x hx
  obtain ⟨s, t, hst⟩ := exists_eq_add_mul hτ hi hτi ⟨x, hx⟩
  have hx' : x = (s : ℚ̄) + (i : ℚ̄) * (t : ℚ̄) := congrArg Subtype.val hst.symm
  have hI : (i : ℚ̄) ∈ Cyclotomic.maxCyclotomic := by
    refine subset_adjoin ℚ _ ⟨4, by norm_num, ?_⟩
    have h : (i : ℚ̄) * (i : ℚ̄) = -1 := congrArg Subtype.val hi
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq (i : ℚ̄), h]
    norm_num
  rw [hx']
  exact add_mem (le_sup_left (a := (fixedSubfield τ).1) s.2)
    (mul_mem (le_sup_right (a := (fixedSubfield τ).1) hI) (le_sup_left (a := (fixedSubfield τ).1) t.2))

omit hτ hi hτi in

theorem isReal_comap_fixedSubfield {w : InfinitePlace E.1}
    (hτw : ComplexEmbedding.IsConj w.embedding τ) :
    (w.comap (algebraMap (fixedSubfield τ).1 E.1)).IsReal := by
  rw [← mk_embedding w, comap_mk, isReal_mk_iff, ComplexEmbedding.isReal_iff]
  refine RingHom.ext fun s ↦ ?_
  have h := isConj_iff_forall.1 hτw (algebraMap (fixedSubfield τ).1 E.1 s)
  rw [apply_algebraMap_fixedSubfield] at h
  rw [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, starRingEnd_apply]
  exact h.symm

theorem ideleSymbol_infiniteEmbedding_neg_one_ne_one
    [(E.1.fixingSubgroup.subgroupOf (fixedSubfield τ).1.fixingSubgroup).Normal]
    [IsMulCommutative (E.1 ≃ₐ[(fixedSubfield τ).1] E.1)] {w : InfinitePlace E.1}
    (hτw : ComplexEmbedding.IsConj w.embedding τ) :
    ideleSymbol (fixedSubfield τ).1 E.1
      (infiniteEmbedding (w.comap (algebraMap (fixedSubfield τ).1 E.1)) (-1)) ≠ 1 := by
  have hu := isReal_comap_fixedSubfield hτw
  have hram : w.IsRamified (fixedSubfield τ).1 :=
    isRamified_iff.2 ⟨isComplex_of_mul_self_eq_neg_one hi w, hu⟩
  rw [ideleSymbol_infiniteEmbedding, infiniteLocalSymbol_apply E.1 _ hu
    ⟨w, (inferInstance : w.LiesOver (w.comap (algebraMap (fixedSubfield τ).1 E.1)))⟩, if_pos]
  · exact conjAt_ne_one hram
  · simp

end Fixed

section Main

variable (K L : FiniteSubfield) [hKL : Fact (K ≤ L)]
  [(L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal] [IsMulCommutative (L.1 ≃ₐ[K.1] L.1)]

theorem abstractSymbol_mk_infiniteEmbedding_comap {E : FiniteSubfield} [Fact (K ≤ E)] [Fact (L ≤ E)]
    {τ : E.1 ≃ₐ[K.1] E.1} (hτ : τ * τ = 1) {i : E.1} (hi : i * i = -1) (hτi : τ i = -i)
    [(E.1.fixingSubgroup.subgroupOf (fixedSubfield τ).1.fixingSubgroup).Normal]
    {w : InfinitePlace E.1} (hτw : ComplexEmbedding.IsConj w.embedding τ)
    (x : ((w.comap (algebraMap (fixedSubfield τ).1 E.1)).comap
      (algebraMap K.1 (fixedSubfield τ).1)).Completionˣ) :
    abstractSymbol K L (IdeleClassGroup.mk K.1 (infiniteEmbedding ((w.comap
      (algebraMap (fixedSubfield τ).1 E.1)).comap (algebraMap K.1 (fixedSubfield τ).1)) x)) =
      Abelianization.of (infiniteLocalSymbol L.1 ((w.comap (algebraMap (fixedSubfield τ).1 E.1)).comap
        (algebraMap K.1 (fixedSubfield τ).1)) x) := by
  have := isMulCommutative_galFixed hτ hi hτi
  have hu := isReal_comap_fixedSubfield hτw
  have hfin : Module.finrank ((w.comap (algebraMap (fixedSubfield τ).1 E.1)).comap
      (algebraMap K.1 (fixedSubfield τ).1)).Completion
      (w.comap (algebraMap (fixedSubfield τ).1 E.1)).Completion = 1 :=
    (GroundTheory.Global.InfinitePlace.finrank_completion_eq_one_iff _).2
      fun h ↦ not_isComplex_iff_isReal.2 hu h.2
  let y : (w.comap (algebraMap (fixedSubfield τ).1 E.1)).Completionˣ :=
    Units.map (algebraMap ((w.comap (algebraMap (fixedSubfield τ).1 E.1)).comap
      (algebraMap K.1 (fixedSubfield τ).1)).Completion
      (w.comap (algebraMap (fixedSubfield τ).1 E.1)).Completion).toMonoidHom x
  have hny : LocalField.normUnits ((w.comap (algebraMap (fixedSubfield τ).1 E.1)).comap
      (algebraMap K.1 (fixedSubfield τ).1)).Completion
      (w.comap (algebraMap (fixedSubfield τ).1 E.1)).Completion y = x := by
    apply Units.ext
    rw [LocalField.coe_normUnits]
    change Algebra.norm _ (algebraMap _ _ (x : ((w.comap (algebraMap (fixedSubfield τ).1 E.1)).comap
      (algebraMap K.1 (fixedSubfield τ).1)).Completion)) = _
    rw [Algebra.norm_algebraMap, hfin, pow_one]
  have e1 : infiniteEmbedding ((w.comap (algebraMap (fixedSubfield τ).1 E.1)).comap
      (algebraMap K.1 (fixedSubfield τ).1)) x =
      ideleNorm K.1 (fixedSubfield τ).1
        (infiniteEmbedding (w.comap (algebraMap (fixedSubfield τ).1 E.1)) y) := by
    rw [ideleNorm_infiniteEmbedding, hny]
  have hsym := abstractSymbol_mk_of_natCard_le_two (fixedSubfield τ) E
    (natCard_galFixed_le_two hτ hi hτi) (le_fixedSubfield_sup_maxCyclotomic hτ hi hτi)
    (ideleSymbol_infiniteEmbedding_neg_one_ne_one hτ hi hτi hτw)
    (infiniteEmbedding (w.comap (algebraMap (fixedSubfield τ).1 E.1)) y)
  have e2 : IdeleClassGroup.mk K.1 (ideleNorm K.1 (fixedSubfield τ).1
      (infiniteEmbedding (w.comap (algebraMap (fixedSubfield τ).1 E.1)) y)) =
      FiniteSubfield.ideleClassNorm (le_fixedSubfield τ)
        (IdeleClassGroup.mk (fixedSubfield τ).1
          (infiniteEmbedding (w.comap (algebraMap (fixedSubfield τ).1 E.1)) y)) := rfl
  rw [e1, e2, abstractSymbol_ideleClassNorm_eq_map (K' := fixedSubfield τ) (L' := E), hsym,
    Abelianization.map_of, MonoidHom.comp_apply, restrictScalarsHom_apply,
    show ∀ σ : E.1 ≃ₐ[K.1] E.1, AlgEquiv.restrictNormalHom L.1 σ = σ.restrictNormal L.1 from fun _ ↦ rfl,
    restrictNormal_restrictScalars_ideleSymbol, ← e1,
    ideleSymbol_infiniteEmbedding]

theorem abstractSymbol_mk_infiniteEmbedding_of_isReal (v : InfinitePlace K.1) (hv : v.IsReal)
    (x : v.Completionˣ) :
    abstractSymbol K L (IdeleClassGroup.mk K.1 (infiniteEmbedding v x)) =
      Abelianization.of (infiniteLocalSymbol L.1 v x) := by
  obtain ⟨I, hI⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : ℚ̄) two_pos
  have : FiniteDimensional ℚ ℚ⟮I⟯ := adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral I)
  let F₀ : FiniteSubfield := ⟨L.1 ⊔ ℚ⟮I⟯, inferInstance⟩
  have hF₀E : F₀ ≤ galoisClosure F₀ := le_galoisClosure F₀
  have hLE : L ≤ galoisClosure F₀ := (show L.1 ≤ L.1 ⊔ ℚ⟮I⟯ from le_sup_left).trans hF₀E
  have hIE : I ∈ (galoisClosure F₀).1 :=
    hF₀E ((show ℚ⟮I⟯ ≤ L.1 ⊔ ℚ⟮I⟯ from le_sup_right) (mem_adjoin_simple_self ℚ I))
  have : Fact (L ≤ galoisClosure F₀) := ⟨hLE⟩
  have : Fact (K ≤ galoisClosure F₀) := ⟨hKL.out.trans hLE⟩
  have hEn : (galoisClosure F₀).1.fixingSubgroup.Normal := by
    change (normalClosure ℚ F₀.1 ℚ̄).fixingSubgroup.Normal
    have : IsGalois ℚ (normalClosure ℚ F₀.1 ℚ̄) := IsGalois.normalClosure ℚ F₀.1 ℚ̄
    exact IsGalois.fixingSubgroup_normal_of_isGalois _
  have : ((galoisClosure F₀).1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal :=
    hEn.subgroupOf _
  let i : (galoisClosure F₀).1 := ⟨I, hIE⟩
  have hi : i * i = -1 := Subtype.ext (by
    change I * I = -1
    rw [← sq, hI])
  obtain ⟨w, hw'⟩ := comap_surjective (k := K.1) (K := (galoisClosure F₀).1) v
  have hw : w.comap (algebraMap K.1 (galoisClosure F₀).1) = v := hw'
  have hram : w.IsRamified K.1 :=
    isRamified_iff.2 ⟨isComplex_of_mul_self_eq_neg_one hi w, by rw [hw]; exact hv⟩
  have hτw : ComplexEmbedding.IsConj w.embedding (conjAt K.1 w) := isConj_conjAt hram
  have hτi : conjAt K.1 w i = -i := apply_eq_neg_of_isConj hτw hi
  have : ((galoisClosure F₀).1.fixingSubgroup.subgroupOf
      (fixedSubfield (conjAt K.1 w)).1.fixingSubgroup).Normal := hEn.subgroupOf _
  have hvu : (w.comap (algebraMap (fixedSubfield (conjAt K.1 w)).1 (galoisClosure F₀).1)).comap
      (algebraMap K.1 (fixedSubfield (conjAt K.1 w)).1) = v := by
    rw [← hw, ← comap_comp, ← IsScalarTower.algebraMap_eq]
  subst hvu
  exact abstractSymbol_mk_infiniteEmbedding_comap K L (conjAt_mul_self w) hi hτi hτw x

theorem abstractSymbol_mk_infiniteEmbedding_of_not_isReal (v : InfinitePlace K.1) (hv : ¬ v.IsReal)
    (x : v.Completionˣ) :
    abstractSymbol K L (IdeleClassGroup.mk K.1 (infiniteEmbedding v x)) = 1 := by
  have : Finite (Abelianization (L.1 ≃ₐ[K.1] L.1)) :=
    Finite.of_surjective _ (QuotientGroup.mk_surjective (s := commutator (L.1 ≃ₐ[K.1] L.1)))
  set n := Nat.card (Abelianization (L.1 ≃ₐ[K.1] L.1))
  have hn : 0 < n := Nat.card_pos
  let e := ringEquivComplexOfIsComplex (not_isReal_iff_isComplex.1 hv)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e x) hn
  have hz0 : e.symm z ≠ 0 := by
    intro h
    apply x.ne_zero
    apply e.injective
    rw [map_zero, ← hz, ← e.apply_symm_apply z, h, map_zero, zero_pow hn.ne']
  have hxy : x = Units.mk0 (e.symm z) hz0 ^ n := by
    apply Units.ext
    apply e.injective
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, map_pow, RingEquiv.apply_symm_apply, hz]
  rw [hxy, map_pow, map_pow, map_pow, pow_card_eq_one']

theorem abstractSymbol_mk_infiniteEmbedding (v : InfinitePlace K.1) (x : v.Completionˣ) :
    abstractSymbol K L (IdeleClassGroup.mk K.1 (infiniteEmbedding v x)) =
      Abelianization.of (infiniteLocalSymbol L.1 v x) := by
  by_cases hv : v.IsReal
  · exact abstractSymbol_mk_infiniteEmbedding_of_isReal K L v hv x
  · rw [abstractSymbol_mk_infiniteEmbedding_of_not_isReal K L v hv x,
      infiniteLocalSymbol_of_not_isReal L.1 v hv, MonoidHom.one_apply, map_one]

theorem abstractSymbol_mk_infiniteEmbedding_neg_one (v : InfinitePlace K.1) (hv : v.IsReal)
    (w : InfinitePlace L.1) (hw : w.comap (algebraMap K.1 L.1) = v) :
    abstractSymbol K L (IdeleClassGroup.mk K.1 (infiniteEmbedding v (-1))) =
      Abelianization.of (conjAt K.1 w) := by
  subst hw
  rw [abstractSymbol_mk_infiniteEmbedding_of_isReal K L _ hv,
    infiniteLocalSymbol_apply L.1 _ hv ⟨w, (inferInstance : w.LiesOver _)⟩, if_pos (by simp)]

theorem abstractSymbol_mk_infiniteEmbedding_of_pos (v : InfinitePlace K.1) (hv : v.IsReal)
    (x : v.Completionˣ) (hx : 0 < extensionEmbeddingOfIsReal hv x) :
    abstractSymbol K L (IdeleClassGroup.mk K.1 (infiniteEmbedding v x)) = 1 := by
  obtain ⟨w⟩ := IdeleNorm.nonempty_infinitePlacesOver L.1 v
  rw [abstractSymbol_mk_infiniteEmbedding_of_isReal K L v hv, infiniteLocalSymbol_apply L.1 v hv w,
    if_neg (not_lt.2 hx.le), map_one]

end Main

end IdeleClassLimit

end

end GroundTheory.Global
