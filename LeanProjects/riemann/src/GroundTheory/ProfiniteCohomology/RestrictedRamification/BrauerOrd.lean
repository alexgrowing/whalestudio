import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerDefs
import GroundTheory.ProfiniteCohomology.RestrictedRamification.SDivisor
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalLimits.LiesOver
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.Splitting
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain IntermediateField GroundTheory.Global FiniteSubfield
  GroundTheory.Global.SemiLocal

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield}

variable (K) in

def levelOf (y : ℚ̄) : FiniteSubfield :=
  ⟨K.1 ⊔ IntermediateField.adjoin ℚ {y}, by
    have := K.2
    have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {y}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral y)
    infer_instance⟩

instance fact_le_levelOf (y : ℚ̄) : Fact (K ≤ levelOf K y) := ⟨le_sup_left (a := K.1)⟩

theorem mem_levelOf (y : ℚ̄) : y ∈ (levelOf K y).1 :=
  (le_sup_right (a := K.1) : IntermediateField.adjoin ℚ {y} ≤ (levelOf K y).1)
    (IntermediateField.mem_adjoin_simple_self ℚ y)

def supLevel (F E : FiniteSubfield) : FiniteSubfield :=
  ⟨F.1 ⊔ E.1, inferInstance⟩

theorem le_supLevel_left (F E : FiniteSubfield) : F ≤ supLevel F E := le_sup_left (a := F.1)

theorem le_supLevel_right (F E : FiniteSubfield) : E ≤ supLevel F E := le_sup_right (a := F.1)

variable (S : Set (HeightOneSpectrum (𝓞 K.1))) {v : HeightOneSpectrum (𝓞 K.1)}
  (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1))

section Inside

theorem levelOf_subset_max {y : ℚ̄} (hy : y ∈ maxUnramifiedOutside K.1 ℚ̄ S) :
    ∀ x ∈ (levelOf K y).1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S := by
  have h : (levelOf K y).1 ≤ (maxUnramifiedOutside K.1 ℚ̄ S).restrictScalars ℚ := by
    refine sup_le (fun x hx => ?_) ?_
    · exact (maxUnramifiedOutside K.1 ℚ̄ S).algebraMap_mem ⟨x, hx⟩
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact hy
  exact fun x hx => h hx

theorem supLevel_subset_max {F E : FiniteSubfield}
    (hF : ∀ x ∈ F.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (hE : ∀ x ∈ E.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S) :
    ∀ x ∈ (supLevel F E).1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S := by
  have h : (supLevel F E).1 ≤ (maxUnramifiedOutside K.1 ℚ̄ S).restrictScalars ℚ :=
    sup_le (fun x hx => hF x hx) (fun x hx => hE x hx)
  exact fun x hx => h hx

theorem isUnramifiedIn_of_subset_max (hv : v ∉ S) (F : FiniteSubfield) [Fact (K ≤ F)]
    (hF : ∀ x ∈ F.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S) :
    Algebra.IsUnramifiedIn (𝓞 F.1) v.asIdeal := by
  let E' : IntermediateField K.1 ℚ̄ :=
    IntermediateField.extendScalars (show K.1 ≤ F.1 from Fact.out)
  have : FiniteDimensional K.1 E' := (inferInstance : FiniteDimensional K.1 F.1)
  have hle : E' ≤ maxUnramifiedOutside K.1 ℚ̄ S := fun x hx => hF x hx
  exact (isUnramifiedOutside_iff_le_maxUnramifiedOutside S).2 hle v hv

theorem valuation_placeOfEmbedding_algebraMap (hv : v ∉ S) {F E : FiniteSubfield} [Fact (K ≤ F)]
    [Fact (K ≤ E)] [Fact (F ≤ E)] (hE : ∀ x ∈ E.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S) (y : F.1) :
    (placeOfEmbedding ι E).1.valuation E.1 (algebraMap F.1 E.1 y) =
      (placeOfEmbedding ι F).1.valuation F.1 y := by
  have hU : Algebra.IsUnramifiedAt (𝓞 K.1) (placeOfEmbedding ι E).1.asIdeal :=
    isUnramifiedIn_of_subset_max S hv E hE _ inferInstance (placeOfEmbedding ι E).2
  have : Algebra.IsUnramifiedAt (𝓞 F.1) (placeOfEmbedding ι E).1.asIdeal :=
    ((isUnramifiedAt_tower_iff (F := K.1) (L := F.1) (M := E.1) _).1 hU).2
  exact valuation_algebraMap_of_isUnramifiedAt (placeOfEmbedding ι F).1 (placeOfEmbedding ι E).1 y

theorem valuation_placeOfEmbedding_algebraMap_base (hv : v ∉ S) {E : FiniteSubfield} [Fact (K ≤ E)]
    (hE : ∀ x ∈ E.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S) (a : K.1) :
    (placeOfEmbedding ι E).1.valuation E.1 (algebraMap K.1 E.1 a) = v.valuation K.1 a := by
  have : Algebra.IsUnramifiedAt (𝓞 K.1) (placeOfEmbedding ι E).1.asIdeal :=
    isUnramifiedIn_of_subset_max S hv E hE _ inferInstance (placeOfEmbedding ι E).2
  exact valuation_algebraMap_of_isUnramifiedAt v (placeOfEmbedding ι E).1 a

end Inside

section Transport

variable {N : FiniteSubfield} [Fact (K ≤ N)]

theorem placeOfEmbedding_comp_algEquiv
    (σ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1)) :
    placeOfEmbedding (((σ : AlgebraicClosure (v.adicCompletion K.1) →ₐ[v.adicCompletion K.1]
      AlgebraicClosure (v.adicCompletion K.1)).restrictScalars K.1).comp ι) N =
      placeOfEmbedding ι N := by
  refine (eq_placeOfEmbedding _ N ((σ : AlgebraicClosure (v.adicCompletion K.1) →ₐ[v.adicCompletion K.1]
      AlgebraicClosure (v.adicCompletion K.1)).comp (completionEmbedding ι N)) fun x => ?_).symm
  rw [AlgHom.comp_apply, completionEmbedding_algebraMap]
  rfl

theorem placeOfEmbedding_eq_inv_smul (g : N.1 ≃ₐ[K.1] N.1)
    (ι' : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1)) (h : ∀ x : N.1, ι' x = ι (g x)) :
    placeOfEmbedding ι' N = g⁻¹ • placeOfEmbedding ι N := by
  set w₀ := placeOfEmbedding ι N
  have hu : w₀.1 = g • (g⁻¹ • w₀).1 := eq_smul_inv_smul v g w₀
  let j := (completionEmbedding ι N).comp (galEquiv v g (g⁻¹ • w₀).1 w₀.1 hu).toAlgHom
  refine (eq_placeOfEmbedding ι' N j fun x => ?_).symm
  change completionEmbedding ι N (galEquiv v g (g⁻¹ • w₀).1 w₀.1 hu (algebraMap N.1 _ x)) = ι' x
  rw [galEquiv_algebraMap, completionEmbedding_algebraMap, h]

theorem inv_smul_placeOfEmbedding_of_comm (g : N.1 ≃ₐ[K.1] N.1)
    (σ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1))
    (hg : ∀ x : N.1, ι (g x) = σ (ι x)) :
    g⁻¹ • placeOfEmbedding ι N = placeOfEmbedding ι N := by
  set w₀ := placeOfEmbedding ι N
  have hu : w₀.1 = g • (g⁻¹ • w₀).1 := eq_smul_inv_smul v g w₀
  let j := σ.symm.toAlgHom.comp
    ((completionEmbedding ι N).comp (galEquiv v g (g⁻¹ • w₀).1 w₀.1 hu).toAlgHom)
  refine eq_placeOfEmbedding ι N j fun x => ?_
  change σ.symm (completionEmbedding ι N (galEquiv v g (g⁻¹ • w₀).1 w₀.1 hu (algebraMap N.1 _ x))) =
    ι x
  rw [galEquiv_algebraMap, completionEmbedding_algebraMap, hg, AlgEquiv.symm_apply_apply]

theorem valuation_inv_smul_placesOver (g : N.1 ≃ₐ[K.1] N.1) (w : PlacesOver N.1 v) (x : N.1) :
    (g⁻¹ • w).1.valuation N.1 x = w.1.valuation N.1 (g x) := by
  have := valuation_smul g (g⁻¹ • w).1 x
  rw [← coe_smul_placesOver, smul_inv_smul] at this
  exact this.symm

end Transport

section GaloisLevel

theorem exists_galois_level {y : ℚ̄} (hy : y ∈ maxUnramifiedOutside K.1 ℚ̄ S) :
    ∃ (N : FiniteSubfield) (_ : Fact (K ≤ N)), IsGalois K.1 N.1 ∧
      (∀ x ∈ N.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S) ∧ y ∈ N.1 := by
  let A : IntermediateField K.1 ℚ̄ := IntermediateField.adjoin K.1 {y}
  have : FiniteDimensional K.1 A :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral y)
  let N' : IntermediateField K.1 ℚ̄ := IntermediateField.normalClosure K.1 A ℚ̄
  have hN'f : FiniteDimensional K.1 N' := inferInstance
  have hN'n : Normal K.1 N' := inferInstance
  have hN'le : N' ≤ maxUnramifiedOutside K.1 ℚ̄ S :=
    IntermediateField.normalClosure_le_iff_of_normal.2
      ((IntermediateField.adjoin_simple_le_iff).2 hy)
  have := K.2
  have hN'q : FiniteDimensional ℚ N' := Module.Finite.trans K.1 N'
  let N : FiniteSubfield := ⟨N'.restrictScalars ℚ, hN'q⟩
  have hKN : Fact (K ≤ N) := ⟨fun x hx => N'.algebraMap_mem ⟨x, hx⟩⟩
  refine ⟨N, hKN, ?_, fun x hx => hN'le hx, IntermediateField.le_normalClosure A
    (IntermediateField.mem_adjoin_simple_self K.1 y)⟩
  have : IsGalois K.1 N' := ⟨⟩
  exact this

end GaloisLevel

def ordEmbFun (y : ℚ̄ˣ) : ℤ :=
  -WithZero.log ((placeOfEmbedding ι (levelOf K (y : ℚ̄))).1.valuation (levelOf K (y : ℚ̄)).1
    ⟨(y : ℚ̄), mem_levelOf (y : ℚ̄)⟩)

theorem valuation_placeOfEmbedding_eq (hv : v ∉ S) (F : FiniteSubfield) [Fact (K ≤ F)]
    (hF : ∀ x ∈ F.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S) (y : ℚ̄ˣ) (hy : (y : ℚ̄) ∈ F.1) :
    (placeOfEmbedding ι F).1.valuation F.1 ⟨y, hy⟩ = WithZero.exp (-ordEmbFun ι y) := by
  set L := levelOf K (y : ℚ̄)
  set M := supLevel L F
  have hL : ∀ x ∈ L.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S := levelOf_subset_max S (hF _ hy)
  have hM : ∀ x ∈ M.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S := supLevel_subset_max S hL hF
  have : Fact (L ≤ M) := ⟨le_supLevel_left L F⟩
  have : Fact (F ≤ M) := ⟨le_supLevel_right L F⟩
  have : Fact (K ≤ M) := ⟨(Fact.out : K ≤ L).trans (le_supLevel_left L F)⟩
  have h1 := valuation_placeOfEmbedding_algebraMap S ι hv (F := F) (E := M) hM ⟨y, hy⟩
  have h2 := valuation_placeOfEmbedding_algebraMap S ι hv (F := L) (E := M) hM
    ⟨y, mem_levelOf (y : ℚ̄)⟩
  have h3 : algebraMap F.1 M.1 ⟨y, hy⟩ = algebraMap L.1 M.1 ⟨y, mem_levelOf (y : ℚ̄)⟩ := rfl
  rw [← h1, h3, h2]
  have h0 : (placeOfEmbedding ι L).1.valuation L.1 ⟨(y : ℚ̄), mem_levelOf (y : ℚ̄)⟩ ≠ 0 := by
    rw [Ne, map_eq_zero]
    intro h
    exact y.ne_zero (congrArg Subtype.val h)
  rw [ordEmbFun, neg_neg, WithZero.exp_log h0]

abbrev maxUnitsToUnits : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ →* ℚ̄ˣ :=
  Units.map (maxUnramifiedOutside K.1 ℚ̄ S).val.toRingHom.toMonoidHom

def ordEmb (hv : v ∉ S) : Additive (maxUnramifiedOutside K.1 ℚ̄ S)ˣ →+ ℤ where
  toFun y := ordEmbFun ι (maxUnitsToUnits S y.toMul)
  map_zero' := by
    change ordEmbFun ι (maxUnitsToUnits S 1) = 0
    rw [map_one, ordEmbFun]
    have : (⟨((1 : ℚ̄ˣ) : ℚ̄), mem_levelOf _⟩ : (levelOf K ((1 : ℚ̄ˣ) : ℚ̄)).1) = 1 := rfl
    rw [this, map_one, WithZero.log_one, neg_zero]
  map_add' y z := by
    change ordEmbFun ι (maxUnitsToUnits S (y.toMul * z.toMul)) =
      ordEmbFun ι (maxUnitsToUnits S y.toMul) + ordEmbFun ι (maxUnitsToUnits S z.toMul)
    rw [map_mul]
    set a := maxUnitsToUnits S y.toMul
    set b := maxUnitsToUnits S z.toMul
    have ha : (a : ℚ̄) ∈ maxUnramifiedOutside K.1 ℚ̄ S := (y.toMul : maxUnramifiedOutside K.1 ℚ̄ S).2
    have hb : (b : ℚ̄) ∈ maxUnramifiedOutside K.1 ℚ̄ S := (z.toMul : maxUnramifiedOutside K.1 ℚ̄ S).2
    set F := supLevel (levelOf K (a : ℚ̄)) (levelOf K (b : ℚ̄))
    have hF : ∀ x ∈ F.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S :=
      supLevel_subset_max S (levelOf_subset_max S ha) (levelOf_subset_max S hb)
    have : Fact (K ≤ F) := ⟨(Fact.out : K ≤ levelOf K (a : ℚ̄)).trans (le_supLevel_left _ _)⟩
    have haF : (a : ℚ̄) ∈ F.1 := le_supLevel_left _ _ (mem_levelOf (a : ℚ̄))
    have hbF : (b : ℚ̄) ∈ F.1 := le_supLevel_right _ _ (mem_levelOf (b : ℚ̄))
    have habF : ((a * b : ℚ̄ˣ) : ℚ̄) ∈ F.1 := by
      rw [Units.val_mul]
      exact F.1.mul_mem haF hbF
    have e1 := valuation_placeOfEmbedding_eq S ι hv F hF (a * b) habF
    have e2 := valuation_placeOfEmbedding_eq S ι hv F hF a haF
    have e3 := valuation_placeOfEmbedding_eq S ι hv F hF b hbF
    have hmul : (⟨((a * b : ℚ̄ˣ) : ℚ̄), habF⟩ : F.1) = ⟨a, haF⟩ * ⟨b, hbF⟩ := rfl
    rw [hmul, map_mul, e2, e3, ← WithZero.exp_add] at e1
    have := WithZero.exp_injective e1
    omega

theorem ordEmb_apply (hv : v ∉ S) (y : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :
    ordEmb S ι hv (Additive.ofMul y) = ordEmbFun ι (maxUnitsToUnits S y) :=
  rfl

theorem ordEmb_decompHomS (hv : v ∉ S)
    (σ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1))
    (y : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :
    ordEmb S ι hv (Additive.ofMul
      (galUnitsHom K.1 _ (decompHomS (v.adicCompletion K.1) S ι σ) y)) =
      ordEmb S ι hv (Additive.ofMul y) := by
  have key : ∀ x : maxUnramifiedOutside K.1 ℚ̄ S,
      ι ((decompHomS (v.adicCompletion K.1) S ι σ x : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) = σ (ι x) :=
    fun x => decompHom_apply (Kv := v.adicCompletion K.1)
      (ι.comp (maxUnramifiedOutside K.1 ℚ̄ S).val) σ x
  generalize decompHomS (v.adicCompletion K.1) S ι σ = τ at key ⊢
  rw [ordEmb_apply, ordEmb_apply]
  have hY : ((maxUnitsToUnits S y : ℚ̄ˣ) : ℚ̄) ∈ maxUnramifiedOutside K.1 ℚ̄ S :=
    (y : maxUnramifiedOutside K.1 ℚ̄ S).2
  obtain ⟨N, hKN, hNg, hN, hYN⟩ := exists_galois_level S hY
  obtain ⟨g, hg⟩ : ∃ g : N.1 ≃ₐ[K.1] N.1, ∀ x : N.1, ι (g x) = σ (ι x) :=
    ⟨decompHom (v.adicCompletion K.1) (embedLevel ι N) σ, fun x =>
      decompHom_apply (Kv := v.adicCompletion K.1) (embedLevel ι N) σ x⟩
  have hz : ((maxUnitsToUnits S (galUnitsHom K.1 _ τ y) : ℚ̄ˣ) : ℚ̄) = ((g ⟨_, hYN⟩ : N.1) : ℚ̄) := by
    apply ι.toRingHom.injective
    have h1 := key (y : maxUnramifiedOutside K.1 ℚ̄ S)
    have h2 := hg ⟨_, hYN⟩
    change ι _ = ι _
    rw [h2]
    exact h1
  generalize maxUnitsToUnits S (galUnitsHom K.1 _ τ y) = b at hz ⊢
  generalize maxUnitsToUnits S y = a at hY hYN hz ⊢
  have hbN : (b : ℚ̄) ∈ N.1 := by
    rw [hz]
    exact (g _).2
  have e1 := valuation_placeOfEmbedding_eq S ι hv N hN b hbN
  have e2 := valuation_placeOfEmbedding_eq S ι hv N hN a hYN
  have e3 := (inv_smul_placeOfEmbedding_of_comm ι g σ hg).symm
  have e4 := valuation_inv_smul_placesOver g (placeOfEmbedding ι N) ⟨a, hYN⟩
  rw [← e3] at e4
  have e5 : (⟨(b : ℚ̄), hbN⟩ : N.1) = g ⟨a, hYN⟩ := Subtype.ext hz
  rw [e5, ← e4, e2] at e1
  have := WithZero.exp_injective e1
  omega

theorem ordEmb_algebraMap (hv : v ∉ S) (a : K.1ˣ) :
    ordEmb S ι hv (Additive.ofMul
      (Units.map (algebraMap K.1 (maxUnramifiedOutside K.1 ℚ̄ S)).toMonoidHom a)) = ordAt v a := by
  set x := maxUnitsToUnits S (Units.map (algebraMap K.1 (maxUnramifiedOutside K.1 ℚ̄ S)).toMonoidHom a)
  have hx : (x : ℚ̄) = algebraMap K.1 ℚ̄ a := rfl
  have hxS : (x : ℚ̄) ∈ maxUnramifiedOutside K.1 ℚ̄ S := by
    rw [hx]
    exact (maxUnramifiedOutside K.1 ℚ̄ S).algebraMap_mem a
  set F := levelOf K (x : ℚ̄)
  have hF := levelOf_subset_max S hxS
  have e1 := valuation_placeOfEmbedding_eq S ι hv F hF x (mem_levelOf _)
  have e2 := valuation_placeOfEmbedding_algebraMap_base S ι hv hF (a : K.1)
  have e3 : (⟨(x : ℚ̄), mem_levelOf _⟩ : F.1) = algebraMap K.1 F.1 a := rfl
  rw [e3, e2, valuation_eq_exp_neg_ordAt] at e1
  change ordEmbFun ι x = ordAt v a
  have := WithZero.exp_injective e1
  omega

theorem ordEmb_eq_zero_of_mem (hv : v ∉ S) {z : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ}
    (hz : z ∈ sUnitsMax K.1 ℚ̄ S) : ordEmb S ι hv (Additive.ofMul z) = 0 := by
  rw [ordEmb_apply]
  have hZ : ((maxUnitsToUnits S z : ℚ̄ˣ) : ℚ̄) ∈ maxUnramifiedOutside K.1 ℚ̄ S :=
    (z : maxUnramifiedOutside K.1 ℚ̄ S).2
  generalize hzz : maxUnitsToUnits S z = a at hZ
  set F := levelOf K (a : ℚ̄)
  have hF := levelOf_subset_max S hZ
  have e1 := valuation_placeOfEmbedding_eq S ι hv F hF a (mem_levelOf _)
  let E' : IntermediateField K.1 ℚ̄ :=
    IntermediateField.extendScalars (show K.1 ≤ F.1 from (fact_le_levelOf (a : ℚ̄)).out)
  have hle : E' ≤ maxUnramifiedOutside K.1 ℚ̄ S := fun x hx => hF x hx
  let φ : F.1 →ₐ[K.1] maxUnramifiedOutside K.1 ℚ̄ S := IntermediateField.inclusion hle
  have hφ : Function.Injective φ := φ.toRingHom.injective
  let aF : F.1ˣ := Units.mk0 ⟨(a : ℚ̄), mem_levelOf _⟩ (fun h => a.ne_zero (congrArg Subtype.val h))
  have hφa : φ.restrictScalars (S.integer K.1) (aF : F.1) = (z : maxUnramifiedOutside K.1 ℚ̄ S) := by
    apply Subtype.ext
    change (a : ℚ̄) = _
    rw [← hzz]
    rfl
  have hφa' : φ.restrictScalars (S.integer K.1) ((aF⁻¹ : F.1ˣ) : F.1) =
      ((z⁻¹ : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S) := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, Units.val_inv_eq_inv_val, ← hφa]
  have hmem : aF ∈ sUnitsOf S F.1 := by
    refine ⟨(isIntegral_algHom_iff (φ.restrictScalars (S.integer K.1)) hφ).1 ?_,
      (isIntegral_algHom_iff (φ.restrictScalars (S.integer K.1)) hφ).1 ?_⟩
    · rw [hφa]
      exact hz.1
    · rw [hφa']
      exact hz.2
  rw [mem_sUnitsOf_iff_mem_unit] at hmem
  have hw : (placeOfEmbedding ι F).1 ∉ placesOver S := by
    rw [mem_placesOver_iff]
    rw [← liesOver_iff_eq_underPlace.1 (placeOfEmbedding ι F).2]
    exact hv
  have h1 := hmem _ hw
  change (placeOfEmbedding ι F).1.valuation F.1 ⟨(a : ℚ̄), mem_levelOf _⟩ = 1 at h1
  rw [h1, ← WithZero.exp_zero] at e1
  have := WithZero.exp_injective e1
  omega

theorem exists_valuation_eq_ordEmb (hv : v ∉ S) {N : FiniteSubfield} [Fact (K ≤ N)]
    [IsGalois K.1 N.1] (hN : ∀ x ∈ N.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (y : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) (hyN : ((y : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) ∈ N.1)
    (w : PlacesOver N.1 v) :
    ∃ τ : galUnramifiedOutside K.1 ℚ̄ S, w.1.valuation N.1 ⟨_, hyN⟩ =
      WithZero.exp (-ordEmb S ι hv (Additive.ofMul (galUnitsHom K.1 _ τ y))) := by
  obtain ⟨ι', hι'⟩ := exists_placeOfEmbedding_eq (K := K) (E := N) w
  obtain ⟨g, rfl⟩ := exists_eq_comp_of_normal ι ι'
  let gN : N.1 ≃ₐ[K.1] N.1 := AlgEquiv.restrictNormal g N.1
  have hgN : ∀ x : N.1, ((gN x : N.1) : ℚ̄) = g x := fun x =>
    AlgEquiv.restrictNormal_commutes g N.1 x
  let τ : galUnramifiedOutside K.1 ℚ̄ S := AlgEquiv.restrictNormal g (maxUnramifiedOutside K.1 ℚ̄ S)
  have hτ : ∀ x : maxUnramifiedOutside K.1 ℚ̄ S, ((τ x : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) = g x :=
    fun x => AlgEquiv.restrictNormal_commutes g (maxUnramifiedOutside K.1 ℚ̄ S) x
  refine ⟨τ, ?_⟩
  have hw := placeOfEmbedding_eq_inv_smul ι gN (ι.comp (g : ℚ̄ →ₐ[K.1] ℚ̄)) fun x => by
    rw [AlgHom.comp_apply, hgN]
    rfl
  rw [hι'] at hw
  rw [hw, valuation_inv_smul_placesOver]
  have hmem : ((maxUnitsToUnits S (galUnitsHom K.1 _ τ y) : ℚ̄ˣ) : ℚ̄) ∈ N.1 := by
    change ((τ (y : maxUnramifiedOutside K.1 ℚ̄ S) : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) ∈ N.1
    rw [hτ, ← hgN ⟨_, hyN⟩]
    exact (gN _).2
  rw [ordEmb_apply, ← valuation_placeOfEmbedding_eq S ι hv N hN _ hmem]
  congr 1
  apply Subtype.ext
  change ((gN ⟨_, hyN⟩ : N.1) : ℚ̄) = ((τ (y : maxUnramifiedOutside K.1 ℚ̄ S) :
    maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄)
  rw [hτ, hgN]

theorem exists_placesOver_valuation_eq_ordEmb (hv : v ∉ S) {N : FiniteSubfield} [Fact (K ≤ N)]
    [IsGalois K.1 N.1] (hN : ∀ x ∈ N.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (y : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) (hyN : ((y : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) ∈ N.1)
    (σ : galUnramifiedOutside K.1 ℚ̄ S) :
    ∃ w : PlacesOver N.1 v, w.1.valuation N.1 ⟨_, hyN⟩ =
      WithZero.exp (-ordEmb S ι hv (Additive.ofMul (galUnitsHom K.1 _ σ y))) := by
  let g : ℚ̄ ≃ₐ[K.1] ℚ̄ := σ.liftNormal ℚ̄
  have hg : ∀ x : maxUnramifiedOutside K.1 ℚ̄ S, g x = ((σ x : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) :=
    fun x => AlgEquiv.liftNormal_commutes σ ℚ̄ x
  let gN : N.1 ≃ₐ[K.1] N.1 := AlgEquiv.restrictNormal g N.1
  have hgN : ∀ x : N.1, ((gN x : N.1) : ℚ̄) = g x := fun x =>
    AlgEquiv.restrictNormal_commutes g N.1 x
  refine ⟨gN⁻¹ • placeOfEmbedding ι N, ?_⟩
  rw [valuation_inv_smul_placesOver]
  have hmem : ((maxUnitsToUnits S (galUnitsHom K.1 _ σ y) : ℚ̄ˣ) : ℚ̄) ∈ N.1 := by
    change ((σ (y : maxUnramifiedOutside K.1 ℚ̄ S) : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) ∈ N.1
    rw [← hg, ← hgN ⟨_, hyN⟩]
    exact (gN _).2
  rw [ordEmb_apply, ← valuation_placeOfEmbedding_eq S ι hv N hN _ hmem]
  congr 1
  apply Subtype.ext
  change ((gN ⟨_, hyN⟩ : N.1) : ℚ̄) = ((σ (y : maxUnramifiedOutside K.1 ℚ̄ S) :
    maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄)
  rw [hgN, hg]

variable (ιs : LocalEmbeddings K)

theorem mem_sUnitsMax_iff_ordEmb (y : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :
    y ∈ sUnitsMax K.1 ℚ̄ S ↔ ∀ (v : HeightOneSpectrum (𝓞 K.1)) (hv : v ∉ S)
      (σ : galUnramifiedOutside K.1 ℚ̄ S),
      ordEmb S (ιs.fin v) hv (Additive.ofMul (galUnitsHom K.1 _ σ y)) = 0 := by
  constructor
  · intro hy v hv σ
    exact ordEmb_eq_zero_of_mem S (ιs.fin v) hv (galUnitsHom_mem_sUnitsOf σ hy)
  · intro h
    have hY : ((y : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) ∈ maxUnramifiedOutside K.1 ℚ̄ S :=
      (y : maxUnramifiedOutside K.1 ℚ̄ S).2
    obtain ⟨N, hKN, hNg, hN, hYN⟩ := exists_galois_level S hY
    let E' : IntermediateField K.1 ℚ̄ :=
      IntermediateField.extendScalars (show K.1 ≤ N.1 from hKN.out)
    have hle : E' ≤ maxUnramifiedOutside K.1 ℚ̄ S := fun x hx => hN x hx
    let φ : N.1 →ₐ[K.1] maxUnramifiedOutside K.1 ℚ̄ S := IntermediateField.inclusion hle
    let yN : N.1ˣ := Units.mk0 ⟨_, hYN⟩ (fun h0 => y.ne_zero (Subtype.ext (by
      have := congrArg Subtype.val h0
      exact this)))
    have hφy : φ.restrictScalars (S.integer K.1) (yN : N.1) = (y : maxUnramifiedOutside K.1 ℚ̄ S) :=
      Subtype.ext rfl
    have hφy' : φ.restrictScalars (S.integer K.1) ((yN⁻¹ : N.1ˣ) : N.1) =
        ((y⁻¹ : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S) := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, Units.val_inv_eq_inv_val, hφy]
    have hmem : yN ∈ sUnitsOf S N.1 := by
      rw [mem_sUnitsOf_iff_mem_unit]
      intro w hw
      have hvS : underPlace (F := K.1) w ∉ S := fun h' => hw (mem_placesOver_iff.2 h')
      obtain ⟨τ, hτ⟩ := exists_valuation_eq_ordEmb S (ιs.fin (underPlace (F := K.1) w)) hvS hN y hYN
        ⟨w, liesOver_underPlace w⟩
      change w.valuation N.1 ⟨_, hYN⟩ = 1
      rw [hτ, h _ hvS τ, neg_zero, WithZero.exp_zero]
    have hφ : Function.Injective φ := φ.toRingHom.injective
    refine ⟨?_, ?_⟩
    · rw [← hφy]
      exact (isIntegral_algHom_iff (φ.restrictScalars (S.integer K.1)) hφ).2 hmem.1
    · rw [← hφy']
      exact (isIntegral_algHom_iff (φ.restrictScalars (S.integer K.1)) hφ).2 hmem.2

theorem finite_ordEmb_ne_zero (y : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :
    {v : {v : HeightOneSpectrum (𝓞 K.1) // v ∉ S} | ∃ σ : galUnramifiedOutside K.1 ℚ̄ S,
      ordEmb S (ιs.fin v.1) v.2 (Additive.ofMul (galUnitsHom K.1 _ σ y)) ≠ 0}.Finite := by
  have hY : ((y : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) ∈ maxUnramifiedOutside K.1 ℚ̄ S :=
    (y : maxUnramifiedOutside K.1 ℚ̄ S).2
  obtain ⟨N, hKN, hNg, hN, hYN⟩ := exists_galois_level S hY
  let yN : N.1ˣ := Units.mk0 ⟨_, hYN⟩ (fun h0 => y.ne_zero (Subtype.ext (by
      have := congrArg Subtype.val h0
      exact this)))
  have hT := finite_ordAt_ne_zero yN
  refine ((hT.image (underPlace (F := K.1))).preimage Subtype.val_injective.injOn).subset ?_
  rintro ⟨v, hv⟩ ⟨σ, hσ⟩
  obtain ⟨w, hw⟩ := exists_placesOver_valuation_eq_ordEmb S (ιs.fin v) hv hN y hYN σ
  refine ⟨w.1, ?_, (liesOver_iff_eq_underPlace.1 w.2).symm⟩
  intro h0
  rw [ordAt_eq_zero_iff] at h0
  apply hσ
  change w.1.valuation N.1 ⟨_, hYN⟩ = 1 at h0
  rw [hw, ← WithZero.exp_zero] at h0
  exact neg_eq_zero.1 (WithZero.exp_injective h0)

end

end GroundTheory.ProfCoh
