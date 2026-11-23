import Mathlib
import GroundTheory.ProfiniteCohomology.LocalTateDuality.InjectiveCohomologyMapKummerSeqOpenFTwo
import GroundTheory.ProfiniteCohomology.LocalTateDuality.Bockstein
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory IntermediateField

attribute [local instance 2000] Rep.hV2

attribute [local irreducible] localClassFormationOfIsSepClosure

section Pairings

variable {K Ksep : Type} [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] {n : ℕ}

theorem nsmul_res_galRootsOfUnity_eq_zero (hn : (n : K) ≠ 0) (W : Subgroup Gal(Ksep/K))
    (d : Rep.res W.subtype (galRootsOfUnity.{0} K Ksep n)) : n • d = 0 :=
  nsmul_eq_zero_of_nonempty_addEquiv (nonempty_addEquiv_galRootsOfUnity (Ksep := Ksep) hn) d

omit [IsSepClosure K Ksep] in

theorem bockSeq_kummerSeqOpen_compat₁₂ (W : Subgroup Gal(Ksep/K)) :
    ((bockSeq W n).f ⊗ₘ 𝟙 (kummerSeqOpen (K := K) (Ksep := Ksep) n W).X₂) ≫
        intMulPairing W (kummerSeqOpen (K := K) (Ksep := Ksep) n W).X₂ =
      (𝟙 (bockSeq W n).X₁ ⊗ₘ (kummerSeqOpen (K := K) (Ksep := Ksep) n W).g) ≫
        intMulPairing W (kummerSeqOpen (K := K) (Ksep := Ksep) n W).X₃ := by
  refine Rep.Hom.ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => ?_))
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul m a =>
    obtain ⟨m⟩ := m
    show (intMulPairing W (Rep.res W.subtype (galUnits.{0} K Ksep))).hom
        ((n • 𝟙 (intRepTriv W)).hom (ULift.up m) ⊗ₜ[ULift.{0} ℤ] a) =
      (intMulPairing W (Rep.res W.subtype (galUnits.{0} K Ksep))).hom
        (ULift.up m ⊗ₜ[ULift.{0} ℤ] (kummerSeqOpen (K := K) (Ksep := Ksep) n W).g.hom a)
    have hnm : (n • 𝟙 (intRepTriv W)).hom (ULift.up m) = (ULift.up ((n : ℤ) * m) : intRepTriv W) := by
      rw [nsmul_id_hom_apply]
      ext
      simp
    rw [hnm, kummerSeqOpen_g_hom_apply, intMulPairing_tmul, intMulPairing_tmul, mul_zsmul',
      natCast_zsmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem bockSeq_kummerSeqOpen_compat₂₃ (hn : (n : K) ≠ 0) (W : Subgroup Gal(Ksep/K)) :
    (𝟙 (bockSeq W n).X₂ ⊗ₘ (kummerSeqOpen (K := K) (Ksep := Ksep) n W).f) ≫
        intMulPairing W (kummerSeqOpen (K := K) (Ksep := Ksep) n W).X₂ =
      ((bockSeq W n).g ⊗ₘ 𝟙 (kummerSeqOpen (K := K) (Ksep := Ksep) n W).X₁) ≫
        (zmodMulPairing n (Rep.res W.subtype (galRootsOfUnity.{0} K Ksep n))
          (nsmul_res_galRootsOfUnity_eq_zero hn W) ≫ (kummerSeqOpen (K := K) (Ksep := Ksep) n W).f) := by
  refine Rep.Hom.ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => ?_))
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul m d =>
    obtain ⟨m⟩ := m
    show (intMulPairing W (Rep.res W.subtype (galUnits.{0} K Ksep))).hom
        (ULift.up m ⊗ₜ[ULift.{0} ℤ] (kummerSeqOpen (K := K) (Ksep := Ksep) n W).f.hom d) =
      (kummerSeqOpen (K := K) (Ksep := Ksep) n W).f.hom
        ((zmodMulPairing n (Rep.res W.subtype (galRootsOfUnity.{0} K Ksep n))
          (nsmul_res_galRootsOfUnity_eq_zero hn W)).hom
          ((zmodReduction W n).hom (ULift.up m) ⊗ₜ[ULift.{0} ℤ] d))
    rw [zmodReduction_hom_apply, zmodMulPairing_tmul, intMulPairing_tmul,
      zsmul_eq_zsmul_of_intCast_eq (nsmul_res_galRootsOfUnity_eq_zero hn W)
        (ZMod.intCast_zmod_cast (m : ZMod n)) d, map_zsmul]
  | add x y hx hy => simp only [map_add, hx, hy]

end Pairings

section Key

variable {K Ksep : Type} [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] {n : ℕ}

theorem ne_zero_of_natCast_ne_zero' (hn : (n : K) ≠ 0) : n ≠ 0 := by
  rintro rfl
  exact hn Nat.cast_zero

theorem cohomologyMap_cupPairing_zmodMul_δ (hn : (n : K) ≠ 0) (W : Subgroup Gal(Ksep/K))
    (x : cohomology (zmodRep.{0} W n) 1)
    (y : cohomology (Rep.res W.subtype (galUnits.{0} K Ksep)) 0) :
    (cohomologyMap (kummerSeqOpen (K := K) (Ksep := Ksep) n W).f 2).hom
        (cupPairing (zmodMulPairing n (Rep.res W.subtype (galRootsOfUnity.{0} K Ksep n))
          (nsmul_res_galRootsOfUnity_eq_zero hn W)) (show 1 + 1 = 2 from rfl) x
          ((δ (kummerSeqOpen_shortExact hn W) 0 1 rfl).hom y)) =
      cupPairing (intMulPairing W (Rep.res W.subtype (galUnits.{0} K Ksep))) (show 2 + 0 = 2 from rfl)
        ((δ (bockSeq_shortExact W n (ne_zero_of_natCast_ne_zero' hn)) 1 2 rfl).hom x) y := by
  have h := cupPairing_δ_eq (S := bockSeq W n) (T := kummerSeqOpen (K := K) (Ksep := Ksep) n W)
    (p := 1) (p' := 2) (q := 0) (q' := 1) (n := 2)
    (intMulPairing W (Rep.res W.subtype (galUnits.{0} K Ksep)))
    (intMulPairing W (Rep.res W.subtype (galUnits.{0} K Ksep)))
    (zmodMulPairing n (Rep.res W.subtype (galRootsOfUnity.{0} K Ksep n))
      (nsmul_res_galRootsOfUnity_eq_zero hn W) ≫ (kummerSeqOpen (K := K) (Ksep := Ksep) n W).f)
    (bockSeq_kummerSeqOpen_compat₁₂ W) (bockSeq_kummerSeqOpen_compat₂₃ hn W)
    (bockSeq_shortExact W n (ne_zero_of_natCast_ne_zero' hn)) (kummerSeqOpen_shortExact hn W)
    rfl rfl rfl rfl x y
  have h1 : ((-1 : ULift.{0} ℤ) ^ (1 + 1)) = 1 := by norm_num
  rw [h1] at h
  exact (cohomologyMap_cupPairing _ _ _ _ _).trans (h.trans (@one_smul _ _ _
    (cohomology (Rep.res W.subtype (galUnits.{0} K Ksep)) 2).isModule.toMulAction _)).symm

end Key

section Units

variable {K Ksep : Type} [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]

def unitsInvariantOpen (W : Subgroup Gal(Ksep/K)) (a : (fixedField W)ˣ) :
    (Rep.res W.subtype (galUnits.{0} K Ksep)).ρ.invariants :=
  ⟨Additive.ofMul (Units.map (algebraMap (fixedField W) Ksep : fixedField W →* Ksep) a),
    (Representation.mem_invariants _ _).2 fun σ =>
      congrArg Additive.ofMul (Units.ext ((mem_fixedField_iff _ _).1 (a : fixedField W).2 σ σ.2))⟩

omit [IsSepClosure K Ksep] in
theorem coe_unitsInvariantOpen (W : Subgroup Gal(Ksep/K)) (a : (fixedField W)ˣ) :
    ((unitsInvariantOpen W a : Rep.res W.subtype (galUnits.{0} K Ksep)) : Additive Ksepˣ) =
      Additive.ofMul (Units.map (algebraMap (fixedField W) Ksep : fixedField W →* Ksep) a) :=
  rfl

omit [IsSepClosure K Ksep] in

theorem exists_unitsInvariantOpen_eq (W : Subgroup Gal(Ksep/K))
    (v : (Rep.res W.subtype (galUnits.{0} K Ksep)).ρ.invariants) :
    ∃ a : (fixedField W)ˣ, unitsInvariantOpen W a = v := by
  have ha : ((Additive.toMul (v : Rep.res W.subtype (galUnits.{0} K Ksep)) : Ksepˣ) : Ksep) ∈
      fixedField W :=
    (mem_fixedField_iff _ _).2 fun σ hσ =>
      congrArg (fun y : Additive Ksepˣ => ((Additive.toMul y : Ksepˣ) : Ksep))
        ((Representation.mem_invariants _ _).1 v.2 ⟨σ, hσ⟩)
  refine ⟨Units.mk0 ⟨_, ha⟩ fun h =>
    (Additive.toMul (v : Rep.res W.subtype (galUnits.{0} K Ksep)) : Ksepˣ).ne_zero
      (congrArg Subtype.val h), Subtype.ext (congrArg Additive.ofMul (Units.ext rfl))⟩

omit [IsSepClosure K Ksep] in
theorem unitsInvariantOpen_pow (W : Subgroup Gal(Ksep/K)) (a : (fixedField W)ˣ) (m : ℕ) :
    unitsInvariantOpen W (a ^ m) = m • unitsInvariantOpen W a := by
  apply Subtype.ext
  change Additive.ofMul (Units.map (algebraMap (fixedField W) Ksep : fixedField W →* Ksep) (a ^ m)) =
    m • Additive.ofMul (Units.map (algebraMap (fixedField W) Ksep : fixedField W →* Ksep) a)
  rw [map_pow, ofMul_pow]

theorem δ_unitsInvariantOpen_pow_eq_zero {n : ℕ} (hn : (n : K) ≠ 0) (W : Subgroup Gal(Ksep/K))
    (b : (fixedField W)ˣ) :
    (δ (kummerSeqOpen_shortExact (Ksep := Ksep) hn W) 0 1 rfl).hom
      ((H0Iso _).inv.hom (unitsInvariantOpen W (b ^ n))) = 0 := by
  refine (δ_H0Iso_inv_eq_zero_iff (kummerSeqOpen_shortExact (Ksep := Ksep) hn W) _).2
    ⟨unitsInvariantOpen W b, Subtype.ext ?_⟩
  rw [unitsInvariantOpen_pow]
  exact kummerSeqOpen_g_hom_apply n W _

end Units

section Transport

theorem exists_coboundary_iff_of_mulEquiv {Γ Γ' X : Type*} [Group Γ] [TopologicalSpace Γ] [Group Γ']
    [TopologicalSpace Γ'] [AddCommGroup X] (e : Γ' ≃* Γ) (he : Continuous e) (he' : Continuous e.symm)
    (ρ : Γ → X → X) (ρ' : Γ' → X → X) (hρ : ∀ g x, ρ (e g) x = ρ' g x)
    (c : Γ → Γ → X) (c' : Γ' → Γ' → X) (hc : ∀ g h, c (e g) (e h) = c' g h) :
    (∃ f : Γ → X, IsLocallyConstant f ∧ ∀ g h, c g h = ρ g (f h) - f (g * h) + f g) ↔
      ∃ f : Γ' → X, IsLocallyConstant f ∧ ∀ g h, c' g h = ρ' g (f h) - f (g * h) + f g := by
  constructor
  · rintro ⟨f, hf, hfc⟩
    refine ⟨fun g => f (e g), hf.comp_continuous he, fun g h => ?_⟩
    show c' g h = ρ' g (f (e h)) - f (e (g * h)) + f (e g)
    rw [← hc, hfc, map_mul, hρ]
  · rintro ⟨f, hf, hfc⟩
    refine ⟨fun g => f (e.symm g), hf.comp_continuous he', fun g h => ?_⟩
    obtain ⟨g, rfl⟩ := e.surjective g
    obtain ⟨h, rfl⟩ := e.surjective h
    show c (e g) (e h) = ρ (e g) (f (e.symm (e h))) - f (e.symm (e g * e h)) + f (e.symm (e g))
    rw [hc, hfc, ← map_mul, e.symm_apply_apply, e.symm_apply_apply, e.symm_apply_apply, hρ]

end Transport

section Local

variable {K Ksep : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] {n : ℕ}

theorem exists_δ_unitsInvariantOpen_eq (hn : (n : K) ≠ 0) (U : OpenSubgroup Gal(Ksep/K))
    (y : cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep n)) 1) :
    ∃ a : (fixedField (U : Subgroup Gal(Ksep/K)))ˣ,
      (δ (kummerSeqOpen_shortExact hn (U : Subgroup Gal(Ksep/K))) 0 1 rfl).hom
        ((H0Iso _).inv.hom (unitsInvariantOpen (U : Subgroup Gal(Ksep/K)) a)) = y := by
  obtain ⟨v, hv⟩ := exists_δ_H0Iso_inv_eq (kummerSeqOpen_shortExact hn (U : Subgroup Gal(Ksep/K)))
    (subsingleton_cohomology_one_kummerSeqOpen_X₂ K Ksep (n := n) U) y
  obtain ⟨a, rfl⟩ := exists_unitsInvariantOpen_eq (U : Subgroup Gal(Ksep/K)) v
  exact ⟨a, hv⟩

variable (n) in

def openChar (U : OpenSubgroup Gal(Ksep/K)) (z : cocycles (zmodRep.{0} (U : Subgroup Gal(Ksep/K)) n) 1) :
    Additive Gal(Ksep/fixedField (U : Subgroup Gal(Ksep/K))) →ₜ+ QZ where
  toFun σ := zmodToQZ n (zmodCocycleHom z (galFixedFieldEquivOpen U (Additive.toMul σ)))
  map_zero' := by
    have h0 : zmodCocycleHom z 1 = 0 := by
      have h := zmodCocycleHom_mul z 1 1
      rw [mul_one] at h
      simpa using h
    simp only [toMul_zero, map_one, h0, map_zero]
  map_add' σ τ := by
    simp only [toMul_add, map_mul, zmodCocycleHom_mul, map_add]
  continuous_toFun :=
    (((isLocallyConstant_zmodCocycleHom z).comp_continuous
      ((continuous_galFixedFieldEquivOpen U).comp continuous_toMul)).comp (zmodToQZ n)).continuous

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem openChar_apply (U : OpenSubgroup Gal(Ksep/K))
    (z : cocycles (zmodRep.{0} (U : Subgroup Gal(Ksep/K)) n) 1)
    (σ : Additive Gal(Ksep/fixedField (U : Subgroup Gal(Ksep/K)))) :
    openChar n U z σ = zmodToQZ n (zmodCocycleHom z (galFixedFieldEquivOpen U (Additive.toMul σ))) :=
  rfl

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem res_galUnits_ρ_galFixedFieldEquivOpen (U : OpenSubgroup Gal(Ksep/K))
    (σ : Gal(Ksep/fixedField (U : Subgroup Gal(Ksep/K)))) (x : Additive Ksepˣ) :
    (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galUnits.{0} K Ksep)).ρ (galFixedFieldEquivOpen U σ) x =
      (galUnitsZ (fixedField (U : Subgroup Gal(Ksep/K))) Ksep).ρ σ x := by
  apply Additive.toMul.injective
  apply Units.ext
  rfl

theorem cupPairing_δ_unitsInvariantOpen_eq_zero_iff (hn : (n : K) ≠ 0) (U : OpenSubgroup Gal(Ksep/K))
    (z : cocycles (zmodRep.{0} (U : Subgroup Gal(Ksep/K)) n) 1)
    (a : (fixedField (U : Subgroup Gal(Ksep/K)))ˣ) :
    cupPairing (zmodMulPairing n (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep n))
        (nsmul_res_galRootsOfUnity_eq_zero hn _)) (show 1 + 1 = 2 from rfl) (cohomologyπ _ 1 z)
        ((δ (kummerSeqOpen_shortExact hn (U : Subgroup Gal(Ksep/K))) 0 1 rfl).hom
          ((H0Iso _).inv.hom (unitsInvariantOpen (U : Subgroup Gal(Ksep/K)) a))) = 0 ↔
      ∃ y : fixedField (charKer (charAdd (openChar n U z))),
        Algebra.norm (fixedField (U : Subgroup Gal(Ksep/K))) y =
          (a : fixedField (U : Subgroup Gal(Ksep/K))) := by
  have hn0 := ne_zero_of_natCast_ne_zero' hn
  have : NeZero n := ⟨hn0⟩
  rw [← galCupClass_eq_zero_iff_of_isSepClosure (openChar n U z) a,
    ← (injective_cohomologyMap_kummerSeqOpen_f_two hn U).eq_iff, map_zero,
    cohomologyMap_cupPairing_zmodMul_δ hn]
  obtain ⟨w, hw, hwc⟩ := exists_cocycle_cupPairing_δ_bockSeq hn0
    (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galUnits.{0} K Ksep)) z
    (unitsInvariantOpen (U : Subgroup Gal(Ksep/K)) a)
  obtain ⟨w', hw', hwc'⟩ := exists_cocycle_cupCharClassProf
    (galUnitsZ (fixedField (U : Subgroup Gal(Ksep/K))) Ksep) (openChar n U z)
    (unitsInvariant (fixedField (U : Subgroup Gal(Ksep/K))) Ksep a)
  rw [← hw, galCupClass, ← hw', cohomologyπ_two_eq_zero_iff, cohomologyπ_two_eq_zero_iff]
  refine exists_coboundary_iff_of_mulEquiv (galFixedFieldEquivOpen U)
    (continuous_galFixedFieldEquivOpen U) (continuous_galFixedFieldEquivOpen_symm U) _ _
    (res_galUnits_ρ_galFixedFieldEquivOpen U) _ _ fun g h => ?_
  rw [hwc, hwc', charCocycle_eq_bockInt (fun σ => zmodCocycleHom z (galFixedFieldEquivOpen U σ))
    (charAdd (openChar n U z)) (fun σ => rfl)]
  rfl

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem zmodCocycleHom_eq_zero_of_charKer_eq_top (hn : (n : K) ≠ 0) (U : OpenSubgroup Gal(Ksep/K))
    (z : cocycles (zmodRep.{0} (U : Subgroup Gal(Ksep/K)) n) 1)
    (h : charKer (charAdd (openChar n U z)) = ⊤) (g : (U : Subgroup Gal(Ksep/K))) :
    zmodCocycleHom z g = 0 := by
  have : NeZero n := ⟨ne_zero_of_natCast_ne_zero' hn⟩
  obtain ⟨σ, rfl⟩ := (galFixedFieldEquivOpen U).surjective g
  have hσ : σ ∈ charKer (charAdd (openChar n U z)) := h ▸ Subgroup.mem_top σ
  rw [mem_charKer, charAdd_apply, openChar_apply, AddEquiv.map_eq_zero_iff] at hσ
  exact zmodToQZ_injective (hσ.trans (map_zero _).symm)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem exists_cocycle_charKer_eq (hn : (n : K) ≠ 0) (U : OpenSubgroup Gal(Ksep/K))
    (ψ : Gal(Ksep/fixedField (U : Subgroup Gal(Ksep/K))) →* Multiplicative (ZMod n))
    (hψ : IsOpen (ψ.ker : Set Gal(Ksep/fixedField (U : Subgroup Gal(Ksep/K))))) :
    ∃ z : cocycles (zmodRep.{0} (U : Subgroup Gal(Ksep/K)) n) 1,
      charKer (charAdd (openChar n U z)) = ψ.ker := by
  have : NeZero n := ⟨ne_zero_of_natCast_ne_zero' hn⟩
  have hlc : IsLocallyConstant fun σ : Gal(Ksep/fixedField (U : Subgroup Gal(Ksep/K))) => ψ σ := by
    intro s
    refine isOpen_iff_forall_mem_open.2 fun x hx => ⟨(fun y => x⁻¹ * y) ⁻¹' (ψ.ker : Set _), ?_,
      hψ.preimage (continuous_const_mul x⁻¹), by simp⟩
    intro y hy
    simp only [Set.mem_preimage, SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv] at hy
    have hxy : ψ y = ψ x := (inv_mul_eq_one.1 hy).symm
    simpa [Set.mem_preimage, hxy] using hx
  let f : ↥(U : Subgroup Gal(Ksep/K)) → zmodRep.{0} (U : Subgroup Gal(Ksep/K)) n :=
    fun g => ULift.up (Multiplicative.toAdd (ψ ((galFixedFieldEquivOpen U).symm g)))
  have hf : IsLocallyConstant f :=
    ((hlc.comp_continuous (continuous_galFixedFieldEquivOpen_symm U)).comp
      (fun m => (ULift.up (Multiplicative.toAdd m) : zmodRep.{0} (U : Subgroup Gal(Ksep/K)) n)))
  have hmul : ∀ g h, f (g * h) = f g + f h := fun g h => by
    apply ULift.ext
    simp [f, toAdd_mul]
  refine ⟨cocyclesOneOfHom _ (fun _ _ => rfl) f hf hmul, ?_⟩
  have hz : ∀ g, zmodCocycleHom (cocyclesOneOfHom _ (fun _ _ => rfl) f hf hmul) g =
      Multiplicative.toAdd (ψ ((galFixedFieldEquivOpen U).symm g)) := fun g =>
    congrArg ULift.down (cochainOf_cocyclesOneOfHom _ (fun _ _ => rfl) f hf hmul ![g])
  ext σ
  rw [mem_charKer, charAdd_apply, openChar_apply, AddEquiv.map_eq_zero_iff, toMul_ofMul, hz,
    MulEquiv.symm_apply_apply, MonoidHom.mem_ker, ← toAdd_eq_zero]
  exact ⟨fun h => zmodToQZ_injective (h.trans (map_zero _).symm), fun h => by rw [h, map_zero]⟩

end Local

end GroundTheory.ProfCoh
