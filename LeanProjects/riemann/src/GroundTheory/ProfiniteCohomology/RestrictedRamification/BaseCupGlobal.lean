import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseCupGlob
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseCupLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits MonoidalCategory GroundTheory.GroupCoh

section ConstCup

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type} {H : ι → Type} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)] [∀ v, IsTopologicalGroup (H v)]
  (φ : ∀ v, H v →ₜ* G)

omit [TopologicalSpace G] [IsTopologicalGroup G] in

theorem cupCochain_const_left {A B : Rep.{0} k G} {q n : ℕ} (h : 0 + q = n) (m : A) (g : (Fin q → G) → B)
    (x : Fin n → G) :
    cupCochain h (fun _ => m) g x = m ⊗ₜ[k] g (fun j : Fin q => x ⟨j, by omega⟩) := by
  rw [cupCochain_apply]
  congr 1
  have h0 : Fin.partialProd x ⟨0, by omega⟩ = 1 := Fin.partialProd_zero x
  rw [h0, map_one, Module.End.one_apply]
  congr 1
  funext j
  congr 1
  ext
  simp

variable {U X B : Rep.{0} k G} [IsDiscreteRep U] [IsDiscreteRep X] [IsDiscreteRep B] (j : U ⟶ X)
  (μU : U ⊗ B ⟶ U) (μX : X ⊗ B ⟶ X) (hj : μU ≫ j = (j ⊗ₘ 𝟙 B) ≫ μX)

noncomputable def constCupSub (m : X) {s : ℕ} (e : (cochainsComplex B).X s) (z : (cochainsComplex U).X s) :
    (cochainsComplex X).X s :=
  cupPairingCochains μX (show 0 + s = s by omega) (constCochain X m) e - ((cochainsMap j).f s).hom z

theorem cochainOf_constCupSub (m : X) {s : ℕ} (e : (cochainsComplex B).X s) (z : (cochainsComplex U).X s)
    (σ : Fin s → G) :
    cochainOf X (constCupSub j μX m e z) σ = μX.hom (m ⊗ₜ[k] cochainOf B e σ) - j.hom (cochainOf U z σ) := by
  change cochainOf X (cupPairingCochains μX (show 0 + s = s by omega) (constCochain X m) e) σ -
    cochainOf X (((cochainsMap j).f s).hom z) σ = _
  rw [cochainOf_cochainsMap_f, cochainOf_cupPairingCochains]
  congr 1
  refine (congrArg μX.hom (cupCochain_const_left (show 0 + s = s by omega) m _ σ)).trans ?_
  congr 3

include hj in

theorem d_constCupSub (m : X) (x : (cochainsComplex U).X 1)
    (hx : ((cochainsMap j).f 1).hom x = ((cochainsComplex X).d 0 1).hom (constCochain X m))
    {s : ℕ} (e : (cochainsComplex B).X s) (he : ((cochainsComplex B).d s (s + 1)).hom e = 0)
    (z : (cochainsComplex U).X s)
    (hz : ((cochainsComplex U).d s (s + 1)).hom z = cupPairingCochains μU (show 1 + s = s + 1 by omega) x e) :
    ((cochainsComplex X).d s (s + 1)).hom (constCupSub j μX m e z) = 0 := by
  have L := (cupLeibniz μX).leibniz (show 0 + s = s by omega) (constCochain X m) e
  change ((cochainsComplex X).d s (s + 1)).hom (cupPairingCochains μX _ (constCochain X m) e) = _ at L
  rw [constCupSub, map_sub, L, he, map_zero, smul_zero, add_zero, ← hx,
    hom_apply_hom_apply_eq_of_comp_eq ((cochainsMap j).comm s (s + 1)) z, hz, sub_eq_zero]
  apply cochainOf_injective
  funext σ
  rw [cochainOf_cochainsMap_f]
  exact (cupCochain_tensorHom_eq' ((j ⊗ₘ 𝟙 B) ≫ μX) μX j rfl (show 1 + s = s + 1 by omega) (cochainOf U x)
    (cochainOf B e) σ).symm.trans (congrArg (fun f : U ⊗ B ⟶ X =>
      f.hom (cupCochain (show 1 + s = s + 1 by omega) (cochainOf U x) (cochainOf B e) σ)) hj.symm)

variable (Ωᵥ : ∀ v, Rep.{0} k (H v)) [∀ v, IsDiscreteRep (Ωᵥ v)] (l : ∀ v, Rep.res (φ v).toMonoidHom X ⟶ Ωᵥ v)
  (μΩ : ∀ v, Ωᵥ v ⊗ Rep.res (φ v).toMonoidHom B ⟶ Ωᵥ v)
  (hl : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map μX ≫ l v = resTensorHom (φ v).toMonoidHom (l v) (𝟙 _) ≫ μΩ v)

include hj hl in

theorem exists_compactCup_const
    (hμ : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map μU ≫ ((Rep.resFunctor (φ v).toMonoidHom).map j ≫ l v) =
      resTensorHom (φ v).toMonoidHom ((Rep.resFunctor (φ v).toMonoidHom).map j ≫ l v) (𝟙 _) ≫ μΩ v)
    (Xc : (compactCochains φ U Ωᵥ (fun v => (Rep.resFunctor (φ v).toMonoidHom).map j ≫ l v)).cycles 1)
    (m : X) (x : (cochainsComplex U).X 1)
    (hX1 : (((compactCochains φ U Ωᵥ _).iCycles 1).hom Xc).1 = x) (y : ∀ v, Ωᵥ v)
    (hX2 : (((compactCochains φ U Ωᵥ _).iCycles 1).hom Xc).2 = piConst Ωᵥ y) (hy : ∀ v, y v = (l v).hom m)
    (hx : ((cochainsMap j).f 1).hom x = ((cochainsComplex X).d 0 1).hom (constCochain X m))
    {s : ℕ} (e : (cochainsComplex B).cycles s) (z : (cochainsComplex U).X s)
    (hz : ((cochainsComplex U).d s (s + 1)).hom z =
      cupPairingCochains μU (show 1 + s = s + 1 by omega) x (((cochainsComplex B).iCycles s).hom e)) :
    ∃ W : cocycles X s, cochainOf X (cocycleι X s W) =
        cochainOf X (constCupSub j μX m (((cochainsComplex B).iCycles s).hom e) z) ∧
      compactCup φ μU μΩ hμ (show 1 + s = s + 1 by omega)
          (((compactCochains φ U Ωᵥ _).homologyπ 1).hom Xc) (((cochainsComplex B).homologyπ s).hom e) =
        (localToCompact φ U Ωᵥ (fun v => (Rep.resFunctor (φ v).toMonoidHom).map j ≫ l v) s).hom
          (fun v => (cohomologyMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v)) (l v) s).hom
            (cohomologyπ X s W)) := by
  have hdW := d_constCupSub j μU μX hj m x hx (((cochainsComplex B).iCycles s).hom e)
    (iCycles_d_apply _ s (s + 1) e) z hz
  let W : cocycles X s := (cochainsComplex X).cyclesMk _ (s + 1) (by simp) hdW
  have hW : cochainOf X (cocycleι X s W) = cochainOf X (constCupSub j μX m (((cochainsComplex B).iCycles s).hom e) z) :=
    congrArg (cochainOf X) ((cochainsComplex X).i_cyclesMk _ _ _ _)
  refine ⟨W, hW, ?_⟩
  obtain ⟨w, hw1, hw2⟩ := LeibnizPairing.exists_coconeLeft_homology_eq_homologyδ
    (LeibnizPairing.pi fun v => cupLeibniz (μΩ v))
    (localRes φ B (fun v => Rep.res (φ v).toMonoidHom B) fun _ => 𝟙 _) (cupLeibniz μU)
    (localRes_cupPairingCochains φ μU μΩ hμ) (show 0 + 1 + s = s + 1 by omega) Xc e z
    (hz.trans (congrArg (fun a => cupPairingCochains μU (show 1 + s = s + 1 by omega) a
      (((cochainsComplex B).iCycles s).hom e)) hX1.symm))
  refine hw2.trans ((homologyδ_homologyπ_eq_localToCompact φ w).trans (congrArg _ (funext fun v => ?_)))
  rw [cohomologyMapAlong_cohomologyπ]
  congr 1
  apply cocycles_ext
  rw [cochainOf_cocycleι_cocyclesMapAlong, hW]
  funext σ
  have e1 := iCycles_cyclesMap_apply (piProj (fun v => cochainsComplex (Ωᵥ v)) v) s w
  rw [cocycleι, e1, piProj_f_hom_apply, hw1, cochainOf_constCupSub, map_sub]
  change cochainOf (Ωᵥ v) (cupPairingCochains (μΩ v) (show 0 + s = s by omega)
      ((((compactCochains φ U Ωᵥ _).iCycles 1).hom Xc).2 v)
      (((localRes φ B (fun v => Rep.res (φ v).toMonoidHom B) fun _ => 𝟙 _).f s).hom
        (((cochainsComplex B).iCycles s).hom e) v)) σ -
    cochainOf (Ωᵥ v) (((localRes φ U Ωᵥ fun v => (Rep.resFunctor (φ v).toMonoidHom).map j ≫ l v).f s).hom z v) σ = _
  rw [hX2, piConst_apply, cochainOf_cupPairingCochains, cochainOf_localRes_f_apply]
  congr 1
  refine (congrArg (μΩ v).hom (cupCochain_const_left (show 0 + s = s by omega) (y v) _ σ)).trans ?_
  rw [hy v]
  refine Eq.trans ?_ (congrArg (fun f => f.hom ((m ⊗ₜ[k] cochainOf B (((cochainsComplex B).iCycles s).hom e)
    (⇑(φ v).toMonoidHom ∘ σ)) : Rep.res (φ v).toMonoidHom (X ⊗ B))) (hl v)).symm
  rfl

end ConstCup

section Exists

theorem nsmul_apply_eq_zero_of {F M N : Type*} [AddMonoid M] [AddMonoid N] [FunLike F M N] [AddMonoidHomClass F M N]
    (f : F) (n : ℕ) {y : M} (hy : n • y = 0) : n • f y = 0 := by
  rw [← map_nsmul, hy, map_zero]

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A B C : Rep.{0} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]

theorem exists_d_eq_cupPairingCochains (μ : A ⊗ B ⟶ C) {p q m : ℕ} (h : p + q = m + 1) (x : cocycles A p)
    (y : cocycles B q) (h0 : cupPairing μ h (cohomologyπ A p x) (cohomologyπ B q y) = 0) :
    ∃ z : (cochainsComplex C).X m, ((cochainsComplex C).d m (m + 1)).hom z =
      cupPairingCochains μ h (cocycleι A p x) (cocycleι B q y) := by
  rw [cupPairing_cohomologyπ] at h0
  have h1 := (homologyπ_eq_zero_iff (cochainsComplex C) _).1 h0
  rw [CochainComplex.prev_nat_succ] at h1
  obtain ⟨z, hz⟩ := h1
  refine ⟨z, hz.trans (cochainOf_injective (funext fun σ => ?_))⟩
  exact (cochainOf_cocycleι_cyclesMap_cupCocycles μ h x y σ).trans rfl

end Exists

section Units

theorem toMul_zsmul_sub_mul_inv_mem {M : Type*} [CommGroup M] (H : Subgroup M) (u : M) (b : ℤ) (w : M) (hw : w ∈ H) :
    Additive.toMul (b • Additive.ofMul u - Additive.ofMul w) * (u ^ b)⁻¹ ∈ H := by
  have e : Additive.toMul (b • Additive.ofMul u - Additive.ofMul w) * (u ^ b)⁻¹ = w⁻¹ := by
    rw [toMul_sub, toMul_zsmul, toMul_ofMul, toMul_ofMul, div_eq_mul_inv, mul_comm (u ^ b) w⁻¹, mul_assoc,
      mul_inv_cancel, mul_one]
  rw [e]
  exact H.inv_mem hw

theorem toMul_mem_of_eq {M : Type*} [CommGroup M] (H : Subgroup M) (u : M) (b : ℤ) (w : M) (X : Additive M)
    (hX : X = b • Additive.ofMul u - Additive.ofMul w) (hw : w ∈ H) : Additive.toMul X * (u ^ b)⁻¹ ∈ H := by
  rw [hX]
  exact toMul_zsmul_sub_mul_inv_mem H u b w hw

end Units

section Concrete

open IsDedekindDomain NumberField GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))

noncomputable abbrev gsPairingK :
    galUnits.{0, 0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) ⊗ intRepTriv (galUnramifiedOutside K.1 ℚ̄ S) ⟶
      galUnits.{0, 0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) :=
  intActPairing _ _ (AddEquiv.ulift : ULift.{0} ℤ ≃+ ℤ).toAddMonoidHom (fun _ _ => rfl)

theorem gsPairingK_tmul (x : galUnits.{0, 0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S))
    (m : intRepTriv (galUnramifiedOutside K.1 ℚ̄ S)) :
    (gsPairingK S).hom (x ⊗ₜ[ULift.{0} ℤ] m) = m.down • x :=
  intActPairing_tmul _ _ _ _ x m

theorem gsPairingU_sUnitsToUnits :
    gsPairingU S ≫ sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S) =
      (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S) ⊗ₘ 𝟙 (intRepTriv (galUnramifiedOutside K.1 ℚ̄ S))) ≫
        gsPairingK S := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (TensorProduct.ext'
    fun (x : galSUnitsMax K.1 ℚ̄ S) (m : intRepTriv (galUnramifiedOutside K.1 ℚ̄ S)) => ?_))
  change (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)).hom ((gsPairingU S).hom (x ⊗ₜ[ULift.{0} ℤ] m)) =
    (gsPairingK S).hom ((sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)).hom x ⊗ₜ[ULift.{0} ℤ] m)
  exact (congrArg (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)).hom (gsPairingU_tmul S x m)).trans
    ((map_zsmul (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)).hom m.down x).trans
      (gsPairingK_tmul S _ m).symm)

theorem gsPairingK_gsUnitsLocalMor (v : S) :
    (Rep.resFunctor (gsFinFamily S ιs v).toMonoidHom).map (gsPairingK S) ≫ gsUnitsLocalMor.{0} S ιs v =
      resTensorHom (gsFinFamily S ιs v).toMonoidHom (gsUnitsLocalMor.{0} S ιs v) (𝟙 _) ≫
        mulIntRight (gsFinFamily S ιs v).toMonoidHom (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (TensorProduct.ext'
    fun (x : galUnits.{0, 0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S))
      (m : intRepTriv (galUnramifiedOutside K.1 ℚ̄ S)) => ?_))
  change (gsUnitsLocalMor.{0} S ιs v).hom ((gsPairingK S).hom (x ⊗ₜ[ULift.{0} ℤ] m)) =
    (mulIntRight (gsFinFamily S ιs v).toMonoidHom (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))).hom ((gsUnitsLocalMor.{0} S ιs v).hom x ⊗ₜ[ULift.{0} ℤ]
      (ULift.up m.down : Rep.res (gsFinFamily S ιs v).toMonoidHom (intRepTriv (galUnramifiedOutside K.1 ℚ̄ S))))
  exact (congrArg (gsUnitsLocalMor.{0} S ιs v).hom (gsPairingK_tmul S x m)).trans
    ((map_zsmul (gsUnitsLocalMor.{0} S ιs v).hom m.down x).trans
      (mulIntRight_tmul (gsFinFamily S ιs v).toMonoidHom (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) _ m.down).symm)

variable [Fintype S] (n ℓ k : ℕ) [NeZero n] (hℓ : ℓ.Prime) (hnk : n = ℓ ^ k)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)

set_option maxHeartbeats 1600000 in
omit [Fintype S] in
include hℓ hnk hS in

theorem exists_gsUnitsData_cup_bock (t : sInvariantSubgroup (F := K.1) ℚ̄ S)
    (z : cocycles (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1) :
    ∃ W : cocycles (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2,
      (∀ g h, (Additive.toMul (cochainOf _ (cocycleι _ 2 W) ![g, h]) : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) *
          ((t : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) ^ bockInt (zmodCocycleHom z) g h)⁻¹ ∈ sUnitsMax K.1 ℚ̄ S) ∧
      compactCup (gsFinFamily S ιs) (gsPairingU S)
          (fun v => mulIntRight (gsFinFamily S ιs v).toMonoidHom (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))) (gsPairingU_hμ S ιs)
          (show 1 + 2 = 2 + 1 from rfl) (gsUnitsData S ιs (Additive.ofMul t, 0))
          ((δ (bockSeq_shortExact (galUnramifiedOutside K.1 ℚ̄ S) n (NeZero.ne n)) 1 2 rfl).hom
            (cohomologyπ _ 1 z)) =
        (localToCompact (gsFinFamily S ιs) (galSUnitsMax K.1 ℚ̄ S) (fun v => galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) (gsSUnitsLocalMor S ιs) 2).hom
          (fun v => (cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
            (gsUnitsLocalMor S ιs v) 2).hom (cohomologyπ _ 2 W)) := by
  have hb := exists_cocycle_δ_bockSeq (NeZero.ne n) z
  obtain ⟨x₁, hx₁π, hx₁v⟩ := hb
  let c : cocycles (galSUnitsMax K.1 ℚ̄ S) 1 :=
    (cochainsComplex (galSUnitsMax K.1 ℚ̄ S)).cyclesMk (sInvCochain S t) 2 (by simp) (d_sInvCochain S t)
  have hc : cocycleι _ 1 c = sInvCochain S t := (cochainsComplex (galSUnitsMax K.1 ℚ̄ S)).i_cyclesMk _ _ _ _
  have hnz : n • cohomologyπ (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1 z = 0 :=
    nsmul_cohomology_eq_zero _ (fun a => ULift.ext _ _ (by
      change n • a.down = 0
      rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul])) 1 _
  have hb' : n • cohomologyπ _ 2 x₁ = 0 :=
    (congrArg (n • ·) hx₁π).trans (nsmul_apply_eq_zero_of
      (δ (bockSeq_shortExact (galUnramifiedOutside K.1 ℚ̄ S) n (NeZero.ne n)) 1 2 rfl).hom n hnz)
  have h0 : cupPairing (gsPairingU S) (show 1 + 2 = 2 + 1 from rfl) (cohomologyπ _ 1 c) (cohomologyπ _ 2 x₁) = 0 := by
    refine eq_zero_of_h3_sUnits K S ℓ hℓ hS _ k ?_
    rw [← hnk]
    exact nsmul_apply_eq_zero_of (cupPairing (gsPairingU S) (show 1 + 2 = 2 + 1 from rfl) (cohomologyπ _ 1 c)) n hb'
  have hz := exists_d_eq_cupPairingCochains (gsPairingU S) (show 1 + 2 = 2 + 1 from rfl) c x₁ h0
  have hz₀' := hz.choose_spec.trans (congrArg (fun a => cupPairingCochains (gsPairingU S)
    (show 1 + 2 = 2 + 1 from rfl) a (cocycleι _ 2 x₁)) hc)
  have hX := iCycles_dataCycle (gsFinFamily S ιs) (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S))
    (fun v : S => galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) (gsUnitsLocalMor.{0} S ιs)
    (sInvCochain S (Additive.toMul ((Additive.ofMul t, 0) : GsUnitsDatum S).1))
    (fun v => dataLocalUnit S ιs (Additive.toMul ((Additive.ofMul t, 0) : GsUnitsDatum S).1) v
      (((Additive.ofMul t, 0) : GsUnitsDatum S).2 v))
    (d_sInvCochain S _) (fun v σ => dataLocalUnit_compat S ιs (Additive.toMul ((Additive.ofMul t, 0) : GsUnitsDatum S).1)
      ((Additive.ofMul t, 0) : GsUnitsDatum S).2 v σ)
  have key := exists_compactCup_const (U := galSUnitsMax K.1 ℚ̄ S)
    (X := galUnits.{0, 0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) (B := intRepTriv (galUnramifiedOutside K.1 ℚ̄ S))
    (gsFinFamily S ιs) (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S))
    (gsPairingU S) (gsPairingK S) (gsPairingU_sUnitsToUnits S) (fun v : S => galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) (gsUnitsLocalMor.{0} S ιs)
    (fun v => mulIntRight (gsFinFamily S ιs v).toMonoidHom (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))) (gsPairingK_gsUnitsLocalMor S ιs)
    (gsPairingU_hμ S ιs) _ (Additive.ofMul (t : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ)) (sInvCochain S t)
    (congrArg Prod.fst hX) _ (congrArg Prod.snd hX)
    (fun v => (congrArg (· + sInvLocalHom S ιs v (Additive.ofMul t)) (map_zero (localUnitsAlgHom S v))).trans
      (zero_add _))
    (cochainsMap_sUnitsToUnits_sInvCochain S t) x₁ hz.choose hz₀'
  refine ⟨key.choose, fun g h => ?_, ?_⟩
  · have e1 := (congrFun key.choose_spec.1 ![g, h]).trans (cochainOf_constCupSub _ _ _ _ _ _)
    have e2 := gsPairingK_tmul S (Additive.ofMul (t : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ))
      (cochainOf _ (cocycleι _ 2 x₁) ![g, h])
    have e3 := sUnitsToUnits_hom_apply S (maxUnramifiedOutside K.1 ℚ̄ S) (cochainOf _ hz.choose ![g, h])
    exact toMul_mem_of_eq (sUnitsMax K.1 ℚ̄ S) _ _ _ _
      (e1.trans (congrArg₂ (· - ·) (e2.trans (congrArg (· • Additive.ofMul (t : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ))
        (hx₁v g h))) e3))
      (Additive.toMul (cochainOf _ hz.choose ![g, h]) : sUnitsMax K.1 ℚ̄ S).2
  · exact (congrArg _ hx₁π.symm).trans key.choose_spec.2

end Concrete

end GroundTheory.ProfCoh
