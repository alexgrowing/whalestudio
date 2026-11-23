import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseDefs
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseFormal
import GroundTheory.ProfiniteCohomology.LocalTateDuality.TensorHomDualRepRootsOfUnityIsoCartierPairing
import GroundTheory.ProfiniteCohomology.PoincareDuality
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory MonoidalCategory GroundTheory.Global GroundTheory.LocalField

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

attribute [local instance 2000] Rep.hV2

universe u

section RootsMap

variable {M N : Type*} [CommMonoid M] [CommMonoid N] (n : ℕ)

def rootsOfUnityMapHom (f : M →* N) : rootsOfUnity n M →* rootsOfUnity n N :=
  ((Units.map f).comp (rootsOfUnity n M).subtype).codRestrict (rootsOfUnity n N) fun ζ => by
    rw [MonoidHom.comp_apply, mem_rootsOfUnity, ← map_pow]
    exact (congrArg (Units.map f) ((mem_rootsOfUnity n _).1 ζ.2)).trans (map_one _)

theorem coe_rootsOfUnityMapHom (f : M →* N) (ζ : rootsOfUnity n M) :
    ((rootsOfUnityMapHom n f ζ : Nˣ) : N) = f ((ζ : Mˣ) : M) :=
  rfl

end RootsMap

section RootsMapField

variable {M N : Type*} [Field M] [Field N] (n : ℕ) [NeZero n]

theorem bijective_rootsOfUnityMapHom (f : M →+* N) {z : M} (hz : IsPrimitiveRoot z n) :
    Function.Bijective (rootsOfUnityMapHom n f.toMonoidHom) := by
  refine ⟨fun a b h => ?_, fun ω => ?_⟩
  · have e : f ((a : Mˣ) : M) = f ((b : Mˣ) : M) := congrArg (fun x : rootsOfUnity n N => ((x : Nˣ) : N)) h
    exact Subtype.ext (Units.ext (f.injective e))
  · have hω : IsPrimitiveRoot (f z) n := hz.map_of_injective f.injective
    obtain ⟨i, -, hi⟩ := hω.eq_pow_of_pow_eq_one (ξ := ((ω : Nˣ) : N))
      (by rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity n _).1 ω.2, Units.val_one])
    refine ⟨hz.toRootsOfUnity ^ i, Subtype.ext (Units.ext ?_)⟩
    rw [coe_rootsOfUnityMapHom, ← hi]
    change f (((hz.toRootsOfUnity : Mˣ) ^ i : Mˣ) : M) = f z ^ i
    rw [Units.val_pow_eq_pow_val, IsPrimitiveRoot.val_toRootsOfUnity_coe, map_pow]

end RootsMapField

section IsoOfBijective

variable {k Γ : Type u} [CommRing k] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] in

def invOfBijective {A B : Rep.{u} k Γ} (f : A ⟶ B) (hf : Function.Bijective f.hom) : B ⟶ A :=
  Rep.ofHom ⟨(LinearEquiv.ofBijective f.hom.toLinearMap hf).symm.toLinearMap, fun g => LinearMap.ext fun b => by
    set e := LinearEquiv.ofBijective f.hom.toLinearMap hf
    apply e.injective
    change e (e.symm (B.ρ g b)) = f.hom (A.ρ g (e.symm b))
    rw [e.apply_symm_apply, Rep.hom_comm_apply]
    change B.ρ g b = B.ρ g (e (e.symm b))
    rw [e.apply_symm_apply]⟩

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] in
theorem comp_invOfBijective {A B : Rep.{u} k Γ} (f : A ⟶ B) (hf : Function.Bijective f.hom) :
    f ≫ invOfBijective f hf = 𝟙 A :=
  Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun a =>
    (LinearEquiv.ofBijective f.hom.toLinearMap hf).symm_apply_apply a))

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] in
theorem invOfBijective_comp {A B : Rep.{u} k Γ} (f : A ⟶ B) (hf : Function.Bijective f.hom) :
    invOfBijective f hf ≫ f = 𝟙 B :=
  Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun b =>
    (LinearEquiv.ofBijective f.hom.toLinearMap hf).apply_symm_apply b))

theorem bijective_cohomologyMap_of_bijective {A B : Rep.{u} k Γ} [IsDiscreteRep A] [IsDiscreteRep B]
    (f : A ⟶ B) (hf : Function.Bijective f.hom) (m : ℕ) : Function.Bijective (cohomologyMap f m).hom :=
  bijective_cohomologyMap_of_comp_eq_id f (invOfBijective f hf) (comp_invOfBijective f hf)
    (invOfBijective_comp f hf) m

end IsoOfBijective

section CompApply

variable {k Γ : Type u} [CommRing k] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

theorem cohomologyMap_comp_hom_apply {A B C : Rep.{u} k Γ} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
    (f : A ⟶ B) (g : B ⟶ C) (m : ℕ) (z : cohomology A m) :
    (cohomologyMap (f ≫ g) m).hom z = (cohomologyMap g m).hom ((cohomologyMap f m).hom z) := by
  rw [cohomologyMap_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

end CompApply

section AbstractLocal

variable {F Fsep : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field Fsep] [Algebra F Fsep] [IsSepClosure F Fsep]

theorem brauerInvZOfIsSepClosure_cohomologyMap_uliftInt_base (A : Rep.{0} (ULift.{0} ℤ) Gal(Fsep/F))
    [IsDiscreteRep A] (f : A ⟶ galUnits.{0} F Fsep) (f' : uliftIntToIntRep A ⟶ galUnitsZ.{0} F Fsep)
    (hf : ∀ a, f'.hom a = f.hom a) (z : cohomology A 2) :
    brauerInvZOfIsSepClosure F Fsep ((cohomologyMap f' 2).hom (cohomologyULiftIntAddEquiv A 2 z)) =
      brauerInvOfIsSepClosure F Fsep ((cohomologyMap f 2).hom z) := by
  have hnat : (cohomologyMap f' 2).hom (cohomologyULiftIntAddEquiv A 2 z) =
      cohomologyULiftIntAddEquiv (galUnits.{0} F Fsep) 2 ((cohomologyMap f 2).hom z) := by
    obtain ⟨w, rfl⟩ := cohomologyπ_surjective A 2 z
    change cohomologyMap f' 2 (cohomologyULiftIntAddEquiv A 2 (cohomologyπ A 2 w)) =
      cohomologyULiftIntAddEquiv (galUnits.{0} F Fsep) 2 (cohomologyMap f 2 (cohomologyπ A 2 w))
    rw [cohomologyULiftIntAddEquiv_cohomologyπ', cohomologyMap_cohomologyπ, cohomologyMap_cohomologyπ,
      cohomologyULiftIntAddEquiv_cohomologyπ']
    congr 1
    apply cocycles_ext
    rw [cochainOf_cocycleι_cyclesMap, cochainOf_cocycleι_cocyclesULiftInt]
    have : IsDiscreteRep (uliftIntToIntRep (galUnits.{0} F Fsep)) :=
      ⟨fun a => isOpen_stabilizer (galUnits.{0} F Fsep) a⟩
    change _ = cochainOf (uliftIntToIntRep (galUnits.{0} F Fsep)) (cocycleι (uliftIntToIntRep (galUnits.{0} F Fsep)) 2
      (cocyclesULiftInt _ _))
    rw [cochainOf_cocycleι_cocyclesULiftInt, cochainOf_cocycleι_cyclesMap]
    funext σ
    exact hf _
  rw [hnat]
  let := algebraicValuativeRel F Fsep
  let := algebraicTopology F Fsep
  have := algebraicTopology_isValuativeTopology F Fsep
  have := algebraicValuativeRel_valuativeExtension F Fsep
  exact brauerInvZ_cohomologyULiftIntAddEquiv F Fsep _

end AbstractLocal

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) (n : ℕ)

def gsRootsLocalMor (v : S) :
    Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n) ⟶
      galRootsOfUnity.{0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n :=
  Rep.ofHom ⟨(uliftIntLinearMap (MonoidHom.toAdditive (rootsOfUnityMapHom n
      ((ιs v).comp (maxUnramifiedOutside K.1 ℚ̄ S).val).toRingHom.toMonoidHom)) :
        Additive (rootsOfUnity n (maxUnramifiedOutside K.1 ℚ̄ S)) →ₗ[ULift.{0} ℤ]
          Additive (rootsOfUnity n (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))),
    fun σ => LinearMap.ext fun ζ => congrArg Additive.ofMul (Subtype.ext (Units.ext
      (gsFinFamily_apply S ιs v σ
        (((Additive.toMul ζ : rootsOfUnity n _) : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :
          maxUnramifiedOutside K.1 ℚ̄ S))))⟩

theorem gsRootsLocalMor_hom_apply (v : S) (ζ : Additive (rootsOfUnity n (maxUnramifiedOutside K.1 ℚ̄ S))) :
    (Additive.toMul ((gsRootsLocalMor S ιs n v).hom ζ)).val.val =
      ιs v ((Additive.toMul ζ).val.val : ℚ̄) :=
  rfl

set_option maxHeartbeats 1600000 in

theorem bijective_gsRootsLocalMor [NeZero n] (hμ : ∀ ζ : ℚ̄, ζ ^ n = 1 → ζ ∈ K.1) (v : S) :
    Function.Bijective (gsRootsLocalMor S ιs n v).hom := by
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℚ̄ n
  have hzS : z ∈ maxUnramifiedOutside K.1 ℚ̄ S := by
    obtain ⟨x, rfl⟩ : ∃ x : K.1, (x : ℚ̄) = z := ⟨⟨z, hμ z hz.pow_eq_one⟩, rfl⟩
    exact (maxUnramifiedOutside K.1 ℚ̄ S).algebraMap_mem x
  have hzS' : IsPrimitiveRoot (⟨z, hzS⟩ : maxUnramifiedOutside K.1 ℚ̄ S) n :=
    hz.of_map_of_injective (f := (maxUnramifiedOutside K.1 ℚ̄ S).val) Subtype.val_injective
  have hF := bijective_rootsOfUnityMapHom n ((ιs v).comp (maxUnramifiedOutside K.1 ℚ̄ S).val).toRingHom hzS'
  exact Additive.ofMul.bijective.comp (hF.comp Additive.toMul.bijective)

theorem gsLocalInvRootsQZ_eq_brauerInv_base (v : S)
    (z : cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 2) :
    gsLocalInvRootsQZ S ιs n v z =
      brauerInvOfIsSepClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
        ((cohomologyMap (gsRootsLocalMor S ιs n v ≫ rootsOfUnityToUnits ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n) 2).hom z) := by
  refine (DFunLike.congr_fun (gsLocalInvRootsQZ_eq S ιs n v) z).trans ?_
  refine (AddMonoidHom.comp_apply _ _ _).trans ?_
  refine (congrArg (brauerInvZOfIsSepClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
    (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) (AddMonoidHom.comp_apply _ _ _)).trans ?_
  exact brauerInvZOfIsSepClosure_cohomologyMap_uliftInt_base _ _ (rootsLocalMorZ S ιs n v) (fun _ => rfl) z

variable [NeZero n]

theorem natCast_ne_zero_adicCompletion (v : S) :
    (n : (v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) ≠ 0 :=
  Nat.cast_ne_zero.2 (NeZero.ne n)

theorem gsLocalInvRoots_eq (v : S) (z : cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 2) :
    gsLocalInvRoots S ιs n v z =
      (localDualityHypotheses (Ksep := AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
        (natCast_ne_zero_adicCompletion S n v)).tTop ((cohomologyMap (gsRootsLocalMor S ιs n v) 2).hom z) := by
  apply zmodToQZ_injective
  refine (zmodToQZ_gsLocalInvRoots S ιs n v z).trans ?_
  refine (gsLocalInvRootsQZ_eq_brauerInv_base S ιs n v z).trans ?_
  refine (congrArg (brauerInvOfIsSepClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
    (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))
      (cohomologyMap_comp_hom_apply _ _ 2 z)).trans ?_
  exact brauerInvOfIsSepClosure_rootsOfUnity (natCast_ne_zero_adicCompletion S n v) _

theorem bijective_localDualityHypotheses_tTop (v : S) :
    Function.Bijective (localDualityHypotheses (Ksep := AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
      (natCast_ne_zero_adicCompletion S n v)).tTop :=
  ((localDualityHypotheses (Ksep := AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
    (natCast_ne_zero_adicCompletion S n v)).t ⊤).bijective.comp (bijective_cohomologyRes_top _ 2)

theorem bijective_gsLocalInvRoots (hμ : ∀ ζ : ℚ̄, ζ ^ n = 1 → ζ ∈ K.1) (v : S) :
    Function.Bijective (gsLocalInvRoots S ιs n v) := by
  have e : ⇑(gsLocalInvRoots S ιs n v) =
      (localDualityHypotheses (Ksep := AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
        (natCast_ne_zero_adicCompletion S n v)).tTop ∘ (cohomologyMap (gsRootsLocalMor S ιs n v) 2).hom :=
    funext (gsLocalInvRoots_eq S ιs n v)
  rw [e]
  exact (bijective_localDualityHypotheses_tTop S n v).comp
    (bijective_cohomologyMap_of_bijective _ (bijective_gsRootsLocalMor S ιs n hμ v) 2)

end

end GroundTheory.ProfCoh
