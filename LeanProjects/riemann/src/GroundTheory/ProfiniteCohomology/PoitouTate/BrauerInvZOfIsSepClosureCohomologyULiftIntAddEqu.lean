import Mathlib
import GroundTheory.ProfiniteCohomology.PoitouTate.PtCompactDualMapEqZeroOfPtCompactToGlobalEqZero
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseDefs
import GroundTheory.ProfiniteCohomology.LocalTateDuality.TensorHomDualRepRootsOfUnityIsoCartierPairing
import GroundTheory.ProfiniteCohomology.CohomologyFunctoriality.Naturality
import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbolBridge
import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbolSep
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory MonoidalCategory GroundTheory.Global GroundTheory.LocalField

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

theorem bijective_of_bijective_precomp {X Y Y' Z : Type*} [AddCommGroup X] [AddCommGroup Y]
    [AddCommGroup Y'] [AddCommGroup Z] (β : X →+ Y →+ Z) (γ : X →+ Y' →+ Z) (e : Y ≃+ Y')
    (hβγ : ∀ x y, β x y = γ x (e y)) (hγ : Function.Bijective γ) : Function.Bijective β := by
  refine ⟨fun x₁ x₂ hx => hγ.1 (AddMonoidHom.ext fun y' => ?_), fun χ => ?_⟩
  · obtain ⟨y, rfl⟩ := e.surjective y'
    rw [← hβγ, ← hβγ, hx]
  · obtain ⟨x, hx⟩ := hγ.2 (χ.comp e.symm.toAddMonoidHom)
    refine ⟨x, AddMonoidHom.ext fun y => ?_⟩
    rw [hβγ, hx, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.symm_apply_apply]

section Generic

variable {k G H : Type} [CommRing k] [Group G] [Group H] (ψ : H →* G) (D M : Rep.{0} k G)
  (U : Rep.{0} k H) (ρ : Rep.res ψ D ⟶ U)

def resDualPost : Rep.res ψ (dualRep D M) ⟶ (Rep.ihom (Rep.res ψ M)).obj U :=
  Rep.ofHom ⟨{ toFun := fun f => ρ.hom.toLinearMap ∘ₗ f
               map_add' := fun f g => LinearMap.comp_add _ _ _
               map_smul' := fun r f => LinearMap.comp_smul _ _ _ },
    fun σ => LinearMap.ext fun f => LinearMap.ext fun m => by
      change ρ.hom (D.ρ (ψ σ) (f (M.ρ ((ψ σ)⁻¹) m))) = U.ρ σ (ρ.hom (f (M.ρ (ψ σ⁻¹) m)))
      rw [map_inv ψ σ]
      exact Rep.hom_comm_apply ρ σ _⟩

end Generic

section Abstract

variable {F Fsep : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field Fsep] [Algebra F Fsep] [IsSepClosure F Fsep]

theorem brauerInvZOfIsSepClosure_cohomologyULiftIntAddEquiv (x : galoisBrauerGroup F Fsep) :
    brauerInvZOfIsSepClosure F Fsep (cohomologyULiftIntAddEquiv (galUnits.{0} F Fsep) 2 x) =
      brauerInvOfIsSepClosure F Fsep x := by
  let _ := algebraicValuativeRel F Fsep
  let _ := algebraicTopology F Fsep
  have := algebraicTopology_isValuativeTopology F Fsep
  have := algebraicValuativeRel_valuativeExtension F Fsep
  exact brauerInvZ_cohomologyULiftIntAddEquiv F Fsep x

theorem brauerInvZOfIsSepClosure_cohomologyMap_uliftInt (A : Rep.{0} (ULift.{0} ℤ) Gal(Fsep/F))
    [IsDiscreteRep A] (f : A ⟶ galUnits.{0} F Fsep) (f' : uliftIntToIntRep A ⟶ galUnitsZ.{0} F Fsep)
    (hf : ∀ a, f'.hom a = f.hom a) (z : cohomology A 2) :
    brauerInvZOfIsSepClosure F Fsep ((cohomologyMap f' 2).hom (cohomologyULiftIntAddEquiv A 2 z)) =
      brauerInvOfIsSepClosure F Fsep ((cohomologyMap f 2).hom z) := by
  have hnat := cohomologyULiftIntAddEquiv_cohomologyMapAlong A (MonoidHom.id _) continuous_id f f' hf 2 z
  rw [cohomologyMapAlong_id_eq_cohomologyMap] at hnat
  rw [← brauerInvZOfIsSepClosure_cohomologyULiftIntAddEquiv, hnat]
  exact congrArg _ (ConcreteCategory.congr_hom (cohomologyMapAlong_id_eq_cohomologyMap f' 2) _).symm

theorem brauerInvZOfIsSepClosure_comp_cohomologyMap_uliftInt (A : Rep.{0} (ULift.{0} ℤ) Gal(Fsep/F))
    [IsDiscreteRep A] (f : A ⟶ galUnits.{0} F Fsep) (f' : uliftIntToIntRep A ⟶ galUnitsZ.{0} F Fsep)
    (hf : ∀ a, f'.hom a = f.hom a) :
    (brauerInvZOfIsSepClosure F Fsep).comp ((cohomologyMap f' 2).hom.toAddMonoidHom.comp
        (cohomologyULiftIntAddEquiv A 2).toAddMonoidHom) =
      (brauerInvOfIsSepClosure F Fsep).comp (cohomologyMap f 2).hom.toAddMonoidHom :=
  AddMonoidHom.ext fun z => brauerInvZOfIsSepClosure_cohomologyMap_uliftInt A f f' hf z

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (ψ : Gal(Fsep/F) →ₜ* G)
  (D : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep D] (ρ : Rep.res ψ.toMonoidHom D ⟶ galUnits.{0} F Fsep)
  (M : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep M] [Finite M]

abbrev resEvalPairing :
    Rep.res ψ.toMonoidHom M ⊗ Rep.res ψ.toMonoidHom (dualRep D M) ⟶ Rep.res ψ.toMonoidHom D :=
  (Rep.resFunctor ψ.toMonoidHom).map (evalPairing D M)

instance finite_res_toMonoidHom (M : Rep.{0} (ULift.{0} ℤ) G) [Finite M] :
    Finite (Rep.res ψ.toMonoidHom M) :=
  inferInstanceAs (Finite M)

instance isDiscreteRep_cartierDual_res : IsDiscreteRep (cartierDual F Fsep (Rep.res ψ.toMonoidHom M)) :=
  isDiscreteRep_cartierDual _

def dualToCartierDual :
    Rep.res ψ.toMonoidHom (dualRep D M) ⟶ cartierDual F Fsep (Rep.res ψ.toMonoidHom M) :=
  resDualPost ψ.toMonoidHom D M _ ρ

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsSepClosure F Fsep]
  [IsTopologicalGroup G] [IsDiscreteRep D] [IsDiscreteRep M] [Finite M] in
theorem dualToCartierDual_hom_apply (f : M →ₗ[ULift.{0} ℤ] D) (m : M) :
    ((dualToCartierDual ψ D ρ M).hom f : M →ₗ[ULift.{0} ℤ] galUnits.{0} F Fsep) m = ρ.hom (f m) :=
  rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsTopologicalGroup G]
  [IsDiscreteRep D] [IsDiscreteRep M] in
theorem bijective_dualToCartierDual {n : ℕ} [NeZero n] (hn : (n : F) ≠ 0)
    (hD : Nonempty (D ≃+ ZMod n)) (hρ : Function.Injective ρ.hom) (hM : ∀ m : M, n • m = 0) :
    Function.Bijective (dualToCartierDual ψ D ρ M).hom := by
  have hDv := nonempty_addEquiv_galRootsOfUnity (Ksep := Fsep) hn
  have : Finite D := finite_of_nonempty_addEquiv hD
  have : Finite (galRootsOfUnity.{0} F Fsep n) := finite_of_nonempty_addEquiv hDv
  have : Finite (dualRep D M) := finite_dualRep
  have : Finite (dualRep D (dualRep D M)) := finite_dualRep
  have : Finite (dualRep (galRootsOfUnity.{0} F Fsep n) (Rep.res ψ.toMonoidHom M)) := finite_dualRep
  set e := dualRepRootsOfUnityIso F Fsep (Rep.res ψ.toMonoidHom M) n hM
  have he : Function.Injective e.inv.hom := fun a b hab => by
    have h := congrArg e.hom.hom hab
    rwa [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, e.inv_hom_id] at h
  have : Finite (cartierDual F Fsep (Rep.res ψ.toMonoidHom M)) := Finite.of_injective _ he
  refine Function.Injective.bijective_of_nat_card_le ?_ ?_
  · intro f f' hff'
    exact LinearMap.ext fun m => hρ (LinearMap.congr_fun hff' m)
  · calc _ ≤ Nat.card (dualRep (galRootsOfUnity.{0} F Fsep n) (Rep.res ψ.toMonoidHom M)) :=
          Nat.card_le_card_of_injective _ he
      _ ≤ Nat.card M := card_dualRep_le hDv
      _ ≤ Nat.card (dualRep D (dualRep D M)) :=
          Nat.card_le_card_of_injective _ (bijective_toDualDual hD hM).1
      _ ≤ Nat.card (dualRep D M) := card_dualRep_le hD

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsSepClosure F Fsep]
  [IsTopologicalGroup G] [IsDiscreteRep D] [IsDiscreteRep M] [Finite M] in

theorem tensorHom_dualToCartierDual_cartierPairing :
    (𝟙 (Rep.res ψ.toMonoidHom M) ⊗ₘ dualToCartierDual ψ D ρ M) ≫
        cartierPairing F Fsep (Rep.res ψ.toMonoidHom M) =
      resEvalPairing ψ D M ≫ ρ := by
  refine Rep.Hom.ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => ?_))
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a f => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

omit [Finite M] in

theorem localDualityPairing_dualToCartierDual [Finite M] {r s : ℕ} (h : r + s = 2)
    (ξ : cohomology (Rep.res ψ.toMonoidHom M) r)
    (η : cohomology (Rep.res ψ.toMonoidHom (dualRep D M)) s) :
    localDualityPairing F Fsep (Rep.res ψ.toMonoidHom M) h ξ
        ((cohomologyMap (dualToCartierDual ψ D ρ M) s).hom η) =
      brauerInvOfIsSepClosure F Fsep ((cohomologyMap ρ 2).hom
        (cupPairing (resEvalPairing ψ D M) h ξ η)) := by
  rw [localDualityPairing_apply]
  refine congrArg (brauerInvOfIsSepClosure F Fsep) ?_
  have hc := cupPairing_cohomologyMap (cartierPairing F Fsep (Rep.res ψ.toMonoidHom M))
    (𝟙 _) (dualToCartierDual ψ D ρ M) h ξ η
  rw [cohomologyMap_id, ModuleCat.id_apply] at hc
  rw [hc, tensorHom_dualToCartierDual_cartierPairing, cohomologyMap_cupPairing]

theorem bijective_localInvPairing {n : ℕ} [NeZero n] (hn : (n : F) ≠ 0) (hD : Nonempty (D ≃+ ZMod n))
    (hρ : Function.Injective ρ.hom) (hM : ∀ m : M, n • m = 0)
    (inv : cohomology (Rep.res ψ.toMonoidHom D) 2 →+ QZ)
    (hinv : inv = (brauerInvOfIsSepClosure F Fsep).comp (cohomologyMap ρ 2).hom.toAddMonoidHom) {r s : ℕ}
    (h : r + s = 2)
    (β : cohomology (Rep.res ψ.toMonoidHom M) r →+
      cohomology (Rep.res ψ.toMonoidHom (dualRep D M)) s →+ QZ)
    (hβ : ∀ ξ η, β ξ η = inv (cupPairing (resEvalPairing ψ D M) h ξ η)) :
    Function.Bijective β := by
  have hM' : (Nat.card (Rep.res ψ.toMonoidHom M) : F) ≠ 0 := by
    refine fun h0 => hn ?_
    obtain ⟨c, hc⟩ := card_dvd_exponent_nsmul_rank' (Rep.res ψ.toMonoidHom M) hM
    have h1 : ((n ^ AddGroup.rank (Rep.res ψ.toMonoidHom M) : ℕ) : F) = 0 := by
      rw [hc, Nat.cast_mul, h0, zero_mul]
    rw [Nat.cast_pow] at h1
    exact pow_eq_zero_iff'.1 h1 |>.1
  refine bijective_of_bijective_precomp β (localDualityPairing F Fsep (Rep.res ψ.toMonoidHom M) h)
    (cohomologyAddEquivOfIso (Rep.isoOfBijective (dualToCartierDual ψ D ρ M)
      (bijective_dualToCartierDual ψ D ρ M hn hD hρ hM)) s) (fun ξ η => ?_)
    (bijective_localDualityPairing _ hM' h)
  rw [cohomologyAddEquivOfIso_apply, hβ, hinv, AddMonoidHom.comp_apply]
  exact (localDualityPairing_dualToCartierDual ψ D ρ M h ξ η).symm

end Abstract

section GS

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  (n : ℕ)

def gsRootsToLocalUnits (v : S) :
    Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n) ⟶
      galUnits.{0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) :=
  Rep.ofHom ⟨uliftIntLinearMap (A := Additive (rootsOfUnity n (maxUnramifiedOutside K.1 ℚ̄ S)))
      (B := Additive (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))ˣ)
      (MonoidHom.toAdditive
        ((Units.map ((ιs v).comp (maxUnramifiedOutside K.1 ℚ̄ S).val).toRingHom.toMonoidHom).comp
          (rootsOfUnity n (maxUnramifiedOutside K.1 ℚ̄ S)).subtype)),
    fun σ => LinearMap.ext fun (ζ : Additive (rootsOfUnity n (maxUnramifiedOutside K.1 ℚ̄ S))) =>
      congrArg Additive.ofMul
        (Units.ext (gsFinFamily_apply S ιs v σ
          (((Additive.toMul ζ : rootsOfUnity n _) : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :
            maxUnramifiedOutside K.1 ℚ̄ S)))⟩

theorem gsRootsToLocalUnits_hom_apply (v : S)
    (ζ : Additive (rootsOfUnity n (maxUnramifiedOutside K.1 ℚ̄ S))) :
    ((Additive.toMul ((gsRootsToLocalUnits S ιs n v).hom ζ) :
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))ˣ) :
      AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) =
      ιs v (((Additive.toMul ζ : rootsOfUnity n _) : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : ℚ̄) :=
  rfl

theorem gsRootsToLocalUnits_injective (v : S) :
    Function.Injective (gsRootsToLocalUnits S ιs n v).hom := by
  intro a b hab
  have h := congrArg (fun x => ((Additive.toMul x :
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))ˣ) :
    AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) hab
  change ιs v _ = ιs v _ at h
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  apply Subtype.ext
  exact (ιs v).toRingHom.injective h

theorem gsLocalInvRootsQZ_eq_comp (v : S) :
    gsLocalInvRootsQZ S ιs n v =
      (brauerInvOfIsSepClosure _ _).comp (cohomologyMap (gsRootsToLocalUnits S ιs n v) 2).hom.toAddMonoidHom :=
  (gsLocalInvRootsQZ_eq S ιs n v).trans
    (brauerInvZOfIsSepClosure_comp_cohomologyMap_uliftInt _ (gsRootsToLocalUnits S ιs n v)
      (rootsLocalMorZ S ιs n v) (fun _ => rfl))

theorem bijective_gsLocalPairing [NeZero n] (hD : Nonempty (gsRoots S n ≃+ ZMod n))
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) (v : S) {r s : ℕ} (h : r + s = 2) :
    Function.Bijective
      (ptLocalPairing (gsFinFamily S ιs) (gsRoots S n) M (gsLocalInvRootsQZ S ιs n) v h) :=
  bijective_localInvPairing (gsFinFamily S ιs v) (gsRoots S n) (gsRootsToLocalUnits S ιs n v) M
    (Nat.cast_ne_zero.2 (NeZero.ne n)) hD (gsRootsToLocalUnits_injective S ιs n v) hM
    (gsLocalInvRootsQZ S ιs n v) (gsLocalInvRootsQZ_eq_comp S ιs n v) h _
    (ptLocalPairing_apply _ _ _ _ v h)

end GS

end GroundTheory.ProfCoh
