import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseLocal
import GroundTheory.ProfiniteCohomology.RestrictedRamification.MkFiniteEmbeddingGlobalUniformizer
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseCupKummer
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseKummer
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseCupGlob
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory IsDedekindDomain NumberField GroundTheory.Global GroundTheory.GroupCoh

universe u

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

noncomputable section

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) (n : ℕ)
  [NeZero n]

omit [NeZero n] in

theorem localInvU_eq_brauerInvOfIsSepClosure (v : HeightOneSpectrum (𝓞 K.1))
    (x : cohomology (galUnits.{0} (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))) 2) :
    localInvU v x = brauerInvOfIsSepClosure (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) x :=
  ((DFunLike.congr_fun (localInvU_eq v) x).trans ((AddMonoidHom.comp_apply _ _ _).trans
    (congrArg _ (AddMonoidHom.comp_apply _ _ _)))).trans
    ((brauerInvZOfIsSepClosure_cohomologyMap_uliftInt_base _ (𝟙 _) (galUnitsToZ _ _) (fun _ => rfl) x).trans
      (congrArg _ (congrArg (fun f => ModuleCat.Hom.hom f x) (cohomologyMap_id 2))))

omit [NeZero n] in

theorem gsRootsOmegaMor_eq_gsRootsLocalMor (v : S) : gsRootsOmegaMor S ιs n v = gsRootsLocalMor S ιs n v := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun ζ => ?_))
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  exact (restrictRootsOfUnity_coe_apply _ _).trans (gsRootsLocalMor_hom_apply S ιs n v ζ).symm

theorem zmodToQZ_gsLocalInvRoots_eq_localInvU (v : S)
    (z : cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 2) :
    zmodToQZ n (gsLocalInvRoots S ιs n v z) =
      localInvU (v : HeightOneSpectrum (𝓞 K.1))
        ((cohomologyMap (gsRootsOmegaMor S ιs n v ≫ rootsOfUnityToUnits _ _ n) 2).hom z) := by
  exact (zmodToQZ_gsLocalInvRoots S ιs n v z).trans ((gsLocalInvRootsQZ_eq_brauerInv_base S ιs n v z).trans
    ((congrArg (fun f => brauerInvOfIsSepClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
        ((cohomologyMap (f ≫ rootsOfUnityToUnits _ _ n) 2).hom z))
      (gsRootsOmegaMor_eq_gsRootsLocalMor S ιs n v).symm).trans (localInvU_eq_brauerInvOfIsSepClosure _ _).symm))

theorem compactCup_congr {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)] [∀ v, IsTopologicalGroup (H v)]
    (φ : ∀ v, H v →ₜ* G) {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
    {Aᵥ Cᵥ : ∀ v, Rep.{u} k (H v)} [∀ v, IsDiscreteRep (Aᵥ v)] [∀ v, IsDiscreteRep (Cᵥ v)]
    {a : ∀ v, Rep.res (φ v).toMonoidHom A ⟶ Aᵥ v} {c : ∀ v, Rep.res (φ v).toMonoidHom C ⟶ Cᵥ v}
    {μ₁ μ₂ : A ⊗ B ⟶ C} {μ₁ᵥ μ₂ᵥ : ∀ v, Aᵥ v ⊗ Rep.res (φ v).toMonoidHom B ⟶ Cᵥ v}
    (h₁ : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map μ₁ ≫ c v = resTensorHom (φ v).toMonoidHom (a v) (𝟙 _) ≫ μ₁ᵥ v)
    (h₂ : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map μ₂ ≫ c v = resTensorHom (φ v).toMonoidHom (a v) (𝟙 _) ≫ μ₂ᵥ v)
    (e : μ₁ = μ₂) (eᵥ : ∀ v, μ₁ᵥ v = μ₂ᵥ v) {r s m : ℕ} (h : r + s = m) :
    compactCup φ μ₁ μ₁ᵥ h₁ h = compactCup φ μ₂ μ₂ᵥ h₂ h := by
  subst e
  obtain rfl : μ₁ᵥ = μ₂ᵥ := funext eᵥ
  rfl

theorem compactCup_congr_apply {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)] [∀ v, IsTopologicalGroup (H v)]
    (φ : ∀ v, H v →ₜ* G) {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
    {Aᵥ Cᵥ : ∀ v, Rep.{u} k (H v)} [∀ v, IsDiscreteRep (Aᵥ v)] [∀ v, IsDiscreteRep (Cᵥ v)]
    {a : ∀ v, Rep.res (φ v).toMonoidHom A ⟶ Aᵥ v} {c : ∀ v, Rep.res (φ v).toMonoidHom C ⟶ Cᵥ v}
    {μ₁ μ₂ : A ⊗ B ⟶ C} {μ₁ᵥ μ₂ᵥ : ∀ v, Aᵥ v ⊗ Rep.res (φ v).toMonoidHom B ⟶ Cᵥ v}
    (h₁ : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map μ₁ ≫ c v = resTensorHom (φ v).toMonoidHom (a v) (𝟙 _) ≫ μ₁ᵥ v)
    (h₂ : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map μ₂ ≫ c v = resTensorHom (φ v).toMonoidHom (a v) (𝟙 _) ≫ μ₂ᵥ v)
    (e : μ₁ = μ₂) (eᵥ : ∀ v, μ₁ᵥ v = μ₂ᵥ v) {r s m : ℕ} (h : r + s = m) (y : compactCohomology φ A Aᵥ a r)
    (x : cohomology B s) :
    compactCup φ μ₁ μ₁ᵥ h₁ h y x = compactCup φ μ₂ μ₂ᵥ h₂ h y x := by
  subst e
  obtain rfl : μ₁ᵥ = μ₂ᵥ := funext eᵥ
  rfl

section ActNatural

variable {H : Type} [Group H]

omit [NeZero n] in

theorem zmodActPairing_comp (D D' Z' : Rep.{0} (ULift.{0} ℤ) H) (hD : ∀ d : D, n • d = 0)
    (hD' : ∀ d : D', n • d = 0) (e : Z' →+ ZMod n) (hZ : ∀ (g : H) (z : Z'), Z'.ρ g z = z) (f : D ⟶ D') :
    zmodActPairing n D Z' hD e hZ ≫ f = (f ⊗ₘ 𝟙 Z') ≫ zmodActPairing n D' Z' hD' e hZ := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (TensorProduct.ext' fun (d : D) (z : Z') => ?_))
  change f.hom ((zmodActPairing n D Z' hD e hZ).hom (d ⊗ₜ[ULift.{0} ℤ] z)) =
    (zmodActPairing n D' Z' hD' e hZ).hom (f.hom d ⊗ₜ[ULift.{0} ℤ] z)
  rw [zmodActPairing_tmul, zmodActPairing_tmul, map_zsmul]

end ActNatural

omit [NeZero n] in

theorem zmodMulPairingRight_gsRoots_eq :
    zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n) =
      zmodActPairing n (gsRoots S n) (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) (nsmul_gsRoots S n)
        (AddEquiv.ulift : ULift.{0} (ZMod n) ≃+ ZMod n).toAddMonoidHom (fun _ _ => rfl) := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (TensorProduct.ext'
    fun (ζ : gsRoots S n) (a : zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) => ?_))
  change (zmodMulPairing n (gsRoots S n) (nsmul_gsRoots S n)).hom (a ⊗ₜ[ULift.{0} ℤ] ζ) =
    (zmodActPairing n (gsRoots S n) (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) (nsmul_gsRoots S n)
      (AddEquiv.ulift : ULift.{0} (ZMod n) ≃+ ZMod n).toAddMonoidHom (fun _ _ => rfl)).hom (ζ ⊗ₜ[ULift.{0} ℤ] a)
  exact (zmodMulPairing_tmul n _ _ a.down ζ).trans (zmodActPairing_tmul n (gsRoots S n)
    (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) (nsmul_gsRoots S n)
    (AddEquiv.ulift : ULift.{0} (ZMod n) ≃+ ZMod n).toAddMonoidHom (fun _ _ => rfl) ζ a).symm

section ResPairing

variable {k G H : Type u} [CommRing k] [Group G] [Group H] (ψ : H →* G) {A B C : Rep.{u} k G} {C' : Rep.{u} k H}

theorem resFunctor_map_comp_id_comp (μ : A ⊗ B ⟶ C) (g : Rep.res ψ C ⟶ C') :
    (Rep.resFunctor ψ).map (μ ≫ 𝟙 C) ≫ g =
      resTensorHom ψ (𝟙 (Rep.res ψ A)) (𝟙 (Rep.res ψ B)) ≫ ((Rep.resFunctor ψ).map μ ≫ g) :=
  (congrArg (· ≫ g) ((congrArg (Rep.resFunctor ψ).map (Category.comp_id μ)).trans
    ((Category.comp_id _).symm.trans (resFunctor_map_comp_id ψ μ)))).trans (Category.assoc _ _ _)

theorem resFunctor_map_id_tensor_comp (μ : A ⊗ B ⟶ C) (g : Rep.res ψ C ⟶ C')
    (ν : Rep.res ψ A ⊗ Rep.res ψ B ⟶ C') (e : (Rep.resFunctor ψ).map μ ≫ g = ν) :
    (Rep.resFunctor ψ).map ((𝟙 A ⊗ₘ 𝟙 B) ≫ μ) ≫ g = resTensorHom ψ (𝟙 (Rep.res ψ A)) (𝟙 (Rep.res ψ B)) ≫ ν :=
  (congrArg (fun f => (Rep.resFunctor ψ).map f ≫ g)
    (((congrArg (· ≫ μ) (MonoidalCategory.id_tensorHom_id A B)).trans (Category.id_comp μ)).trans
      (Category.comp_id μ).symm)).trans
    ((resFunctor_map_comp_id_comp ψ μ g).trans (congrArg (resTensorHom ψ (𝟙 _) (𝟙 _) ≫ ·) e))

end ResPairing

abbrev gsZmodPairing :
    gsRoots S n ⊗ zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n ⟶ gsRoots S n :=
  zmodActPairing n (gsRoots S n) (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) (nsmul_gsRoots S n)
    (AddEquiv.ulift : ULift.{0} (ZMod n) ≃+ ZMod n).toAddMonoidHom (fun _ _ => rfl)

abbrev gsZmodPairingᵥ (v : S) :
    galRootsOfUnity.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n ⊗
      Rep.res (gsFinFamily S ιs v).toMonoidHom (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) ⟶
    galRootsOfUnity.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n :=
  zmodActPairing n _ _ (nsmul_galRootsOfUnity_eq_zero' n) (AddEquiv.ulift : ULift.{0} (ZMod n) ≃+ ZMod n).toAddMonoidHom
    (fun _ _ => rfl)

omit [NeZero n] in
theorem resFunctor_map_gsZmodPairing (v : S) :
    (Rep.resFunctor (gsFinFamily S ιs v).toMonoidHom).map (gsZmodPairing S n) =
      zmodActPairing n (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n))
        (Rep.res (gsFinFamily S ιs v).toMonoidHom (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n)) (nsmul_gsRoots S n)
        (AddEquiv.ulift : ULift.{0} (ZMod n) ≃+ ZMod n).toAddMonoidHom (fun _ _ => rfl) :=
  Rep.hom_ext (Representation.IntertwiningMap.ext (TensorProduct.ext' fun _ _ => rfl))

omit [NeZero n] in
theorem gsZmodPairing_hμ (v : S) :
    (Rep.resFunctor (gsFinFamily S ιs v).toMonoidHom).map (gsZmodPairing S n) ≫ gsRootsOmegaMor S ιs n v =
      resTensorHom (gsFinFamily S ιs v).toMonoidHom (gsRootsOmegaMor S ιs n v) (𝟙 _) ≫ gsZmodPairingᵥ S ιs n v :=
  (congrArg (· ≫ gsRootsOmegaMor S ιs n v) (resFunctor_map_gsZmodPairing S ιs n v)).trans
    (zmodActPairing_comp n (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n))
      (galRootsOfUnity.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n)
      (Rep.res (gsFinFamily S ιs v).toMonoidHom (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n))
      (nsmul_gsRoots S n) (nsmul_galRootsOfUnity_eq_zero' n)
      (AddEquiv.ulift : ULift.{0} (ZMod n) ≃+ ZMod n).toAddMonoidHom (fun _ _ => rfl) (gsRootsOmegaMor S ιs n v))

omit [NeZero n] in

theorem gsRootsComparison_compactCupRes (y : compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 2)
    (x : cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1) :
    (gsRootsComparison S ιs n 3).hom (compactCupRes (gsFinFamily S ιs)
        (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n)) (show 2 + 1 = 3 from rfl) y x) =
      compactCup (gsFinFamily S ιs) (gsZmodPairing S n) (gsZmodPairingᵥ S ιs n) (gsZmodPairing_hμ S ιs n)
        (show 2 + 1 = 3 from rfl) ((gsRootsComparison S ιs n 2).hom y) x := by
  have hg : ∀ v, 𝟙 (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) ≫ gsRootsOmegaMor S ιs n v =
      (Rep.resFunctor (gsFinFamily S ιs v).toMonoidHom).map (𝟙 (gsRoots S n)) ≫ gsRootsOmegaMor S ιs n v :=
    fun _ => Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl))
  have e1 := compactCohomologyMap_compactCup (gsFinFamily S ιs) (A := gsRoots S n)
    (B := zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) (C := gsRoots S n) (C' := gsRoots S n)
    (Aᵥ := fun v => Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n))
    (Cᵥ := fun v => Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) (C'ᵥ := fun v => galRootsOfUnity.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n)
    (a := fun _ => 𝟙 _) (c := fun _ => 𝟙 _) (c' := gsRootsOmegaMor S ιs n)
    (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n))
    (fun v => (Rep.resFunctor (gsFinFamily S ιs v).toMonoidHom).map
      (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n)))
    (fun v => resFunctor_map_comp_id _ _) (𝟙 (gsRoots S n)) (gsRootsOmegaMor S ιs n) hg
    (fun v => resFunctor_map_comp_id_comp _ _ _) (show 2 + 1 = 3 from rfl) y x
  have e2 := compactCup_compactCohomologyMap (gsFinFamily S ιs) (A := gsRoots S n) (A' := gsRoots S n)
    (B := zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) (C := gsRoots S n)
    (Aᵥ := fun v => Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) (A'ᵥ := fun v => galRootsOfUnity.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n)
    (Cᵥ := fun v => galRootsOfUnity.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n) (a := fun _ => 𝟙 _) (a' := gsRootsOmegaMor S ιs n) (c := gsRootsOmegaMor S ιs n)
    (𝟙 (gsRoots S n)) (gsRootsOmegaMor S ιs n) hg
    (gsZmodPairing S n) (gsZmodPairingᵥ S ιs n) (gsZmodPairing_hμ S ιs n)
    (fun v => resFunctor_map_id_tensor_comp _ _ _ _ (gsZmodPairing_hμ S ιs n v)) (show 2 + 1 = 3 from rfl) y x
  have eμ : zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n) ≫ 𝟙 (gsRoots S n) =
      (𝟙 (gsRoots S n) ⊗ₘ 𝟙 (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n)) ≫ gsZmodPairing S n :=
    ((Category.comp_id _).trans (zmodMulPairingRight_gsRoots_eq S n)).trans
      ((congrArg (· ≫ gsZmodPairing S n) (MonoidalCategory.id_tensorHom_id _ _)).trans (Category.id_comp _)).symm
  have eμᵥ : ∀ v, (Rep.resFunctor (gsFinFamily S ιs v).toMonoidHom).map
      (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n)) ≫ gsRootsOmegaMor S ιs n v =
      (gsRootsOmegaMor S ιs n v ⊗ₘ 𝟙 _) ≫ gsZmodPairingᵥ S ιs n v := fun v =>
    (congrArg (fun f => (Rep.resFunctor (gsFinFamily S ιs v).toMonoidHom).map f ≫ gsRootsOmegaMor S ιs n v)
      (zmodMulPairingRight_gsRoots_eq S n)).trans (gsZmodPairing_hμ S ιs n v)
  refine e1.trans (Eq.trans ?_ e2.symm)
  exact compactCup_congr_apply (gsFinFamily S ιs) _ _ eμ eμᵥ (show 2 + 1 = 3 from rfl) y x

end

end GroundTheory.ProfCoh
