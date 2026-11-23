import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalResKill
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.ResLocal
import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbolUnramified
import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbolNorm
import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbolReal
import GroundTheory.LocalFields.MainTheorem
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory IntermediateField GroundTheory.LocalField ValuativeRel
open GroundTheory.LocalField.Abstract GroundTheory.LocalField.Abstract.ProfiniteInteger

noncomputable section

section Structure

variable (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

theorem brauerInvZOfIsSepClosure_eq_brauerInvZ [v : ValuativeRel Ω] [t : TopologicalSpace Ω]
    [IsValuativeTopology Ω] [ValuativeExtension K Ω] :
    brauerInvZOfIsSepClosure K Ω = brauerInvZ K Ω := by
  have hv : algebraicValuativeRel K Ω = v :=
    valuativeRel_eq_of_isAlgebraic K (algebraicValuativeRel_valuativeExtension K Ω) inferInstance
  subst hv
  let : ValuativeRel Ω := algebraicValuativeRel K Ω
  have ht : algebraicTopology K Ω = t :=
    topologicalSpace_eq_of_isValuativeTopology (algebraicTopology_isValuativeTopology K Ω) inferInstance
  subst ht
  rfl

end Structure

section Res

variable (Kv Ω : Type) [Field Kv] [ValuativeRel Kv] [TopologicalSpace Kv] [IsNonarchimedeanLocalField Kv]
  [Field Ω] [Algebra Kv Ω] [IsSepClosure Kv Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [ValuativeExtension Kv Ω] (L : IntermediateField Kv Ω) [FiniteDimensional Kv L]

theorem brauerInvZOfIsSepClosure_unitsScalarsRes (y : cohomology (galUnitsZ Kv Ω) 2) :
    brauerInvZOfIsSepClosure L Ω ((unitsScalarsRes Kv Ω L 2).hom y) =
      Module.finrank Kv L • brauerInvZOfIsSepClosure Kv Ω y := by
  rw [brauerInvZOfIsSepClosure_eq_brauerInvZ L Ω, brauerInvZOfIsSepClosure_eq_brauerInvZ Kv Ω]
  obtain ⟨x, rfl⟩ := (cohomologyULiftIntAddEquiv (galUnits.{0} Kv Ω) 2).surjective y
  have e := cohomologyULiftIntAddEquiv_cohomologyMapAlong (galUnits.{0} Kv Ω)
    (AlgEquiv.restrictScalarsHom Kv) (continuous_restrictScalarsHom_of_tower Kv L Ω)
    (galUnitsResScalars Kv L Ω) (unitsScalarsMor Kv Ω L) (fun _ => rfl) 2 x
  have e' := congrArg (brauerInvZ L Ω) e
  rw [brauerInvZ_cohomologyULiftIntAddEquiv] at e'
  refine e'.symm.trans ?_
  rw [brauerInvZ_cohomologyULiftIntAddEquiv]
  exact brauerInv_brauerRes Kv L Ω x

end Res

section Injective

variable {k G H : Type} [CommRing k] [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H] {A : Rep k G} {B : Rep k H} [IsDiscreteRep A] [IsDiscreteRep B]

theorem cohomologyMapAlong_injective_of_leftInverse (φ : H →* G) (hφ : Continuous φ) (ψ : G →* H)
    (hψ : Continuous ψ) (hφψ : ∀ g, φ (ψ g) = g) (f : Rep.res φ A ⟶ B) (f' : Rep.res ψ B ⟶ A)
    (hff : ∀ a : A, f'.hom (f.hom a) = a) (n : ℕ) :
    Function.Injective (cohomologyMapAlong φ hφ f n).hom := by
  have h : cohomologyMapAlong φ hφ f n ≫ cohomologyMapAlong ψ hψ f' n = 𝟙 _ := by
    rw [← cohomologyMapAlong_comp]
    exact cohomologyMapAlong_eq_id _ _ (MonoidHom.ext hφψ) hff n
  intro x y hxy
  have e := congrArg (cohomologyMapAlong ψ hψ f' n).hom hxy
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, h] at e
  exact e

end Injective

section Quadratic

variable {F F' Ω Ω' : Type} [Field F] [Field F'] [Field Ω] [Field Ω'] [Algebra F Ω] [Algebra F' Ω']
  [FiniteDimensional F Ω] [IsGalois F Ω] [FiniteDimensional F' Ω'] [IsGalois F' Ω']

theorem quadraticInv_cohomologyMapAlong_of_injective (h2 : Module.finrank F Ω ≤ 2) (hN)
    (h2' : Module.finrank F' Ω' ≤ 2) (hN') {ρ : Gal(Ω/F) →* Gal(Ω'/F')} (hρc : Continuous ρ)
    (f : Rep.res ρ (galUnitsZ F' Ω') ⟶ galUnitsZ F Ω)
    (hinj : Function.Injective (cohomologyMapAlong ρ hρc f 2).hom) (x : cohomology (galUnitsZ F' Ω') 2) :
    quadraticInv F Ω h2 hN ((cohomologyMapAlong ρ hρc f 2).hom x) = quadraticInv F' Ω' h2' hN' x := by
  rw [quadraticInv_apply, quadraticInv_apply]
  by_cases hx : x = 0
  · rw [hx, map_zero, quadraticInvFun_zero, quadraticInvFun_zero]
  · rw [quadraticInvFun_of_ne_zero F Ω (fun h => hx (hinj (h.trans (map_zero _).symm))),
      quadraticInvFun_of_ne_zero F' Ω' hx]

end Quadratic

section Surjective

variable {F Ω : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field Ω] [Algebra F Ω] [IsSepClosure F Ω]

theorem exists_galCupClass_eq (x : cohomology (galUnitsZ F Ω) 2) :
    ∃ (χ : Additive Gal(Ω/F) →ₜ+ QZ) (a : Fˣ), galCupClass F Ω χ a = x := by
  let := algebraicValuativeRel F Ω
  let := algebraicTopology F Ω
  have := algebraicTopology_isValuativeTopology F Ω
  have := algebraicValuativeRel_valuativeExtension F Ω
  obtain ⟨r, hr⟩ := QZ.mk_surjective (brauerInvZ F Ω x)
  let n : ℕ+ := ⟨r.den, r.den_pos⟩
  let f₀ : ℤ →+ QZ := zmultiplesHom QZ (QZ.mk r)
  have hf₀ : f₀ ((n : ℕ) : ℤ) = 0 := by
    change ((r.den : ℕ) : ℤ) • QZ.mk r = 0
    rw [natCast_zsmul, ← QZ.mk_nsmul, nsmul_eq_mul, Rat.den_mul_eq_num, QZ.mk_eq_zero_iff]
    exact ⟨r.num, rfl⟩
  let χ₀ : ZMod n →+ QZ := ZMod.lift n ⟨f₀, hf₀⟩
  have hχ₀ : χ₀ 1 = QZ.mk r := by
    rw [show (1 : ZMod n) = ((1 : ℤ) : ZMod n) from Int.cast_one.symm, ZMod.lift_coe]
    change (1 : ℤ) • QZ.mk r = QZ.mk r
    rw [one_zsmul]
  let ψ : Additive Gal(Ω/F) →ₜ+ QZ :=
    { toFun := fun g => χ₀ (proj n (Multiplicative.toAdd (unramifiedDegree F Ω (Additive.toMul g))))
      map_zero' := by
        change χ₀ (proj n (Multiplicative.toAdd (unramifiedDegree F Ω 1))) = 0
        rw [map_one, toAdd_one, map_zero, map_zero]
      map_add' := fun g h => by
        change χ₀ (proj n (Multiplicative.toAdd (unramifiedDegree F Ω (Additive.toMul g * Additive.toMul h)))) = _
        rw [map_mul, toAdd_mul, map_add, map_add]
      continuous_toFun := continuous_of_discreteTopology.comp ((continuous_proj n).comp
        (continuous_toAdd.comp ((continuous_unramifiedDegree (K := F) (Ω := Ω)).comp continuous_toMul))) }
  obtain ⟨π, hπ⟩ : ∃ π : Fˣ, ord (π : F) = 1 := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
    have h0 : (ϖ : F) ≠ 0 := by exact_mod_cast hϖ.ne_zero
    exact ⟨Units.mk0 _ h0, by rw [Units.val_mk0]; exact ord_uniformizer hϖ⟩
  obtain ⟨σ, hσ⟩ := unramifiedDegree_surjective (K := F) (Ω := Ω) (Multiplicative.ofAdd 1)
  have hψ : ∀ g ∈ (unramifiedDegree F Ω).ker, ψ (Additive.ofMul g) = 0 := fun g hg => by
    change χ₀ (proj n (Multiplicative.toAdd (unramifiedDegree F Ω g))) = 0
    rw [MonoidHom.mem_ker.1 hg, toAdd_one, map_zero, map_zero]
  refine ⟨ψ, π, (brauerInvZ_bijective F Ω).1 ?_⟩
  rw [brauerInvZ_galCupClass_of_unramified ψ hψ hσ π, hπ, one_smul, ← hr]
  change χ₀ (proj n (Multiplicative.toAdd (unramifiedDegree F Ω σ))) = QZ.mk r
  rw [hσ, toAdd_ofAdd, map_one, hχ₀]

end Surjective

section Transport

variable {F F' Ω Ω' : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field F'] [ValuativeRel F'] [TopologicalSpace F'] [IsNonarchimedeanLocalField F']
  [Field Ω] [Algebra F Ω] [IsSepClosure F Ω] [Field Ω'] [Algebra F' Ω'] [IsSepClosure F' Ω']
  (e : F ≃+* F') (ε : Ω ≃+* Ω') (hε : ∀ x : F, ε (algebraMap F Ω x) = algebraMap F' Ω' (e x))
  (ρ : Gal(Ω/F) →* Gal(Ω'/F')) (hρc : Continuous ρ) (hρ : ∀ (σ : Gal(Ω/F)) (x : Ω), ρ σ (ε x) = ε (σ x))
  (f : Rep.res ρ (galUnitsZ F' Ω') ⟶ galUnitsZ F Ω)
  (hf : ∀ u : Ω'ˣ, ((Additive.toMul (f.hom (Additive.ofMul u)) : Ωˣ) : Ω) = ε.symm u)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [ValuativeRel F']
  [TopologicalSpace F'] [IsNonarchimedeanLocalField F'] in
include hε hf in

theorem cohomologyMapAlong_galCupClass_transport (χ : Additive Gal(Ω'/F') →ₜ+ QZ) (a : Fˣ) :
    (cohomologyMapAlong ρ hρc f 2).hom (galCupClass F' Ω' χ (Units.map e.toRingHom.toMonoidHom a)) =
      galCupClass F Ω (contCharComp χ ρ hρc) a := by
  refine cohomologyMapAlong_cupCharClassProf ρ hρc f χ _ _ ?_
  apply Additive.toMul.injective
  apply Units.ext
  change algebraMap F Ω a = ((Additive.toMul (f.hom (Additive.ofMul
    (Units.map (algebraMap F' Ω' : F' →* Ω') (Units.map e.toRingHom.toMonoidHom a)))) : Ωˣ) : Ω)
  rw [hf, Units.coe_map, Units.coe_map]
  change algebraMap F Ω a = ε.symm (algebraMap F' Ω' (e a))
  rw [← hε, RingEquiv.symm_apply_apply]

include hε hρ in

theorem brauerInvZOfIsSepClosure_galCupClass_transport (he : ∀ x y : F, e x ≤ᵥ e y ↔ x ≤ᵥ y)
    (χ : Additive Gal(Ω'/F') →ₜ+ QZ) (a : Fˣ) :
    brauerInvZOfIsSepClosure F Ω (galCupClass F Ω (contCharComp χ ρ hρc) a) =
      brauerInvZOfIsSepClosure F' Ω' (galCupClass F' Ω' χ (Units.map e.toRingHom.toMonoidHom a)) := by
  set g : Gal(Ω/F) := (localArtinMap F Ω a).liftNormal Ω
  have hg : ∀ (y : Ω) (hy : y ∈ maximalAbelianExtension F Ω), g y = (localArtinMap F Ω a ⟨y, hy⟩ : Ω) :=
    fun y hy => AlgEquiv.liftNormal_commutes (localArtinMap F Ω a) Ω ⟨y, hy⟩
  rw [brauerInvZOfIsSepClosure_galCupClass _ a g hg, contCharComp_apply]
  refine (brauerInvZOfIsSepClosure_galCupClass χ _ (ρ g) fun y' hy' => ?_).symm
  obtain ⟨y, rfl⟩ := ε.surjective y'
  have hy : y ∈ maximalAbelianExtension F Ω := (mem_maximalAbelianExtension_transport_iff e ε hε).1 hy'
  rw [hρ, hg y hy, localArtinMap_transport e he ε hε a hy]

include hε hρ hf in

theorem brauerInvZOfIsSepClosure_cohomologyMapAlong_transport (he : ∀ x y : F, e x ≤ᵥ e y ↔ x ≤ᵥ y)
    (x : cohomology (galUnitsZ F' Ω') 2) :
    brauerInvZOfIsSepClosure F Ω ((cohomologyMapAlong ρ hρc f 2).hom x) = brauerInvZOfIsSepClosure F' Ω' x := by
  obtain ⟨χ, a', rfl⟩ := exists_galCupClass_eq x
  obtain ⟨a, rfl⟩ : ∃ a : Fˣ, Units.map e.toRingHom.toMonoidHom a = a' :=
    ⟨Units.map e.symm.toRingHom.toMonoidHom a', by ext; simp⟩
  rw [cohomologyMapAlong_galCupClass_transport e ε hε ρ hρc f hf,
    brauerInvZOfIsSepClosure_galCupClass_transport e ε hε ρ hρc hρ he]

end Transport

end

end GroundTheory.ProfCoh
