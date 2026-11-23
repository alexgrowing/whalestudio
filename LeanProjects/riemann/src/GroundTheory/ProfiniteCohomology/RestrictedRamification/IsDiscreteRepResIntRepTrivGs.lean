import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseCupLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.IdeleGroup

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

noncomputable section

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) [Fintype S]
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  {n : ℕ} [NeZero n] (hodd : Odd n ∨ IsTotallyComplex K.1)

instance isDiscreteRep_res_intRepTriv_gs (v : S) :
    IsDiscreteRep (Rep.res (gsFinFamily S ιs v).toMonoidHom (intRepTriv (galUnramifiedOutside K.1 ℚ̄ S))) :=
  isDiscreteRep_res_toMonoidHom (gsFinFamily S ιs v) _

section General

variable (F E : Type) [Field F] [Field E] [Algebra F E] [IsGalois F E]
  {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  (ψ : Gal(E/F) →* Γ) (hψ : Continuous ψ) [IsDiscreteRep (Rep.res ψ (intRepTriv Γ))] {m : ℕ} [NeZero m]
  [IsDiscreteRep (uliftIntToIntRep (galUnits.{0} F E))]

theorem cohomologyMap_galUnitsToZ_cupPairing_δ_bockSeq (z : cocycles (zmodRep.{0} Γ m) 1)
    (χ' : Additive Gal(E/F) →ₜ+ QZ)
    (hχ' : ∀ σ : Gal(E/F), χ' (Additive.ofMul σ) = zmodToQZ m (zmodCocycleHom z (ψ σ))) (a : Fˣ) :
    (cohomologyMap (galUnitsToZ F E) 2).hom (cohomologyULiftIntAddEquiv _ 2
      (cupPairing (mulIntRight ψ (galUnits.{0} F E)) (show 0 + 2 = 2 from rfl)
        ((H0Iso (galUnits.{0} F E)).inv.hom (unitsToInvariants F E (Additive.ofMul a)))
        ((cohomologyMapAlong ψ hψ (𝟙 _) 2).hom
          ((δ (bockSeq_shortExact Γ m (NeZero.ne m)) 1 2 rfl).hom (cohomologyπ _ 1 z))))) =
      galCupClass F E χ' a := by
  obtain ⟨x₁, hx₁, hx₁v⟩ := exists_cocycle_δ_bockSeq (NeZero.ne m) z
  obtain ⟨z0, hz0, hz0c⟩ := exists_cocycle_H0Iso_inv (galUnits.{0} F E) (unitsToInvariants F E (Additive.ofMul a))
  obtain ⟨w, hw, hwv⟩ := exists_cocycle_cupCharClassProf (galUnitsZ F E) χ' (unitsInvariant F E a)
  rw [← hx₁, ← hz0, cohomologyMapAlong_cohomologyπ, cupPairing_cohomologyπ, cohomologyULiftIntAddEquiv_cohomologyπ',
    cohomologyMap_cohomologyπ]
  change _ = (cupCharClassProf (galUnitsZ F E) χ').hom (unitsInvariant F E a)
  rw [← hw]
  congr 1
  apply cocycles_ext
  funext s
  rw [cochainOf_cocycleι_cyclesMap, cochainOf_cocycleι_cocyclesULiftInt]
  beta_reduce
  rw [cochainOf_cocycleι_cyclesMap_cupCocycles, hz0c, cochainOf_cocycleι_cocyclesMapAlong, hwv]
  have hs : (⇑ψ ∘ fun j : Fin 2 => s ⟨0 + j, by omega⟩) = ![ψ (s 0), ψ (s 1)] := by
    funext j
    fin_cases j <;> rfl
  have hb := hx₁v (ψ (s 0)) (ψ (s 1))
  have hχf : ∀ σ : Gal(E/F), charAdd χ' (Additive.ofMul σ) =
      QZ.toAddCircle (zmodToQZ m ((fun σ => zmodCocycleHom z (ψ σ)) σ)) := fun σ => by
    rw [charAdd_apply, hχ']
  rw [charCocycle_eq_bockInt (fun σ => zmodCocycleHom z (ψ σ)) (charAdd χ') hχf]
  change (mulIntRight ψ (galUnits.{0} F E)).hom
      ((unitsToInvariants F E (Additive.ofMul a) : galUnits.{0} F E) ⊗ₜ[ULift.{0} ℤ]
        (cochainOf (intRepTriv Γ) (cocycleι (intRepTriv Γ) 2 x₁) (⇑ψ ∘ fun j : Fin 2 => s ⟨0 + j, by omega⟩))) = _
  rw [hs]
  have hx : cochainOf (intRepTriv Γ) (cocycleι (intRepTriv Γ) 2 x₁) ![ψ (s 0), ψ (s 1)] =
      ULift.up (bockInt (zmodCocycleHom z) (ψ (s 0)) (ψ (s 1))) := ULift.ext _ _ hb
  rw [hx]
  exact mulIntRight_tmul ψ (galUnits.{0} F E) _ _

end General

theorem localInvU_cupPairing_δ_bockSeq (v : S) (a : ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)ˣ)
    (z : cocycles (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1)
    (χ : ContinuousMonoidHom (galUnramifiedOutside K.1 ℚ̄ S) (Multiplicative (ZMod n)))
    (hχ : ∀ g, Multiplicative.toAdd (χ g) = zmodCocycleHom z g) :
    localInvU (v : HeightOneSpectrum (𝓞 K.1))
      (cupPairing (mulIntRight (gsFinFamily S ιs v).toMonoidHom
          (galUnits.{0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
            (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))))
        (show 0 + 2 = 2 from rfl)
        ((H0Iso (galUnits.{0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
            (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))).inv.hom
          (unitsToInvariants _ _ (Additive.ofMul a)))
        ((cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _) (𝟙 _) 2).hom
          ((δ (bockSeq_shortExact (galUnramifiedOutside K.1 ℚ̄ S) n (NeZero.ne n)) 1 2 rfl).hom
            (cohomologyπ _ 1 z)))) =
      zmodToQZ n (Multiplicative.toAdd (charEquiv ℚ̄ (Set.toFinite S) hodd χ
        (SIdeleClassGroup.mk S (finiteEmbedding (v : HeightOneSpectrum (𝓞 K.1)) a)))) := by
  refine (DFunLike.congr_fun (localInvU_eq (v : HeightOneSpectrum (𝓞 K.1))) _).trans ?_
  refine (AddMonoidHom.comp_apply _ _ _).trans ?_
  refine (congrArg (brauerInvZOfIsSepClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
    (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))
    ((AddMonoidHom.comp_apply _ _ _).trans (cohomologyMap_galUnitsToZ_cupPairing_δ_bockSeq _ _
      (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _) z
      (contCharComp (charQZ χ) (decompHomS ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) S (ιs v))
        (continuous_decompHomS (Kv := (v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) S (ιs v)))
      (fun σ => (charQZ_apply χ _).trans (congrArg (zmodToQZ n) (hχ _))) a))).trans ?_
  exact brauerInvZ_galCupClass_decompHomS (Set.toFinite S) hodd χ (v : HeightOneSpectrum (𝓞 K.1)) (ιs v) a

end

end GroundTheory.ProfCoh
