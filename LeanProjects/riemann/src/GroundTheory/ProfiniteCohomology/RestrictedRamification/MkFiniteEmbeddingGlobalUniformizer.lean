import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsDiscreteRepResIntRepTrivGs
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerOrd
import GroundTheory.ProfiniteCohomology.RestrictedRamification.SInvariantToInvariantsEqZeroIff
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.IdeleGroup

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

noncomputable section

section Ord

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) {v : HeightOneSpectrum (𝓞 K.1)}
  (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1)) (hv : v ∉ S)

theorem ordEmb_eq_ordAbove (x : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) (hx : IsSInvariant S x) :
    ordEmb S ι hv (Additive.ofMul x) = ordAbove S v x := by
  symm
  apply ordAbove_eq_of_isOrdAbove S hv hx
  have hZ : ((maxUnitsToUnits S x : ℚ̄ˣ) : ℚ̄) ∈ maxUnramifiedOutside K.1 ℚ̄ S := (x : maxUnramifiedOutside K.1 ℚ̄ S).2
  have hF := levelOf_subset_max S hZ
  have e1 := valuation_placeOfEmbedding_eq S ι hv (levelOf K ((maxUnitsToUnits S x : ℚ̄ˣ) : ℚ̄)) hF
    (maxUnitsToUnits S x) (mem_levelOf _)
  let E' : IntermediateField K.1 ℚ̄ :=
    IntermediateField.extendScalars (show K.1 ≤ (levelOf K ((maxUnitsToUnits S x : ℚ̄ˣ) : ℚ̄)).1 from
      (fact_le_levelOf ((maxUnitsToUnits S x : ℚ̄ˣ) : ℚ̄)).out)
  have hfd : FiniteDimensional K.1 E' := by
    have : FiniteDimensional ℚ E' := (levelOf K ((maxUnitsToUnits S x : ℚ̄ˣ) : ℚ̄)).2
    exact Module.Finite.of_restrictScalars_finite ℚ K.1 E'
  refine ⟨E', hfd, fun y hy => hF y hy, mem_levelOf _, ?_⟩
  refine ⟨(placeOfEmbedding ι (levelOf K ((maxUnitsToUnits S x : ℚ̄ˣ) : ℚ̄))).1, ?_, ?_⟩
  · exact (liesOver_iff_eq_underPlace.1 (placeOfEmbedding ι (levelOf K ((maxUnitsToUnits S x : ℚ̄ˣ) : ℚ̄))).2).symm
  · exact e1

end Ord

section Unif

variable {K : FiniteSubfield} (v : HeightOneSpectrum (𝓞 K.1))

def globalUniformizer : K.1ˣ :=
  Units.mk0 (v.valuation_exists_uniformizer K.1).choose (by
    intro h
    have h' := (v.valuation_exists_uniformizer K.1).choose_spec
    rw [h, map_zero] at h'
    exact WithZero.exp_ne_zero h'.symm)

theorem ordAt_globalUniformizer : ordAt v (globalUniformizer v) = 1 := by
  have h := valuation_eq_exp_neg_ordAt v (globalUniformizer v)
  rw [show ((globalUniformizer v : K.1ˣ) : K.1) = (v.valuation_exists_uniformizer K.1).choose from rfl,
    (v.valuation_exists_uniformizer K.1).choose_spec] at h
  have := WithZero.exp_injective h
  omega

theorem ordAt_zpow' (x : K.1ˣ) (m : ℤ) : ordAt v (x ^ m) = m * ordAt v x := by
  simp only [ordAt, map_zpow, toAdd_zpow, smul_eq_mul]
  ring

theorem map_globalUniformizer :
    Units.map (algebraMap K.1 (v.adicCompletion K.1) : K.1 →* v.adicCompletion K.1) (globalUniformizer v) =
      localUniformizer v :=
  Units.ext rfl

variable {S : Set (HeightOneSpectrum (𝓞 K.1))} [Finite S]

theorem mk_finiteEmbedding_globalUniformizer (hv : v ∉ S) (m : ℤ) :
    SIdeleClassGroup.mk S (finiteEmbedding v (Units.map (algebraMap K.1 (v.adicCompletion K.1) : K.1 →* _)
      (globalUniformizer v ^ m))) = sPresentation S (1, Multiplicative.ofAdd (Finsupp.single ⟨v, hv⟩ m)) := by
  rw [sPresentation_apply, map_one, one_mul, toAdd_ofAdd, divisorIdele_single, map_zpow, map_globalUniformizer,
    map_zpow]

end Unif

section LocalClass

section General

variable (F E : Type) [Field F] [Field E] [Algebra F E] [IsGalois F E]
  {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  (ψ : Gal(E/F) →* Γ) (hψ : Continuous ψ) {m : ℕ} [NeZero m]
  {A : Rep.{0} (ULift.{0} ℤ) Γ} [IsDiscreteRep A] [IsDiscreteRep (uliftIntToIntRep A)]
  (f : Rep.res ψ (uliftIntToIntRep A) ⟶ galUnitsZ F E)

theorem cohomologyMapAlong_cohomologyπ_bock (z : cocycles (zmodRep.{0} Γ m) 1)
    (χ' : Additive Gal(E/F) →ₜ+ QZ)
    (hχ' : ∀ σ : Gal(E/F), χ' (Additive.ofMul σ) = zmodToQZ m (zmodCocycleHom z (ψ σ))) (b : Fˣ) (a : A)
    (ha : f.hom a = (unitsInvariant F E b : Additive Eˣ))
    (w : cocycles A 2) (hw : ∀ g h, cochainOf _ (cocycleι _ 2 w) ![g, h] = bockInt (zmodCocycleHom z) g h • a) :
    (cohomologyMapAlong ψ hψ f 2).hom (cohomologyULiftIntAddEquiv _ 2 (cohomologyπ _ 2 w)) =
      galCupClass F E χ' b := by
  obtain ⟨w', hw', hw'v⟩ := exists_cocycle_cupCharClassProf (galUnitsZ F E) χ' (unitsInvariant F E b)
  rw [cohomologyULiftIntAddEquiv_cohomologyπ', cohomologyMapAlong_cohomologyπ]
  change _ = (cupCharClassProf (galUnitsZ F E) χ').hom (unitsInvariant F E b)
  rw [← hw']
  congr 1
  apply cocycles_ext
  funext s
  rw [cochainOf_cocycleι_cocyclesMapAlong, cochainOf_cocycleι_cocyclesULiftInt]
  beta_reduce
  rw [hw'v]
  have hs : (⇑ψ ∘ s) = ![ψ (s 0), ψ (s 1)] := by
    funext j
    fin_cases j <;> rfl
  have hχf : ∀ σ, charAdd χ' (Additive.ofMul σ) = QZ.toAddCircle (zmodToQZ m ((fun σ => zmodCocycleHom z (ψ σ)) σ)) :=
    fun σ => by rw [charAdd_apply, hχ']
  rw [hs, hw, charCocycle_eq_bockInt _ _ hχf]
  change f.hom (bockInt (zmodCocycleHom z) (ψ (s 0)) (ψ (s 1)) • a) = _
  rw [map_zsmul, ha]
  rfl

end General

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) {v : HeightOneSpectrum (𝓞 K.1)}
  (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1)) {n : ℕ} [NeZero n]

theorem gsLocalRes_cohomologyπ_bock (z : cocycles (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1)
    (χ : ContinuousMonoidHom (galUnramifiedOutside K.1 ℚ̄ S) (Multiplicative (ZMod n)))
    (hχ : ∀ g, Multiplicative.toAdd (χ g) = zmodCocycleHom z g) (b : K.1ˣ)
    (w : cocycles (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2)
    (hw : ∀ g h, cochainOf _ (cocycleι _ 2 w) ![g, h] = bockInt (zmodCocycleHom z) g h •
      (Additive.ofMul (Units.map (algebraMap K.1 (maxUnramifiedOutside K.1 ℚ̄ S) : K.1 →* _) b))) :
    (gsLocalRes S ι 2).hom (cohomologyULiftIntAddEquiv _ 2 (cohomologyπ _ 2 w)) =
      galCupClass (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))
        (contCharComp (charQZ χ) (decompHomS (v.adicCompletion K.1) S ι)
          (continuous_decompHomS (Kv := v.adicCompletion K.1) S ι))
        (Units.map (algebraMap K.1 (v.adicCompletion K.1) : K.1 →* _) b) :=
  cohomologyMapAlong_cohomologyπ_bock _ _ (decompHomS (v.adicCompletion K.1) S ι)
    (continuous_decompHomS (Kv := v.adicCompletion K.1) S ι) (embUnitsMorZ S ι) z _
    (fun σ => (charQZ_apply χ _).trans (congrArg (zmodToQZ n) (hχ _))) _ _
    (by
      apply Additive.toMul.injective
      apply Units.ext
      change ι (algebraMap K.1 ℚ̄ (b : K.1)) = algebraMap (v.adicCompletion K.1)
        (AlgebraicClosure (v.adicCompletion K.1)) (algebraMap K.1 (v.adicCompletion K.1) (b : K.1))
      rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]) w hw

end LocalClass

section Outside

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) [Fintype S] {v : HeightOneSpectrum (𝓞 K.1)}
  (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1)) (hv : v ∉ S) {n : ℕ} [NeZero n]
  (hodd : Odd n ∨ IsTotallyComplex K.1)

set_option maxHeartbeats 2000000 in

theorem placeInv_gsLocalRes_of_bock (t : sInvariantSubgroup ℚ̄ S)
    (z : cocycles (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1)
    (χ : ContinuousMonoidHom (galUnramifiedOutside K.1 ℚ̄ S) (Multiplicative (ZMod n)))
    (hχ : ∀ g, Multiplicative.toAdd (χ g) = zmodCocycleHom z g)
    (W : cocycles (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2)
    (hW : ∀ g h, (Additive.toMul (cochainOf _ (cocycleι _ 2 W) ![g, h]) : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) *
      ((t : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) ^ bockInt (zmodCocycleHom z) g h)⁻¹ ∈ sUnitsMax K.1 ℚ̄ S) :
    placeInv (K := K) (.inr v) ((gsLocalRes S ι 2).hom (cohomologyULiftIntAddEquiv _ 2 (cohomologyπ _ 2 W))) =
      zmodToQZ n (Multiplicative.toAdd (charEquiv ℚ̄ (Set.toFinite S) hodd χ
        (sPresentation S (1, Multiplicative.ofAdd (Finsupp.single ⟨v, hv⟩
          (ordAbove S v (t : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ))))))) := by
  obtain ⟨wb, hwb, hwbv⟩ := exists_cocycle_cupPairing_δ_bockSeq (NeZero.ne n)
    (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) z
    (unitsToInvariants K.1 (maxUnramifiedOutside K.1 ℚ̄ S) (Additive.ofMul (globalUniformizer v ^ ordAbove S v (t : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ))))
  have hWv : ∀ g h, ordEmb S ι hv (cochainOf _ (cocycleι _ 2 W) ![g, h]) = bockInt (zmodCocycleHom z) g h * ordAbove S v (t : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) := by
    intro g h
    have hu := hW g h
    have e : cochainOf _ (cocycleι _ 2 W) ![g, h] =
        Additive.ofMul ((Additive.toMul (cochainOf _ (cocycleι _ 2 W) ![g, h]) : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) *
          ((t : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) ^ bockInt (zmodCocycleHom z) g h)⁻¹) +
        bockInt (zmodCocycleHom z) g h • Additive.ofMul (t : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) := by
      rw [← ofMul_zpow, ← ofMul_mul, inv_mul_cancel_right, ofMul_toMul]
    rw [e, map_add, map_zsmul, ordEmb_eq_zero_of_mem S ι hv hu, zero_add, ordEmb_eq_ordAbove S ι hv _ t.2,
      smul_eq_mul]
  have hbv : ordEmb S ι hv (Additive.ofMul (Units.map (algebraMap K.1 (maxUnramifiedOutside K.1 ℚ̄ S)).toMonoidHom
      (globalUniformizer v ^ ordAbove S v (t : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ)))) =
        ordAbove S v (t : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) := by
    rw [ordEmb_algebraMap, ordAt_zpow', ordAt_globalUniformizer, mul_one]
  have hval : (cohomologyMapAlong (decompHomS (v.adicCompletion K.1) S ι)
      (continuous_decompHomS (Kv := v.adicCompletion K.1) S ι) (ordEmbMor S ι hv) 2).hom
        (cohomologyπ _ 2 W - cohomologyπ _ 2 wb) = 0 := by
    rw [map_sub, sub_eq_zero, cohomologyMapAlong_cohomologyπ, cohomologyMapAlong_cohomologyπ]
    congr 1
    apply cocycles_ext
    funext s
    rw [cochainOf_cocycleι_cocyclesMapAlong, cochainOf_cocycleι_cocyclesMapAlong]
    beta_reduce
    have hu : ∀ u : Fin 2 → galUnramifiedOutside K.1 ℚ̄ S, u = ![u 0, u 1] := fun u => by
      funext j
      fin_cases j <;> rfl
    have hW' : ∀ u : Fin 2 → galUnramifiedOutside K.1 ℚ̄ S, ordEmb S ι hv (cochainOf _ (cocycleι _ 2 W) u) =
        bockInt (zmodCocycleHom z) (u 0) (u 1) * ordAbove S v (t : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) := fun u => by
      conv_lhs => rw [hu u]
      exact hWv _ _
    have hwb' : ∀ u : Fin 2 → galUnramifiedOutside K.1 ℚ̄ S, cochainOf _ (cocycleι _ 2 wb) u =
        bockInt (zmodCocycleHom z) (u 0) (u 1) • ((unitsToInvariants K.1 (maxUnramifiedOutside K.1 ℚ̄ S)
          (Additive.ofMul (globalUniformizer v ^ ordAbove S v (t : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ))) :
            (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)).ρ.invariants) : galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) :=
      fun u => by
        conv_lhs => rw [hu u]
        exact hwbv _ _
    refine (hW' _).trans ?_
    refine Eq.trans ?_ (congrArg (ordEmb S ι hv) (hwb' _)).symm
    refine Eq.trans ?_ (map_zsmul (ordEmb S ι hv) _ _).symm
    exact (congrArg (_ * ·) hbv.symm).trans (smul_eq_mul _ _).symm
  have hloc := (gsLocalRes_eq_zero_iff S ι hv _).2 hval
  rw [map_sub, map_sub, sub_eq_zero] at hloc
  refine (congrArg (placeInv (K := K) (.inr v)) (hloc.trans (gsLocalRes_cohomologyπ_bock S ι z χ hχ
    (globalUniformizer v ^ ordAbove S v (t : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ)) wb (fun g h => hwbv g h)))).trans ?_
  refine (placeInv_galCupClass_decompHomS (Set.toFinite S) hodd χ v ι _).trans ?_
  exact congrArg (fun x => zmodToQZ n (Multiplicative.toAdd (charEquiv ℚ̄ (Set.toFinite S) hodd χ x)))
    (mk_finiteEmbedding_globalUniformizer v hv _)

end Outside

section Global

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) [Fintype S]
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  {n : ℕ} [NeZero n] (hodd : Odd n ∨ IsTotallyComplex K.1)

def divChar (χ : ContinuousMonoidHom (galUnramifiedOutside K.1 ℚ̄ S) (Multiplicative (ZMod n))) :
    sDivisor S →+ QZ :=
  (zmodToQZ n).comp (MonoidHom.toAdditiveRight ((charEquiv ℚ̄ (Set.toFinite S) hodd χ).comp
    ((sPresentation S).comp (MonoidHom.inr _ _))))

theorem divChar_apply (χ : ContinuousMonoidHom (galUnramifiedOutside K.1 ℚ̄ S) (Multiplicative (ZMod n)))
    (D : sDivisor S) :
    divChar S hodd χ D = zmodToQZ n (Multiplicative.toAdd (charEquiv ℚ̄ (Set.toFinite S) hodd χ
      (sPresentation S (1, Multiplicative.ofAdd D)))) :=
  rfl

theorem nsmul_divChar (χ : ContinuousMonoidHom (galUnramifiedOutside K.1 ℚ̄ S) (Multiplicative (ZMod n)))
    (D : sDivisor S) : n • divChar S hodd χ D = 0 := by
  rw [divChar_apply, ← map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, map_zero]

set_option maxHeartbeats 2000000 in

theorem sum_localInvU_eq_neg_divChar (t : sInvariantSubgroup ℚ̄ S)
    (z : cocycles (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1)
    (χ : ContinuousMonoidHom (galUnramifiedOutside K.1 ℚ̄ S) (Multiplicative (ZMod n)))
    (hχ : ∀ g, Multiplicative.toAdd (χ g) = zmodCocycleHom z g)
    (W : cocycles (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2)
    (hW : ∀ g h, (Additive.toMul (cochainOf _ (cocycleι _ 2 W) ![g, h]) : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) *
      ((t : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) ^ bockInt (zmodCocycleHom z) g h)⁻¹ ∈ sUnitsMax K.1 ℚ̄ S)
    (β' : ∀ v : S, cohomology (galUnits.{0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) 2)
    (y : cohomology (galSUnitsMax K.1 ℚ̄ S) 2)
    (hy : ∀ v, (cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
        (gsUnitsLocalMor S ιs v) 2).hom (cohomologyπ _ 2 W) - β' v =
      (cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
        (gsSUnitsLocalMor S ιs v) 2).hom y)
    (hβ' : n • ∑ v : S, localInvU (v : HeightOneSpectrum (𝓞 K.1)) (β' v) = 0) :
    ∑ v : S, localInvU (v : HeightOneSpectrum (𝓞 K.1)) (β' v) =
      -divChar S hodd χ (divAbove S (Additive.ofMul t)) := by
  classical
  let ιL := gsLocalEmbeddings S ιs
  let B : cohomology (unitsLimitRep K) 2 :=
    (gsBrauerInfl K S 2).hom (cohomologyULiftIntAddEquiv _ 2 (cohomologyπ _ 2 W)) - sUnitsBrauer K S y
  have hBv : ∀ w : HeightOneSpectrum (𝓞 K.1), placeInv (K := K) (.inr w) (brauerLocal ιL B (.inr w)) =
      placeInv (K := K) (.inr w) ((gsLocalRes S (ιL.fin w) 2).hom (cohomologyULiftIntAddEquiv _ 2 (cohomologyπ _ 2 W))) -
        placeInv (K := K) (.inr w) (brauerLocal ιL (sUnitsBrauer K S y) (.inr w)) := fun w => by
    have e : brauerLocal ιL B (.inr w) = brauerLocal ιL ((gsBrauerInfl K S 2).hom
        (cohomologyULiftIntAddEquiv _ 2 (cohomologyπ _ 2 W))) (.inr w) -
          brauerLocal ιL (sUnitsBrauer K S y) (.inr w) := by
      rw [map_sub, DFinsupp.sub_apply]
    rw [e, map_sub, brauerLocal_gsBrauerInfl_inr]
  have hS' : ∀ v : S, placeInv (K := K) (.inr (v : HeightOneSpectrum (𝓞 K.1)))
      (brauerLocal ιL B (.inr (v : HeightOneSpectrum (𝓞 K.1)))) = localInvU (v : HeightOneSpectrum (𝓞 K.1)) (β' v) := by
    intro v
    have hfin : ιL.fin (v : HeightOneSpectrum (𝓞 K.1)) = ιs v := gsLocalEmbeddings_fin S ιs v
    have h2 : brauerLocal ιL (sUnitsBrauer K S y) (.inr (v : HeightOneSpectrum (𝓞 K.1))) =
        (gsLocalRes S (ιs v) 2).hom (cohomologyULiftIntAddEquiv _ 2
          ((cohomologyMap (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)) 2).hom y)) := by
      rw [sUnitsBrauer_apply, brauerLocal_gsBrauerInfl_inr, hfin]
    have hyv : (cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
        (gsUnitsLocalMor S ιs v) 2).hom (cohomologyπ _ 2 W) -
        (cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
          (gsSUnitsLocalMor S ιs v) 2).hom y = β' v := by
      exact (congrArg (_ - ·) (hy v).symm).trans (sub_sub_cancel _ _)
    refine (hBv (v : HeightOneSpectrum (𝓞 K.1))).trans ?_
    refine (congrArg₂ (· - ·) (congrArg (fun ι => placeInv (K := K) (.inr (v : HeightOneSpectrum (𝓞 K.1)))
      ((gsLocalRes S ι 2).hom (cohomologyULiftIntAddEquiv _ 2 (cohomologyπ _ 2 W)))) hfin)
      (congrArg (placeInv (K := K) (.inr (v : HeightOneSpectrum (𝓞 K.1)))) h2)).trans ?_
    refine Eq.trans ?_ (congrArg (localInvU (v : HeightOneSpectrum (𝓞 K.1))) hyv)
    refine Eq.trans ?_ (map_sub _ _ _).symm
    exact congrArg₂ (· - ·) (localInvU_cohomologyMapAlong_gsUnitsLocalMor S ιs v _).symm
      (localInvU_cohomologyMapAlong_gsSUnitsLocalMor S ιs v y).symm
  have hout : ∀ (w : HeightOneSpectrum (𝓞 K.1)) (hw : w ∉ S), placeInv (K := K) (.inr w) (brauerLocal ιL B (.inr w)) =
      divChar S hodd χ (Finsupp.single ⟨w, hw⟩ (ordAbove S w (t : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ))) := by
    intro w hw
    refine (hBv w).trans ?_
    refine (congrArg₂ (· - ·) rfl ((congrArg (placeInv (K := K) (.inr w))
      (brauerLocal_sUnitsBrauer_inr K S ιL y w hw)).trans (map_zero _))).trans ((sub_zero _).trans ?_)
    exact (placeInv_gsLocalRes_of_bock S (ιL.fin w) hw hodd t z χ hχ W hW).trans (divChar_apply S hodd χ _).symm
  let D := divAbove S (Additive.ofMul t)

  let T1 := Finset.univ.image (fun v : S => (Sum.inr (v : HeightOneSpectrum (𝓞 K.1)) : Place K.1))
  let T2 := D.support.image (fun u : {v // v ∉ S} => (Sum.inr u.1 : Place K.1))
  let T3 := Finset.univ.image (fun w : InfinitePlace K.1 => (Sum.inl w : Place K.1))
  have hT : ∀ w ∉ T1 ∪ (T2 ∪ T3), placeInv w (brauerLocal ιL B w) = 0 := by
    intro w hw
    rcases w with w | w
    · exact absurd (Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_image.2 ⟨w, Finset.mem_univ _, rfl⟩))) hw
    · by_cases hwS : w ∈ S
      · exact absurd (Finset.mem_union_left _ (Finset.mem_image.2 ⟨(⟨w, hwS⟩ : S), Finset.mem_univ _, rfl⟩)) hw
      · have hD0 : D ⟨w, hwS⟩ = 0 := by
          by_contra hne
          exact hw (Finset.mem_union_right _ (Finset.mem_union_left _
            (Finset.mem_image.2 ⟨⟨w, hwS⟩, Finsupp.mem_support_iff.2 hne, rfl⟩)))
        rw [hout w hwS, show ordAbove S w (t : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) = D ⟨w, hwS⟩ from rfl, hD0,
          Finsupp.single_zero, map_zero]
  have hd12 : Disjoint T1 (T2 ∪ T3) := by
    rw [Finset.disjoint_left]
    intro w hw1 hw23
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hw1
    rcases Finset.mem_union.1 hw23 with h | h
    · obtain ⟨u, hu, hu'⟩ := Finset.mem_image.1 h
      exact u.2 (Sum.inr_injective hu' ▸ v.2)
    · obtain ⟨u, -, hu⟩ := Finset.mem_image.1 h
      exact Sum.inl_ne_inr hu
  have hd23 : Disjoint T2 T3 := by
    rw [Finset.disjoint_left]
    intro w hw2 hw3
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hw2
    obtain ⟨x, -, hx⟩ := Finset.mem_image.1 hw3
    exact Sum.inl_ne_inr hx
  have hsum : ∑ v : S, localInvU (v : HeightOneSpectrum (𝓞 K.1)) (β' v) + (divChar S hodd χ D +
      ∑ w : InfinitePlace K.1, placeInv (.inl w) (brauerLocal ιL B (.inl w))) = 0 := by
    have e := (AddMonoidHom.comp_apply _ _ _).symm.trans (brauerSumInv_eq_zero ιL B)
    rw [sumPlaceInv_eq_sum_of_placeInv _ _ hT, Finset.sum_union hd12, Finset.sum_union hd23,
      Finset.sum_image (fun v _ w _ h => Subtype.ext (Sum.inr_injective h)),
      Finset.sum_image (fun u _ x _ h => Subtype.ext (Sum.inr_injective h)),
      Finset.sum_image (fun u _ x _ h => Sum.inl_injective h)] at e
    have e1 : ∑ v : S, placeInv (K := K) (.inr (v : HeightOneSpectrum (𝓞 K.1)))
        (brauerLocal ιL B (.inr (v : HeightOneSpectrum (𝓞 K.1)))) =
          ∑ v : S, localInvU (v : HeightOneSpectrum (𝓞 K.1)) (β' v) := Finset.sum_congr rfl fun v _ => hS' v
    have e2 : ∑ u ∈ D.support, placeInv (K := K) (.inr u.1) (brauerLocal ιL B (.inr u.1)) = divChar S hodd χ D := by
      rw [Finset.sum_congr rfl fun u _ => hout u.1 u.2]
      conv_rhs => rw [← Finsupp.sum_single D]
      rw [map_finsuppSum]
      rfl
    exact (congrArg₂ (· + ·) e1.symm (congrArg₂ (· + ·) e2.symm rfl)).trans e
  generalize hs1 : ∑ v : S, localInvU (v : HeightOneSpectrum (𝓞 K.1)) (β' v) = s1 at hsum hβ' ⊢
  generalize hs3 : ∑ w : InfinitePlace K.1, placeInv (.inl w) (brauerLocal ιL B (.inl w)) = s3 at hsum
  have h32 : 2 • s3 = 0 := by
    rw [← hs3, Finset.smul_sum]
    exact Finset.sum_eq_zero fun w _ => two_nsmul_placeInv_inl w _
  have h3 : s3 = 0 := by
    rcases id hodd with ⟨m, hm⟩ | hc
    · have h3n : n • s3 = 0 := by
        have : s3 = -(s1 + divChar S hodd χ D) := by
          rw [eq_neg_iff_add_eq_zero, add_comm, add_assoc]
          exact hsum
        rw [this, smul_neg, smul_add, hβ', nsmul_divChar, add_zero, neg_zero]
      rw [hm] at h3n
      have : s3 = (2 * m + 1) • s3 - m • (2 • s3) := by
        rw [← mul_nsmul', add_nsmul, one_nsmul, mul_comm m 2]
        abel
      rw [this, h3n, h32, smul_zero, sub_zero]
    · rw [← hs3]
      exact Finset.sum_eq_zero fun w _ => by
        have := subsingleton_cohomology_two_of_isComplex w (hc.isComplex w)
        rw [show brauerLocal ιL B (.inl w) = 0 from Subsingleton.elim (α := cohomology (galUnitsZ w.Completion
          (AlgebraicClosure w.Completion)) 2) _ 0, map_zero]
  rw [h3, add_zero] at hsum
  exact eq_neg_of_add_eq_zero_left hsum

end Global

end

end GroundTheory.ProfCoh
