import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalLimits.InfRange
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.LocalTransition
import GroundTheory.ProfiniteCohomology.FilteredHomology
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory IsDedekindDomain NumberField IntermediateField GroundTheory.Global
  GroundTheory.Global.SemiLocal FiniteSubfield

open scoped Pointwise NumberField.LiesOver

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} {v : NumberField.InfinitePlace K.1}
  (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure v.Completion)

section Level

variable (F : FiniteSubfield) [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal]

abbrev infLocalLevelRep :
    Rep ℤ (MulAction.stabilizer Gal(F.1/K.1) (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1)) :=
  Rep.ofMulDistribMulAction (MulAction.stabilizer Gal(F.1/K.1) (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1))
    ((infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion)ˣ

abbrev infLocalCochainsInfl :
    cochainsComplex (infLocalLevelRep ι F) ⟶
      cochainsComplex (galUnitsZ v.Completion (AlgebraicClosure v.Completion)) :=
  cochainsMapAlong (infLocalDecompHom ι F) (continuous_infLocalDecompHom ι F) (infLocalUnitsMor ι F)

theorem infLocalUnitsMor_injective : Function.Injective (infLocalUnitsMor ι F).hom := by
  intro a b h
  have h' := congrArg (fun u ↦ ((Additive.toMul u :
    (AlgebraicClosure v.Completion)ˣ) : AlgebraicClosure v.Completion)) h
  simp only at h'
  exact congrArg Additive.ofMul (Units.ext ((infCompletionEmbedding ι F).toRingHom.injective h'))

theorem infLocalCochains_injective (m : ℕ) : Function.Injective ((infLocalCochainsInfl ι F).f m).hom := by
  intro y y' h
  apply (ModuleCat.mono_iff_injective ((cochainsComplexι (infLocalLevelRep ι F)).f m)).1 inferInstance
  funext τ
  obtain ⟨σ, rfl⟩ : ∃ σ : Fin m → Gal(AlgebraicClosure v.Completion/v.Completion),
      (fun i ↦ infLocalDecompHom ι F (σ i)) = τ :=
    ⟨fun i ↦ Function.surjInv (infLocalDecompHom_surjective ι F) (τ i),
      funext fun i ↦ Function.surjInv_eq (infLocalDecompHom_surjective ι F) (τ i)⟩
  have h1 := congrFun (congrArg (fun c ↦ ((cochainsComplexι
    (galUnitsZ v.Completion (AlgebraicClosure v.Completion))).f m).hom c) h) σ
  exact infLocalUnitsMor_injective ι F h1

end Level

theorem exists_infLevel_factor (m : ℕ)
    (f : (Fin m → Gal(AlgebraicClosure v.Completion/v.Completion)) →
      Additive (AlgebraicClosure v.Completion)ˣ) :
    ∃ (p : GLevel K) (z : (Fin m → MulAction.stabilizer Gal(p.1.1/K.1)
      (infPlaceOfEmbedding ι p.1 : NumberField.InfinitePlace p.1.1)) →
        ((infPlaceOfEmbedding ι p.1 : NumberField.InfinitePlace p.1.1).Completion)ˣ),
      ∀ g, infCompletionEmbedding ι p.1 (z fun i ↦ infLocalDecompHom ι p.1 (g i)) =
        ((Additive.toMul (f g) : (AlgebraicClosure v.Completion)ˣ) :
          AlgebraicClosure v.Completion) := by
  have hp := exists_level_infCompletionEmbedding_surjective ι
  obtain ⟨p, hp⟩ := hp
  have hsurj := hp p le_rfl
  have hinj := infLocalDecompHom_injective ι p.1 hsurj
  have hval : ∀ g, ∃ z : ((infPlaceOfEmbedding ι p.1 : NumberField.InfinitePlace p.1.1).Completion)ˣ,
      infCompletionEmbedding ι p.1 z = ((Additive.toMul (f g) :
        (AlgebraicClosure v.Completion)ˣ) : AlgebraicClosure v.Completion) := by
    intro g
    have hy := hsurj ((Additive.toMul (f g) : (AlgebraicClosure v.Completion)ˣ) :
      AlgebraicClosure v.Completion)
    obtain ⟨y, hy⟩ := hy
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [map_zero] at hy
      exact (Additive.toMul (f g) : (AlgebraicClosure v.Completion)ˣ).ne_zero hy.symm
    exact ⟨Units.mk0 y hy0, by rw [Units.val_mk0, hy]⟩
  choose z hz using hval
  refine ⟨p, fun τ ↦ z fun i ↦ Function.surjInv (infLocalDecompHom_surjective ι p.1) (τ i),
    fun g ↦ ?_⟩
  have hg : (fun i ↦ Function.surjInv (infLocalDecompHom_surjective ι p.1)
      (infLocalDecompHom ι p.1 (g i))) = g :=
    funext fun i ↦ hinj (Function.surjInv_eq (infLocalDecompHom_surjective ι p.1) _)
  change infCompletionEmbedding ι p.1 (z fun i ↦ Function.surjInv
    (infLocalDecompHom_surjective ι p.1) (infLocalDecompHom ι p.1 (g i))) = _
  rw [hg]
  exact hz g

theorem exists_infLocalCochains_eq (m : ℕ)
    (x : (cochainsComplex (galUnitsZ v.Completion (AlgebraicClosure v.Completion))).X m) :
    ∃ (p : GLevel K) (y : (cochainsComplex (infLocalLevelRep ι p.1)).X m),
      ((infLocalCochainsInfl ι p.1).f m).hom y = x := by
  have hfac := exists_infLevel_factor ι m (((cochainsComplexι (galUnitsZ v.Completion (AlgebraicClosure v.Completion))).f m).hom x)
  obtain ⟨p, z, hz⟩ := hfac
  refine ⟨p, ⟨fun τ ↦ Additive.ofMul (z τ), IsLocallyConstant.of_discrete _⟩, ?_⟩
  apply (ModuleCat.mono_iff_injective ((cochainsComplexι (galUnitsZ v.Completion (AlgebraicClosure v.Completion))).f m)).1 inferInstance
  funext g
  exact congrArg Additive.ofMul (Units.ext ((infLocalUnitsMor_hom_apply ι p.1 _).trans (hz g)))

section Transition

variable {F E : FiniteSubfield} [Fact (K ≤ F)] [Fact (K ≤ E)] [Fact (F ≤ E)]
  [F.1.fixingSubgroup.Normal] [E.1.fixingSubgroup.Normal]

theorem infDecompRestrict_infLocalDecompHom
    (σ : Gal(AlgebraicClosure v.Completion/v.Completion)) :
    infDecompRestrict (w := infPlaceOfEmbedding ι F) (w' := infPlaceOfEmbedding ι E)
      (infLocalDecompHom ι E σ) = infLocalDecompHom ι F σ := by
  apply Subtype.ext
  rw [coe_infDecompRestrict, coe_infLocalDecompHom]
  refine ((decompHom_eq_iff (infEmbedLevel ι F) σ _).2 fun x ↦ ?_).symm
  rw [infEmbedLevel_apply, infEmbedLevel_apply]
  have h1 := coe_levelRestrict_apply (K := K) (F := F) (E := E)
    (infLocalDecompHom ι E σ : Gal(E.1/K.1)) x
  have h2 := ι_infLocalDecompHom_apply ι E σ (algebraMap F.1 E.1 x)
  rw [← h1] at h2
  exact h2

theorem infLocalUnitsMor_infCompletionUnitsRep (a : Additive ((infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion)ˣ) :
    (infLocalUnitsMor ι E).hom ((infCompletionUnitsRep (w := infPlaceOfEmbedding ι F)
      (w' := infPlaceOfEmbedding ι E)).hom a) = (infLocalUnitsMor ι F).hom a :=
  congrArg Additive.ofMul (Units.ext (infCompletionEmbedding_completionMap ι _))

theorem infLocalCochains_comp :
    cochainsMapAlong (infDecompRestrict (w := infPlaceOfEmbedding ι F) (w' := infPlaceOfEmbedding ι E))
      continuous_of_discreteTopology infCompletionUnitsRep ≫ infLocalCochainsInfl ι E =
      infLocalCochainsInfl ι F := by
  rw [← cochainsMapAlong_comp]
  ext m x : 3
  apply Subtype.ext
  funext g
  have hfun : (fun i ↦ infDecompRestrict (w := infPlaceOfEmbedding ι F) (w' := infPlaceOfEmbedding ι E)
      (infLocalDecompHom ι E (g i))) = fun i ↦ infLocalDecompHom ι F (g i) :=
    funext fun i ↦ infDecompRestrict_infLocalDecompHom ι (g i)
  exact (infLocalUnitsMor_infCompletionUnitsRep ι _).trans
    (congrArg (fun τ ↦ (infLocalUnitsMor ι F).hom
      (((cochainsComplexι (infLocalLevelRep ι F)).f m).hom x τ)) hfun)

theorem infLocalTransition_comp_infLocalInfl (n : ℕ) :
    infLocalTransition K F E (infPlaceOfEmbedding ι F) (infPlaceOfEmbedding ι E) n ≫ infLocalInfl ι E n =
      infLocalInfl ι F n := by
  have h := congrArg (fun φ ↦ HomologicalComplex.homologyMap φ n)
    (infLocalCochains_comp ι (F := F) (E := E))
  simp only [HomologicalComplex.homologyMap_comp] at h
  exact h

end Transition

section Generic

variable (F : FiniteSubfield) [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal]

set_option maxHeartbeats 4000000 in

theorem exists_infLocalInfl_eq_homologyπ (n : ℕ)
    (z : (cochainsComplex (galUnitsZ v.Completion (AlgebraicClosure v.Completion))).cycles n)
    (y₀ : (cochainsComplex (infLocalLevelRep ι F)).X n)
    (hy₀ : ((infLocalCochainsInfl ι F).f n).hom y₀ = ((cochainsComplex (galUnitsZ v.Completion (AlgebraicClosure v.Completion))).iCycles n).hom z) :
    ∃ y : cohomology (infLocalLevelRep ι F) n, (infLocalInfl ι F n).hom y =
      ((cochainsComplex (galUnitsZ v.Completion (AlgebraicClosure v.Completion))).homologyπ n).hom z := by
  have hd : ((cochainsComplex (infLocalLevelRep ι F)).d n (n + 1)).hom y₀ = 0 := by
    apply infLocalCochains_injective ι F (n + 1)
    rw [map_zero, hom_f_d_apply, hy₀]
    exact iCycles_d_apply _ n (n + 1) z
  obtain ⟨w, hw⟩ := exists_iCycles_eq_of_d_eq_zero _ n y₀ hd
  refine ⟨((cochainsComplex (infLocalLevelRep ι F)).homologyπ n).hom w,
    (homologyMap_homologyπ_apply (infLocalCochainsInfl ι F) n w).trans (congrArg _ ?_)⟩
  apply (ModuleCat.mono_iff_injective ((cochainsComplex (galUnitsZ v.Completion (AlgebraicClosure v.Completion))).iCycles n)).1 inferInstance
  rw [iCycles_cyclesMap_apply, hw, hy₀]

set_option maxHeartbeats 4000000 in

theorem exists_d_eq_of_infLocalInfl_eq_zero (n : ℕ) (w : (cochainsComplex (infLocalLevelRep ι F)).cycles n)
    (hy : (infLocalInfl ι F n).hom (((cochainsComplex (infLocalLevelRep ι F)).homologyπ n).hom w) = 0) :
    ∃ u : (cochainsComplex (galUnitsZ v.Completion (AlgebraicClosure v.Completion))).X ((ComplexShape.up ℕ).prev n),
      ((cochainsComplex (galUnitsZ v.Completion (AlgebraicClosure v.Completion))).d _ n).hom u =
        ((infLocalCochainsInfl ι F).f n).hom (((cochainsComplex (infLocalLevelRep ι F)).iCycles n).hom w) := by
  have hy' := (homologyMap_homologyπ_apply (infLocalCochainsInfl ι F) n w).symm.trans hy
  obtain ⟨u, hu⟩ := (homologyπ_eq_zero_iff _ _).1 hy'
  rw [iCycles_cyclesMap_apply] at hu
  exact ⟨u, hu⟩

end Generic

section GenericTransition

variable {F M E : FiniteSubfield} [Fact (K ≤ F)] [Fact (K ≤ M)] [Fact (K ≤ E)] [Fact (F ≤ E)]
  [Fact (M ≤ E)] [F.1.fixingSubgroup.Normal] [M.1.fixingSubgroup.Normal] [E.1.fixingSubgroup.Normal]

set_option maxHeartbeats 4000000 in

theorem infLocalTransition_homologyπ_eq_zero (n : ℕ) (w : (cochainsComplex (infLocalLevelRep ι F)).cycles n)
    (u' : (cochainsComplex (infLocalLevelRep ι M)).X ((ComplexShape.up ℕ).prev n))
    (hu : ((cochainsComplex (galUnitsZ v.Completion (AlgebraicClosure v.Completion))).d _ n).hom (((infLocalCochainsInfl ι M).f _).hom u') =
        ((infLocalCochainsInfl ι F).f n).hom (((cochainsComplex (infLocalLevelRep ι F)).iCycles n).hom w)) :
    (infLocalTransition K F E (infPlaceOfEmbedding ι F) (infPlaceOfEmbedding ι E) n).hom
      (((cochainsComplex (infLocalLevelRep ι F)).homologyπ n).hom w) = 0 := by
  refine (homologyMap_homologyπ_apply (cochainsMapAlong (infDecompRestrict (w := infPlaceOfEmbedding ι F)
    (w' := infPlaceOfEmbedding ι E)) continuous_of_discreteTopology infCompletionUnitsRep) n w).trans
    ((homologyπ_eq_zero_iff _ _).2 ⟨((cochainsMapAlong (infDecompRestrict (w := infPlaceOfEmbedding ι M)
      (w' := infPlaceOfEmbedding ι E)) continuous_of_discreteTopology infCompletionUnitsRep).f _).hom u',
      ?_⟩)
  rw [iCycles_cyclesMap_apply]
  apply infLocalCochains_injective ι E n
  rw [hom_f_d_apply]
  have e1 := congrArg (fun φ ↦ (φ.f _).hom u') (infLocalCochains_comp ι (F := M) (E := E))
  have e2 := congrArg (fun φ ↦ (φ.f n).hom (((cochainsComplex (infLocalLevelRep ι F)).iCycles n).hom w))
    (infLocalCochains_comp ι (F := F) (E := E))
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at e1 e2
  exact (congrArg (fun c ↦ ((cochainsComplex (galUnitsZ v.Completion (AlgebraicClosure v.Completion))).d _ n).hom c) e1).trans (hu.trans e2.symm)

end GenericTransition

set_option maxHeartbeats 4000000 in

theorem exists_infLocalInfl_eq (n : ℕ)
    (x : cohomology (galUnitsZ v.Completion (AlgebraicClosure v.Completion)) n) :
    ∃ (p : GLevel K) (y : cohomology (infLocalLevelRep ι p.1) n), (infLocalInfl ι p.1 n).hom y = x := by
  have hz := (ModuleCat.epi_iff_surjective ((cochainsComplex (galUnitsZ v.Completion (AlgebraicClosure v.Completion))).homologyπ n)).1 inferInstance x
  obtain ⟨z, rfl⟩ := hz
  have hc := exists_infLocalCochains_eq ι n (((cochainsComplex (galUnitsZ v.Completion (AlgebraicClosure v.Completion))).iCycles n).hom z)
  obtain ⟨p, y₀, hy₀⟩ := hc
  have hy := exists_infLocalInfl_eq_homologyπ ι p.1 n z y₀ hy₀
  obtain ⟨y, hy⟩ := hy
  exact ⟨p, y, hy⟩

set_option maxHeartbeats 4000000 in

theorem exists_infLocalTransition_eq_zero (n : ℕ) (p : GLevel K) (y : cohomology (infLocalLevelRep ι p.1) n)
    (hy : (infLocalInfl ι p.1 n).hom y = 0) :
    ∃ (q : GLevel K) (h : p ≤ q), (haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
      (infLocalTransition K p.1 q.1 (infPlaceOfEmbedding ι p.1) (infPlaceOfEmbedding ι q.1) n).hom y) = 0 := by
  have hw := (ModuleCat.epi_iff_surjective
    ((cochainsComplex (infLocalLevelRep ι p.1)).homologyπ n)).1 inferInstance y
  obtain ⟨w, rfl⟩ := hw
  have hu := exists_d_eq_of_infLocalInfl_eq_zero ι p.1 n w hy
  obtain ⟨u, hu⟩ := hu
  have hq := exists_infLocalCochains_eq ι _ u
  obtain ⟨q, u', hu'⟩ := hq
  have hr := GLevel.exists_ge p q
  obtain ⟨r, hpr, hqr⟩ := hr
  have : Fact (p.1 ≤ r.1) := ⟨hpr⟩
  have : Fact (q.1 ≤ r.1) := ⟨hqr⟩
  exact ⟨r, hpr, infLocalTransition_homologyπ_eq_zero ι (M := q.1) n w u' (by rw [hu', hu])⟩

end

end GroundTheory.ProfCoh
