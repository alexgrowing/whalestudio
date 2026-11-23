import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalLimits.ApplyCompletionEmbeddingOfLocalDecompHomEqOne
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.LocalTransition
import GroundTheory.ProfiniteCohomology.FilteredHomology
import GroundTheory.ProfiniteCohomology.Factor
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory IsDedekindDomain NumberField IntermediateField GroundTheory.Global
  GroundTheory.Global.SemiLocal FiniteSubfield

open scoped Pointwise

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} {v : HeightOneSpectrum (𝓞 K.1)}
  (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1))

section Level

variable (F : FiniteSubfield) [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal]

abbrev localLevelRep :
    Rep ℤ (MulAction.stabilizer Gal(F.1/K.1) (placeOfEmbedding ι F).1.asIdeal) :=
  Rep.ofMulDistribMulAction (MulAction.stabilizer Gal(F.1/K.1) (placeOfEmbedding ι F).1.asIdeal)
    ((placeOfEmbedding ι F).1.adicCompletion F.1)ˣ

abbrev localCochainsInfl :
    cochainsComplex (localLevelRep ι F) ⟶
      cochainsComplex (galUnitsZ (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))) :=
  cochainsMapAlong (localDecompHom ι F) (continuous_localDecompHom ι F) (localUnitsMor ι F)

theorem localUnitsMor_injective : Function.Injective (localUnitsMor ι F).hom := by
  intro a b h
  have h' := congrArg (fun u ↦ ((Additive.toMul u :
    (AlgebraicClosure (v.adicCompletion K.1))ˣ) : AlgebraicClosure (v.adicCompletion K.1))) h
  simp only at h'
  exact congrArg Additive.ofMul (Units.ext ((completionEmbedding ι F).toRingHom.injective h'))

theorem localCochains_injective (m : ℕ) : Function.Injective ((localCochainsInfl ι F).f m).hom := by
  intro y y' h
  apply (ModuleCat.mono_iff_injective ((cochainsComplexι (localLevelRep ι F)).f m)).1 inferInstance
  funext τ
  obtain ⟨σ, rfl⟩ : ∃ σ : Fin m → Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1),
      (fun i ↦ localDecompHom ι F (σ i)) = τ :=
    ⟨fun i ↦ Function.surjInv (localDecompHom_surjective ι F) (τ i),
      funext fun i ↦ Function.surjInv_eq (localDecompHom_surjective ι F) (τ i)⟩
  have h1 := congrFun (congrArg (fun c ↦ ((cochainsComplexι
    (galUnitsZ (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)))).f m).hom c) h) σ
  exact localUnitsMor_injective ι F h1

end Level

theorem localDecompHom_eq_one_of_le {F E : FiniteSubfield} [Fact (K ≤ F)] [Fact (K ≤ E)]
    [F.1.fixingSubgroup.Normal] [E.1.fixingSubgroup.Normal] (h : F.1 ≤ E.1)
    {σ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1)}
    (hσ : localDecompHom ι E σ = 1) : localDecompHom ι F σ = 1 := by
  have hE : ∀ y : E.1, σ (ι y) = ι y := fun y ↦ by
    have := ι_localDecompHom_apply ι E σ y
    rw [hσ] at this
    exact this.symm
  apply Subtype.ext
  rw [coe_localDecompHom, OneMemClass.coe_one]
  refine (decompHom_eq_iff (embedLevel ι F) σ 1).2 fun x ↦ ?_
  rw [embedLevel_apply, embedLevel_apply, AlgEquiv.one_apply]
  exact (hE ⟨x, h x.2⟩).symm

theorem localDecompHom_inv_mul_eq_one (F : FiniteSubfield) [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal]
    {σ τ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1)}
    (h : localDecompHom ι F σ = localDecompHom ι F τ) : localDecompHom ι F (σ⁻¹ * τ) = 1 := by
  rw [map_mul, map_inv, h, inv_mul_cancel]

theorem exists_level_factor (m : ℕ)
    {f : (Fin m → Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1)) →
      Additive (AlgebraicClosure (v.adicCompletion K.1))ˣ} (hf : IsLocallyConstant f) :
    ∃ (p : GLevel K) (z : (Fin m → MulAction.stabilizer Gal(p.1.1/K.1)
      (placeOfEmbedding ι p.1).1.asIdeal) → ((placeOfEmbedding ι p.1).1.adicCompletion p.1.1)ˣ),
      ∀ g, completionEmbedding ι p.1 (z fun i ↦ localDecompHom ι p.1 (g i)) =
        ((Additive.toMul (f g) : (AlgebraicClosure (v.adicCompletion K.1))ˣ) :
          AlgebraicClosure (v.adicCompletion K.1)) := by
  obtain ⟨U, hU⟩ := exists_openNormalSubgroup_fin_of_isLocallyConstant hf
  have h₁ker := exists_level_ker_le ι U.toOpenSubgroup.mem_nhds_one
  obtain ⟨p₁, hp₁⟩ := h₁ker
  have hfin : (Set.range f).Finite := hf.range_finite
  classical
  have h₂mem := exists_level_forall_mem ι (hfin.toFinset.image fun a ↦
    ((Additive.toMul a : (AlgebraicClosure (v.adicCompletion K.1))ˣ) :
      AlgebraicClosure (v.adicCompletion K.1)))
  obtain ⟨p₂, hp₂⟩ := h₂mem
  have hge := GLevel.exists_ge p₁ p₂
  obtain ⟨p, h₁, h₂⟩ := hge
  have hker : ∀ σ, localDecompHom ι p.1 σ = 1 → σ ∈ U :=
    fun σ hσ ↦ hp₁ σ (localDecompHom_eq_one_of_le ι (show p₁.1.1 ≤ p.1.1 from h₁) hσ)
  have hval : ∀ g, ∃ z : ((placeOfEmbedding ι p.1).1.adicCompletion p.1.1)ˣ,
      completionEmbedding ι p.1 z = ((Additive.toMul (f g) :
        (AlgebraicClosure (v.adicCompletion K.1))ˣ) : AlgebraicClosure (v.adicCompletion K.1)) := by
    intro g
    have hy₀' := hp₂ _ (Finset.mem_image_of_mem _ (by simp : f g ∈ hfin.toFinset))
    obtain ⟨y₀, hy₀⟩ := hy₀'
    have hy' := exists_completionEmbedding_eq_of_le ι h₂ y₀
    obtain ⟨y, hy⟩ := hy'
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [map_zero] at hy
      exact (Additive.toMul (f g) : (AlgebraicClosure (v.adicCompletion K.1))ˣ).ne_zero
        (hy.trans hy₀).symm
    exact ⟨Units.mk0 y hy0, by rw [Units.val_mk0, hy, hy₀]⟩
  choose z hz using hval
  refine ⟨p, fun τ ↦ z fun i ↦ Function.surjInv (localDecompHom_surjective ι p.1) (τ i),
    fun g ↦ ?_⟩
  rw [hz]
  have hfg : f (fun i ↦ Function.surjInv (localDecompHom_surjective ι p.1)
      (localDecompHom ι p.1 (g i))) = f g := hU _ _ fun i ↦ hker _
    (localDecompHom_inv_mul_eq_one ι p.1 (Function.surjInv_eq (localDecompHom_surjective ι p.1) _))
  rw [hfg]

theorem exists_localCochains_eq (m : ℕ)
    (x : (cochainsComplex (galUnitsZ (v.adicCompletion K.1)
      (AlgebraicClosure (v.adicCompletion K.1)))).X m) :
    ∃ (p : GLevel K) (y : (cochainsComplex (localLevelRep ι p.1)).X m),
      ((localCochainsInfl ι p.1).f m).hom y = x := by
  have hfac := exists_level_factor ι m (f := ((cochainsComplexι (galUnitsZ
    (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)))).f m).hom x) x.2
  obtain ⟨p, z, hz⟩ := hfac
  refine ⟨p, ⟨fun τ ↦ Additive.ofMul (z τ), IsLocallyConstant.of_discrete _⟩, ?_⟩
  apply (ModuleCat.mono_iff_injective ((cochainsComplexι (galUnitsZ (v.adicCompletion K.1)
    (AlgebraicClosure (v.adicCompletion K.1)))).f m)).1 inferInstance
  funext g
  exact congrArg Additive.ofMul (Units.ext ((localUnitsMor_hom_apply ι p.1 _).trans (hz g)))

section Transition

variable {F E : FiniteSubfield} [Fact (K ≤ F)] [Fact (K ≤ E)] [Fact (F ≤ E)]
  [F.1.fixingSubgroup.Normal] [E.1.fixingSubgroup.Normal]

theorem decompRestrict_localDecompHom
    (σ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1)) :
    decompRestrict (w := placeOfEmbedding ι F) (w' := placeOfEmbedding ι E)
      (localDecompHom ι E σ) = localDecompHom ι F σ := by
  apply Subtype.ext
  rw [coe_decompRestrict, coe_localDecompHom]
  refine ((decompHom_eq_iff (embedLevel ι F) σ _).2 fun x ↦ ?_).symm
  rw [embedLevel_apply, embedLevel_apply]
  have h1 := coe_levelRestrict_apply (K := K) (F := F) (E := E)
    (localDecompHom ι E σ : Gal(E.1/K.1)) x
  have h2 := ι_localDecompHom_apply ι E σ (algebraMap F.1 E.1 x)
  rw [← h1] at h2
  exact h2

theorem localUnitsMor_completionUnitsRep (a : Additive ((placeOfEmbedding ι F).1.adicCompletion F.1)ˣ) :
    (localUnitsMor ι E).hom ((completionUnitsRep (w := placeOfEmbedding ι F)
      (w' := placeOfEmbedding ι E)).hom a) = (localUnitsMor ι F).hom a :=
  congrArg Additive.ofMul (Units.ext (completionEmbedding_completionMap ι _))

theorem localCochains_comp :
    cochainsMapAlong (decompRestrict (w := placeOfEmbedding ι F) (w' := placeOfEmbedding ι E))
      continuous_of_discreteTopology completionUnitsRep ≫ localCochainsInfl ι E =
      localCochainsInfl ι F := by
  rw [← cochainsMapAlong_comp]
  ext m x : 3
  apply Subtype.ext
  funext g
  have hfun : (fun i ↦ decompRestrict (w := placeOfEmbedding ι F) (w' := placeOfEmbedding ι E)
      (localDecompHom ι E (g i))) = fun i ↦ localDecompHom ι F (g i) :=
    funext fun i ↦ decompRestrict_localDecompHom ι (g i)
  exact (localUnitsMor_completionUnitsRep ι _).trans
    (congrArg (fun τ ↦ (localUnitsMor ι F).hom
      (((cochainsComplexι (localLevelRep ι F)).f m).hom x τ)) hfun)

theorem localTransition_comp_localInfl (n : ℕ) :
    localTransition K F E (placeOfEmbedding ι F) (placeOfEmbedding ι E) n ≫ localInfl ι E n =
      localInfl ι F n := by
  have h := congrArg (fun φ ↦ HomologicalComplex.homologyMap φ n)
    (localCochains_comp ι (F := F) (E := E))
  simp only [HomologicalComplex.homologyMap_comp] at h
  exact h

end Transition

section Generic

variable (F : FiniteSubfield) [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal]

set_option maxHeartbeats 4000000 in

theorem exists_localInfl_eq_homologyπ (n : ℕ)
    (z : (cochainsComplex (galUnitsZ (v.adicCompletion K.1)
      (AlgebraicClosure (v.adicCompletion K.1)))).cycles n)
    (y₀ : (cochainsComplex (localLevelRep ι F)).X n)
    (hy₀ : ((localCochainsInfl ι F).f n).hom y₀ = ((cochainsComplex (galUnitsZ (v.adicCompletion K.1)
      (AlgebraicClosure (v.adicCompletion K.1)))).iCycles n).hom z) :
    ∃ y : cohomology (localLevelRep ι F) n, (localInfl ι F n).hom y =
      ((cochainsComplex (galUnitsZ (v.adicCompletion K.1)
        (AlgebraicClosure (v.adicCompletion K.1)))).homologyπ n).hom z := by
  have hd : ((cochainsComplex (localLevelRep ι F)).d n (n + 1)).hom y₀ = 0 := by
    apply localCochains_injective ι F (n + 1)
    rw [map_zero, hom_f_d_apply, hy₀]
    exact iCycles_d_apply _ n (n + 1) z
  obtain ⟨w, hw⟩ := exists_iCycles_eq_of_d_eq_zero _ n y₀ hd
  refine ⟨((cochainsComplex (localLevelRep ι F)).homologyπ n).hom w,
    (homologyMap_homologyπ_apply (localCochainsInfl ι F) n w).trans (congrArg _ ?_)⟩
  apply (ModuleCat.mono_iff_injective ((cochainsComplex (galUnitsZ (v.adicCompletion K.1)
    (AlgebraicClosure (v.adicCompletion K.1)))).iCycles n)).1 inferInstance
  rw [iCycles_cyclesMap_apply, hw, hy₀]

set_option maxHeartbeats 4000000 in

theorem exists_d_eq_of_localInfl_eq_zero (n : ℕ) (w : (cochainsComplex (localLevelRep ι F)).cycles n)
    (hy : (localInfl ι F n).hom (((cochainsComplex (localLevelRep ι F)).homologyπ n).hom w) = 0) :
    ∃ u : (cochainsComplex (galUnitsZ (v.adicCompletion K.1)
        (AlgebraicClosure (v.adicCompletion K.1)))).X ((ComplexShape.up ℕ).prev n),
      ((cochainsComplex (galUnitsZ (v.adicCompletion K.1)
        (AlgebraicClosure (v.adicCompletion K.1)))).d _ n).hom u =
        ((localCochainsInfl ι F).f n).hom (((cochainsComplex (localLevelRep ι F)).iCycles n).hom w) := by
  have hy' := (homologyMap_homologyπ_apply (localCochainsInfl ι F) n w).symm.trans hy
  obtain ⟨u, hu⟩ := (homologyπ_eq_zero_iff _ _).1 hy'
  rw [iCycles_cyclesMap_apply] at hu
  exact ⟨u, hu⟩

end Generic

section GenericTransition

variable {F M E : FiniteSubfield} [Fact (K ≤ F)] [Fact (K ≤ M)] [Fact (K ≤ E)] [Fact (F ≤ E)]
  [Fact (M ≤ E)] [F.1.fixingSubgroup.Normal] [M.1.fixingSubgroup.Normal] [E.1.fixingSubgroup.Normal]

set_option maxHeartbeats 4000000 in

theorem localTransition_homologyπ_eq_zero (n : ℕ) (w : (cochainsComplex (localLevelRep ι F)).cycles n)
    (u' : (cochainsComplex (localLevelRep ι M)).X ((ComplexShape.up ℕ).prev n))
    (hu : ((cochainsComplex (galUnitsZ (v.adicCompletion K.1)
        (AlgebraicClosure (v.adicCompletion K.1)))).d _ n).hom (((localCochainsInfl ι M).f _).hom u') =
        ((localCochainsInfl ι F).f n).hom (((cochainsComplex (localLevelRep ι F)).iCycles n).hom w)) :
    (localTransition K F E (placeOfEmbedding ι F) (placeOfEmbedding ι E) n).hom
      (((cochainsComplex (localLevelRep ι F)).homologyπ n).hom w) = 0 := by
  refine (homologyMap_homologyπ_apply (cochainsMapAlong (decompRestrict (w := placeOfEmbedding ι F)
    (w' := placeOfEmbedding ι E)) continuous_of_discreteTopology completionUnitsRep) n w).trans
    ((homologyπ_eq_zero_iff _ _).2 ⟨((cochainsMapAlong (decompRestrict (w := placeOfEmbedding ι M)
      (w' := placeOfEmbedding ι E)) continuous_of_discreteTopology completionUnitsRep).f _).hom u',
      ?_⟩)
  rw [iCycles_cyclesMap_apply]
  apply localCochains_injective ι E n
  rw [hom_f_d_apply]
  have e1 := congrArg (fun φ ↦ (φ.f _).hom u') (localCochains_comp ι (F := M) (E := E))
  have e2 := congrArg (fun φ ↦ (φ.f n).hom (((cochainsComplex (localLevelRep ι F)).iCycles n).hom w))
    (localCochains_comp ι (F := F) (E := E))
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at e1 e2
  exact (congrArg (fun c ↦ ((cochainsComplex (galUnitsZ (v.adicCompletion K.1)
    (AlgebraicClosure (v.adicCompletion K.1)))).d _ n).hom c) e1).trans (hu.trans e2.symm)

end GenericTransition

set_option maxHeartbeats 4000000 in

theorem exists_localInfl_eq (n : ℕ)
    (x : cohomology (galUnitsZ (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))) n) :
    ∃ (p : GLevel K) (y : cohomology (localLevelRep ι p.1) n), (localInfl ι p.1 n).hom y = x := by
  have hz := (ModuleCat.epi_iff_surjective ((cochainsComplex (galUnitsZ (v.adicCompletion K.1)
    (AlgebraicClosure (v.adicCompletion K.1)))).homologyπ n)).1 inferInstance x
  obtain ⟨z, rfl⟩ := hz
  have hc := exists_localCochains_eq ι n (((cochainsComplex (galUnitsZ (v.adicCompletion K.1)
    (AlgebraicClosure (v.adicCompletion K.1)))).iCycles n).hom z)
  obtain ⟨p, y₀, hy₀⟩ := hc
  have hy := exists_localInfl_eq_homologyπ ι p.1 n z y₀ hy₀
  obtain ⟨y, hy⟩ := hy
  exact ⟨p, y, hy⟩

set_option maxHeartbeats 4000000 in

theorem exists_localTransition_eq_zero (n : ℕ) (p : GLevel K) (y : cohomology (localLevelRep ι p.1) n)
    (hy : (localInfl ι p.1 n).hom y = 0) :
    ∃ (q : GLevel K) (h : p ≤ q), (haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
      (localTransition K p.1 q.1 (placeOfEmbedding ι p.1) (placeOfEmbedding ι q.1) n).hom y) = 0 := by
  have hw := (ModuleCat.epi_iff_surjective
    ((cochainsComplex (localLevelRep ι p.1)).homologyπ n)).1 inferInstance y
  obtain ⟨w, rfl⟩ := hw
  have hu := exists_d_eq_of_localInfl_eq_zero ι p.1 n w hy
  obtain ⟨u, hu⟩ := hu
  have hq := exists_localCochains_eq ι _ u
  obtain ⟨q, u', hu'⟩ := hq
  have hr := GLevel.exists_ge p q
  obtain ⟨r, hpr, hqr⟩ := hr
  have : Fact (p.1 ≤ r.1) := ⟨hpr⟩
  have : Fact (q.1 ≤ r.1) := ⟨hqr⟩
  exact ⟨r, hpr, localTransition_homologyπ_eq_zero ι (M := q.1) n w u' (by rw [hu', hu])⟩

end

end GroundTheory.ProfCoh
