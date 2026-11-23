import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.EqZeroOfBrauerLocalApplyEqZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield}

section Level

variable {F : FiniteSubfield} [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal]

variable (K F) in

def unitsLevelMor :
    Rep.res (restrictHom (F := K) (E := F)) (galUnitsZ K.1 F.1) ⟶ unitsLimitRep K :=
  Rep.ofHom ⟨(MonoidHom.toAdditive (IdeleLimit.unitsIncl F)).toIntLinearMap, fun _ => LinearMap.ext fun _ =>
    congrArg Additive.ofMul (Units.ext rfl)⟩

@[simp]
theorem unitsLevelMor_hom_apply (x : Additive F.1ˣ) :
    (unitsLevelMor K F).hom x = Additive.ofMul (IdeleLimit.unitsIncl F x.toMul) :=
  rfl

variable (K F) in

def unitsLevelInfl (n : ℕ) : cohomology (galUnitsZ K.1 F.1) n ⟶ cohomology (unitsLimitRep K) n :=
  cohomologyMapAlong restrictHom continuous_restrictHom (unitsLevelMor K F) n

variable (K F) in

def levelDiag : galUnitsZ K.1 F.1 ⟶ ideleRep K.1 F.1 :=
  Rep.ofHom ⟨(MonoidHom.toAdditive (IdeleGroup.diagonal F.1)).toIntLinearMap, fun σ => LinearMap.ext fun x =>
    congrArg Additive.ofMul ((congrArg (IdeleGroup.diagonal F.1) (Units.ext rfl)).trans
      (smul_diagonal σ x.toMul).symm)⟩

omit [F.1.fixingSubgroup.Normal] in
@[simp]
theorem levelDiag_hom_apply (x : Additive F.1ˣ) :
    (levelDiag K F).hom x = Additive.ofMul (IdeleGroup.diagonal F.1 x.toMul) :=
  rfl

theorem levelDiag_cochains_comp :
    cochainsMap (levelDiag K F) ≫ cochainsMapAlong restrictHom continuous_restrictHom (levelMor K F) =
      cochainsMapAlong restrictHom continuous_restrictHom (unitsLevelMor K F) ≫
        cochainsMap (idelesShortComplexRes K).f := by
  have key : ∀ u : Additive F.1ˣ, (levelMor K F).hom ((levelDiag K F).hom u) =
      (idelesShortComplexRes K).f.hom ((unitsLevelMor K F).hom u) := fun u =>
    congrArg Additive.ofMul (IdeleLimit.diag_unitsIncl F u.toMul).symm
  ext n x : 3
  apply Subtype.ext
  funext g
  exact key _

theorem unitsToIdeles_unitsLevelInfl (n : ℕ) (y : cohomology (galUnitsZ K.1 F.1) n) :
    (unitsToIdeles K n).hom ((unitsLevelInfl K F n).hom y) =
      (levelInfl K F n).hom ((cohomologyMap (levelDiag K F) n).hom y) := by
  have h2 : cohomologyMap (levelDiag K F) n ≫ levelInfl K F n = unitsLevelInfl K F n ≫ unitsToIdeles K n := by
    have e1 : cohomologyMap (levelDiag K F) n ≫ levelInfl K F n = HomologicalComplex.homologyMap
        (cochainsMap (levelDiag K F) ≫ cochainsMapAlong restrictHom continuous_restrictHom (levelMor K F)) n :=
      (HomologicalComplex.homologyMap_comp _ _ n).symm
    have e2 : unitsLevelInfl K F n ≫ unitsToIdeles K n = HomologicalComplex.homologyMap
        (cochainsMapAlong restrictHom continuous_restrictHom (unitsLevelMor K F) ≫
          cochainsMap (idelesShortComplexRes K).f) n :=
      (HomologicalComplex.homologyMap_comp _ _ n).symm
    rw [e1, e2, levelDiag_cochains_comp]
    rfl
  exact (congrArg (fun φ => φ.hom y) h2).symm

end Level

section Colimit

abbrev unitsLevelCochainsInfl (p : GLevel K) :
    cochainsComplex (galUnitsZ K.1 p.1.1) ⟶ cochainsComplex (unitsLimitRep K) :=
  cochainsMapAlong restrictHom continuous_restrictHom (unitsLevelMor K p.1)

theorem unitsLevelCochains_injective (p : GLevel K) (m : ℕ) :
    Function.Injective ((unitsLevelCochainsInfl p).f m).hom := by
  intro y y' h
  apply (ModuleCat.mono_iff_injective ((cochainsComplexι (galUnitsZ K.1 p.1.1)).f m)).1 inferInstance
  funext τ
  let σ : Fin m → K.1.fixingSubgroup := fun i =>
    Function.surjInv (restrictHom_surjective (F := K) (E := p.1)) (τ i)
  have hσ : (fun i => restrictHom (E := p.1) (σ i)) = τ :=
    funext fun i => Function.surjInv_eq (restrictHom_surjective (F := K) (E := p.1)) (τ i)
  have h1 := congrFun (congrArg (fun c => ((cochainsComplexι (unitsLimitRep K)).f m).hom c) h) σ
  simp only at h1
  change Additive.ofMul (IdeleLimit.unitsIncl p.1 (((cochainsComplexι _).f m).hom y
      (fun i => restrictHom (E := p.1) (σ i))).toMul) =
    Additive.ofMul (IdeleLimit.unitsIncl p.1 (((cochainsComplexι _).f m).hom y'
      (fun i => restrictHom (E := p.1) (σ i))).toMul) at h1
  rw [hσ] at h1
  exact congrArg Additive.ofMul (IdeleLimit.unitsIncl_injective p.1 (congrArg Additive.toMul h1))

theorem exists_unitsLevelCochains_eq (m : ℕ) (x : (cochainsComplex (unitsLimitRep K)).X m) :
    ∃ (p : GLevel K) (y : (cochainsComplex (galUnitsZ K.1 p.1.1)).X m),
      ((unitsLevelCochainsInfl p).f m).hom y = x := by
  classical
  have hx : IsLocallyConstant (((cochainsComplexι (unitsLimitRep K)).f m).hom x :
      (Fin m → K.1.fixingSubgroup) → unitsLimitRep K) :=
    (show locallyConstantCochains (unitsLimitRep K) m from x).2
  set f := ((cochainsComplexι (unitsLimitRep K)).f m).hom x with hf
  obtain ⟨U, hU⟩ := exists_openNormalSubgroup_fin_of_isLocallyConstant hx
  obtain ⟨t, ht, htU⟩ := isOpen_induced_iff.1 U.isOpen
  have h1t : (1 : ℚ̄ ≃ₐ[ℚ] ℚ̄) ∈ t := by
    have : (1 : K.1.fixingSubgroup) ∈ Subtype.val ⁻¹' t := by
      rw [htU]
      exact U.one_mem
    exact this
  obtain ⟨E₀, hE₀fin, hE₀⟩ := (krullTopology_mem_nhds_one_iff ℚ ℚ̄ t).1 (ht.mem_nhds h1t)
  have hfin : (Set.range f).Finite := hx.range_finite
  choose idx x' hx' using fun a : unitsLimitRep K => IdeleLimit.exists_unitsIncl (Additive.toMul a)
  choose lev hlev using fun E : FiniteSubfield => GLevel.exists_le (K := K) E
  obtain ⟨p, hp⟩ := Finset.exists_le ((hfin.toFinset.image fun a => lev (idx a)) ∪
    {lev ⟨E₀, hE₀fin⟩})
  have hpE₀ : E₀ ≤ p.1.1 := (hlev ⟨E₀, hE₀fin⟩).trans
    (hp _ (Finset.mem_union_right _ (Finset.mem_singleton_self _)))
  have hker : ∀ g : K.1.fixingSubgroup, restrictHom (E := p.1) g = 1 → g ∈ U := by
    intro g hg
    have hg' : g ∈ p.1.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup := by
      rw [← ker_restrictHom, MonoidHom.mem_ker]
      exact hg
    rw [Subgroup.mem_subgroupOf] at hg'
    have : g ∈ Subtype.val ⁻¹' t := hE₀ (IntermediateField.fixingSubgroup_le hpE₀ hg')
    rw [htU] at this
    exact this
  have hval : ∀ g, ∃ z : p.1.1ˣ, IdeleLimit.unitsIncl p.1 z = Additive.toMul (f g) := by
    intro g
    have hmem : f g ∈ hfin.toFinset := by simp
    have hle : idx (f g) ≤ p.1 := (hlev (idx (f g))).trans
      (hp _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hmem)))
    let := algebraOfLE hle
    refine ⟨Units.map (algebraMap (idx (f g)).1 p.1.1 : (idx (f g)).1 →* p.1.1) (x' (f g)), ?_⟩
    exact (Units.ext rfl : IdeleLimit.unitsIncl p.1 _ = IdeleLimit.unitsIncl (idx (f g)) (x' (f g))).trans
      (hx' (f g))
  choose z hz using hval
  let lift : (Fin m → (p.1.1 ≃ₐ[K.1] p.1.1)) → Fin m → K.1.fixingSubgroup := fun τ i =>
    Function.surjInv (restrictHom_surjective (F := K) (E := p.1)) (τ i)
  refine ⟨p, ⟨fun τ => Additive.ofMul (z (lift τ)), IsLocallyConstant.of_discrete _⟩, ?_⟩
  apply (ModuleCat.mono_iff_injective ((cochainsComplexι (unitsLimitRep K)).f m)).1 inferInstance
  funext g
  change Additive.ofMul (IdeleLimit.unitsIncl p.1 (z (lift fun i => restrictHom (E := p.1) (g i)))) = f g
  rw [hz]
  refine hU _ _ fun i => hker _ ?_
  rw [map_mul, map_inv, Function.surjInv_eq (restrictHom_surjective (F := K) (E := p.1)),
    inv_mul_cancel]

theorem exists_unitsLevelInfl_eq (n : ℕ) (x : cohomology (unitsLimitRep K) n) :
    ∃ (p : GLevel K) (y : cohomology (galUnitsZ K.1 p.1.1) n), (unitsLevelInfl K p.1 n).hom y = x := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((cochainsComplex (unitsLimitRep K)).homologyπ n)).1 inferInstance x
  obtain ⟨p, y₀, hy₀⟩ := exists_unitsLevelCochains_eq n
    (((cochainsComplex (unitsLimitRep K)).iCycles n).hom z)
  have hd : ((cochainsComplex (galUnitsZ K.1 p.1.1)).d n (n + 1)).hom y₀ = 0 := by
    apply unitsLevelCochains_injective p (n + 1)
    rw [map_zero, hom_f_d_apply, hy₀]
    exact iCycles_d_apply _ n (n + 1) z
  obtain ⟨w, hw⟩ := exists_iCycles_eq_of_d_eq_zero _ n y₀ hd
  refine ⟨p, ((cochainsComplex (galUnitsZ K.1 p.1.1)).homologyπ n).hom w, ?_⟩
  refine (homologyMap_homologyπ_apply (unitsLevelCochainsInfl p) n w).trans (congrArg _ ?_)
  apply (ModuleCat.mono_iff_injective ((cochainsComplex (unitsLimitRep K)).iCycles n)).1 inferInstance
  rw [iCycles_cyclesMap_apply, hw, hy₀]

end Colimit

end

end GroundTheory.ProfCoh
