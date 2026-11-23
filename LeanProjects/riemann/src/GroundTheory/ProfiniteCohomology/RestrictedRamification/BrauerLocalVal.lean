import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerLocalDefs
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerOrd
import GroundTheory.ProfiniteCohomology.RestrictedRamification.DivisorModule
import GroundTheory.ProfiniteCohomology.RestrictedRamification.MulDistribMulActionGalUnitsFiniteSubfield
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain IntermediateField GroundTheory.Global groupCohomology

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) {v : HeightOneSpectrum (𝓞 K.1)}
  (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1)) (hv : v ∉ S)

def ordEmbMor :
    Rep.res (decompHomS (v.adicCompletion K.1) S ι) (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) ⟶
      trivRep Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1) ℤ :=
  Rep.ofHom ⟨uliftIntLinearMap (ordEmb S ι hv), fun σ => by
    ext y
    exact ordEmb_decompHomS S ι hv σ (Additive.toMul y)⟩

theorem ordEmbMor_hom_apply (y : Additive (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :
    (ordEmbMor S ι hv).hom y = ordEmb S ι hv y := rfl

section Levels

theorem exists_galois_level_finset (T : Finset ℚ̄) (hT : ∀ y ∈ T, y ∈ maxUnramifiedOutside K.1 ℚ̄ S) :
    ∃ (N : FiniteSubfield) (_ : Fact (K ≤ N)), Normal K.1 N.1 ∧
      (∀ x ∈ N.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S) ∧ ∀ y ∈ T, y ∈ N.1 := by
  let A : IntermediateField K.1 ℚ̄ := IntermediateField.adjoin K.1 (T : Set ℚ̄)
  have : FiniteDimensional K.1 A :=
    IntermediateField.finiteDimensional_adjoin fun y _ => Algebra.IsIntegral.isIntegral y
  let N' : IntermediateField K.1 ℚ̄ := IntermediateField.normalClosure K.1 A ℚ̄
  have hN'f : FiniteDimensional K.1 N' := inferInstance
  have hN'n : Normal K.1 N' := inferInstance
  have hN'le : N' ≤ maxUnramifiedOutside K.1 ℚ̄ S :=
    IntermediateField.normalClosure_le_iff_of_normal.2
      ((IntermediateField.adjoin_le_iff).2 fun y hy => hT y hy)
  have := K.2
  have hN'q : FiniteDimensional ℚ N' := Module.Finite.trans K.1 N'
  let N : FiniteSubfield := ⟨N'.restrictScalars ℚ, hN'q⟩
  have hKN : Fact (K ≤ N) := ⟨fun x hx => N'.algebraMap_mem ⟨x, hx⟩⟩
  refine ⟨N, hKN, ?_, fun x hx => hN'le hx, fun y hy => IntermediateField.le_normalClosure A
    (IntermediateField.subset_adjoin K.1 _ hy)⟩
  exact hN'n

variable (N : FiniteSubfield) [Fact (K ≤ N)] [Normal K.1 N.1]
  (hN : ∀ x ∈ N.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S)

def levelIncl : N.1 →ₐ[K.1] maxUnramifiedOutside K.1 ℚ̄ S where
  toFun x := ⟨x, hN x x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

def levelRes : galUnramifiedOutside K.1 ℚ̄ S →* Gal(N.1/K.1) :=
  decompHom K.1 (levelIncl S N hN)

theorem levelRes_apply (σ : galUnramifiedOutside K.1 ℚ̄ S) (x : N.1) :
    ((levelRes S N hN σ x : N.1) : ℚ̄) = ((σ ⟨x, hN x x.2⟩ : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) :=
  congrArg Subtype.val (decompHom_apply (Kv := K.1) (levelIncl S N hN) σ x)

theorem continuous_levelRes : Continuous (levelRes S N hN) :=
  continuous_decompHom _

theorem levelRes_surjective : Function.Surjective (levelRes S N hN) := by
  intro γ
  refine ⟨(γ.liftNormal ℚ̄).restrictNormal (maxUnramifiedOutside K.1 ℚ̄ S), ?_⟩
  rw [levelRes, decompHom_eq_iff]
  intro x
  apply Subtype.val_injective
  change ((γ x : N.1) : ℚ̄) = (((γ.liftNormal ℚ̄).restrictNormal (maxUnramifiedOutside K.1 ℚ̄ S)
    ⟨x, hN x x.2⟩ : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄)
  rw [show (((γ.liftNormal ℚ̄).restrictNormal (maxUnramifiedOutside K.1 ℚ̄ S) ⟨x, hN x x.2⟩ :
      maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) = γ.liftNormal ℚ̄ (algebraMap (maxUnramifiedOutside K.1 ℚ̄ S) ℚ̄
        ⟨x, hN x x.2⟩) from AlgEquiv.restrictNormal_commutes (γ.liftNormal ℚ̄)
          (maxUnramifiedOutside K.1 ℚ̄ S) ⟨x, hN x x.2⟩]
  exact (AlgEquiv.liftNormal_commutes γ ℚ̄ x).symm

theorem decompHom_embedLevel_eq (σ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1)) :
    decompHom (v.adicCompletion K.1) (embedLevel ι N) σ =
      levelRes S N hN (decompHomS (v.adicCompletion K.1) S ι σ) := by
  rw [decompHom_eq_iff]
  intro x
  rw [embedLevel_apply, embedLevel_apply, levelRes_apply]
  exact decompHom_apply (Kv := v.adicCompletion K.1) (ι.comp (maxUnramifiedOutside K.1 ℚ̄ S).val) σ
    ⟨x, hN x x.2⟩

end Levels

section LevelCocycle

def unitOfMem {N : FiniteSubfield} (y : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ)
    (hy : ((y : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) ∈ N.1) : N.1ˣ :=
  Units.mk0 ⟨(y : maxUnramifiedOutside K.1 ℚ̄ S), hy⟩ fun h =>
    y.ne_zero (Subtype.ext (congrArg Subtype.val h : ((y : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) =
      ((0 : N.1) : ℚ̄)))

theorem coe_unitOfMem {N : FiniteSubfield} (y : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ)
    (hy : ((y : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) ∈ N.1) :
    (((unitOfMem S y hy : N.1ˣ) : N.1) : ℚ̄) = ((y : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) :=
  rfl

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

theorem exists_level_cocycle (f : (Fin 2 → galUnramifiedOutside K.1 ℚ̄ S) →
      Additive (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) (hf : IsLocallyConstant f)
    (hcoc : ∀ u : Fin 3 → galUnramifiedOutside K.1 ℚ̄ S,
      (inhomogeneousCochains.d (galUnits.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2).hom f u = 0) :
    ∃ (N : FiniteSubfield) (_ : Fact (K ≤ N)) (_ : Normal K.1 N.1)
      (hN : ∀ x ∈ N.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
      (c : Gal(N.1/K.1) × Gal(N.1/K.1) → N.1ˣ), IsMulCocycle₂ c ∧
      ∀ u : Fin 2 → galUnramifiedOutside K.1 ℚ̄ S,
        (((f u).toMul : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) =
          ((c (levelRes S N hN (u 0), levelRes S N hN (u 1)) : N.1) : ℚ̄) := by
  classical
  obtain ⟨hc, -, ht⟩ := galUnramifiedOutside_isProfinite (F := K.1) (Ω := ℚ̄) S
  obtain ⟨U, hU⟩ := exists_openNormalSubgroup_fin_of_isLocallyConstant hf

  obtain ⟨E, hEf, hEU⟩ := (krullTopology_mem_nhds_one_iff K.1 (maxUnramifiedOutside K.1 ℚ̄ S)
    (U : Set (galUnramifiedOutside K.1 ℚ̄ S))).1 (U.toOpenSubgroup.isOpen.mem_nhds U.one_mem')
  let bE := Module.finBasis K.1 E

  have hfin : (Set.range f).Finite := hf.range_finite
  let T : Finset ℚ̄ := (Finset.univ.image fun i => ((bE i : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄)) ∪
    hfin.toFinset.image fun y => (((Additive.toMul y : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :
      maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄)
  have hT : ∀ y ∈ T, y ∈ maxUnramifiedOutside K.1 ℚ̄ S := by
    intro y hy
    rcases Finset.mem_union.1 hy with h | h
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 h
      exact (bE i : maxUnramifiedOutside K.1 ℚ̄ S).2
    · obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 h
      exact ((Additive.toMul z : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S).2
  obtain ⟨N, hKN, hNn, hN, hTN⟩ := exists_galois_level_finset S T hT

  have hres : ∀ σ σ' : galUnramifiedOutside K.1 ℚ̄ S, levelRes S N hN σ = levelRes S N hN σ' →
      σ⁻¹ * σ' ∈ U := by
    intro σ σ' h
    apply hEU
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hb : ∀ i, σ' (bE i : maxUnramifiedOutside K.1 ℚ̄ S) = σ (bE i : maxUnramifiedOutside K.1 ℚ̄ S) := by
      intro i
      have hmem : ((bE i : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) ∈ N.1 :=
        hTN _ (Finset.mem_union_left _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩))
      have e := congrArg (fun τ : Gal(N.1/K.1) => ((τ ⟨_, hmem⟩ : N.1) : ℚ̄)) h
      simp only [levelRes_apply] at e
      exact Subtype.ext e.symm
    have hsum : x = ∑ i, (bE.repr ⟨x, hx⟩ i) • (bE i : maxUnramifiedOutside K.1 ℚ̄ S) := by
      have := congrArg (fun e : E => (e : maxUnramifiedOutside K.1 ℚ̄ S)) (bE.sum_repr ⟨x, hx⟩)
      simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at this
      exact this.symm
    have h1 : σ' x = σ x := by
      rw [hsum, map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hs : ∀ (τ : galUnramifiedOutside K.1 ℚ̄ S) (r : K.1) (y : maxUnramifiedOutside K.1 ℚ̄ S),
          τ (r • y) = r • τ y := fun τ r y => τ.toLinearEquiv.map_smul r y
      rw [hs, hs, hb i]
    rw [AlgEquiv.mul_apply, h1]
    exact σ.symm_apply_apply x
  have hfac : ∀ u u' : Fin 2 → galUnramifiedOutside K.1 ℚ̄ S,
      (∀ i, levelRes S N hN (u i) = levelRes S N hN (u' i)) → f u = f u' :=
    fun u u' h => hU u u' fun i => hres _ _ (h i)
  have hval : ∀ u, (((f u).toMul : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S).1 ∈ N.1 :=
    fun u => hTN _ (Finset.mem_union_right _ (Finset.mem_image.2 ⟨f u, hfin.mem_toFinset.2 ⟨u, rfl⟩, rfl⟩))
  choose lift hlift using levelRes_surjective S N hN
  let c : Gal(N.1/K.1) × Gal(N.1/K.1) → N.1ˣ := fun p =>
    unitOfMem S (f ![lift p.1, lift p.2]).toMul (hval _)
  have hc_val : ∀ p, ((c p : N.1) : ℚ̄) =
      (((f ![lift p.1, lift p.2]).toMul : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S).1 :=
    fun p => rfl
  have hf2 : ∀ a b : galUnramifiedOutside K.1 ℚ̄ S,
      f ![a, b] = f ![lift (levelRes S N hN a), lift (levelRes S N hN b)] := by
    intro a b
    refine hfac _ _ fun i => ?_
    fin_cases i
    · exact (hlift _).symm
    · exact (hlift _).symm
  have hc_spec : ∀ u : Fin 2 → galUnramifiedOutside K.1 ℚ̄ S,
      (((f u).toMul : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S).1 =
        ((c (levelRes S N hN (u 0), levelRes S N hN (u 1)) : N.1) : ℚ̄) := by
    intro u
    have hu : u = ![u 0, u 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hc_val, hu, hf2]
    rfl
  refine ⟨N, hKN, hNn, hN, c, ?_, hc_spec⟩
  intro g h j
  have hd := hcoc ![lift g, lift h, lift j]
  rw [inhomogeneousCochains_d_two_apply'] at hd
  have e1 : f ![(![lift g, lift h, lift j] : Fin 3 → galUnramifiedOutside K.1 ℚ̄ S) 0 *
      (![lift g, lift h, lift j] : Fin 3 → galUnramifiedOutside K.1 ℚ̄ S) 1,
      (![lift g, lift h, lift j] : Fin 3 → galUnramifiedOutside K.1 ℚ̄ S) 2] =
      f ![lift (g * h), lift j] := by
    refine hfac _ _ fun i => ?_
    fin_cases i
    · change levelRes S N hN (lift g * lift h) = levelRes S N hN (lift (g * h))
      rw [map_mul, hlift, hlift, hlift]
    · rfl
  have e2 : f ![(![lift g, lift h, lift j] : Fin 3 → galUnramifiedOutside K.1 ℚ̄ S) 0,
      (![lift g, lift h, lift j] : Fin 3 → galUnramifiedOutside K.1 ℚ̄ S) 1 *
      (![lift g, lift h, lift j] : Fin 3 → galUnramifiedOutside K.1 ℚ̄ S) 2] =
      f ![lift g, lift (h * j)] := by
    refine hfac _ _ fun i => ?_
    fin_cases i
    · rfl
    · change levelRes S N hN (lift h * lift j) = levelRes S N hN (lift (h * j))
      rw [map_mul, hlift, hlift, hlift]
  rw [e1, e2] at hd
  have key : (galUnits.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S)).ρ (lift g) (f ![lift h, lift j]) +
      f ![lift g, lift (h * j)] = f ![lift (g * h), lift j] + f ![lift g, lift h] := by
    rw [← sub_eq_zero, ← hd]
    change _ = (galUnits.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S)).ρ (lift g) (f ![lift h, lift j]) -
      f ![lift (g * h), lift j] + f ![lift g, lift (h * j)] - f ![lift g, lift h]
    abel
  have key' := congrArg (fun y : Additive (maxUnramifiedOutside K.1 ℚ̄ S)ˣ =>
    (((Additive.toMul y : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄)) key
  simp only [toMul_add, Units.val_mul, IntermediateField.coe_mul] at key'
  apply Units.ext
  apply Subtype.ext
  simp only [Units.val_mul, IntermediateField.coe_mul]
  rw [hc_val, hc_val, hc_val]
  have hg : (((g • c (h, j) : N.1ˣ) : N.1) : ℚ̄) = (((Additive.toMul
      ((galUnits.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S)).ρ (lift g) (f ![lift h, lift j])) :
        (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) := by
    have e : (((g • c (h, j) : N.1ˣ) : N.1) : ℚ̄) =
        ((levelRes S N hN (lift g) (c (h, j) : N.1) : N.1) : ℚ̄) := by
      rw [hlift g]
      rfl
    rw [e, levelRes_apply]
    rfl
  rw [hg]
  exact key'.symm

end LevelCocycle

theorem ordEmb_eq_ordPlace (N : FiniteSubfield) [Fact (K ≤ N)]
    (hN : ∀ x ∈ N.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S) (y : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ)
    (u : N.1ˣ) (hyu : ((y : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) = ((u : N.1) : ℚ̄)) :
    ordEmb S ι hv (Additive.ofMul y) = ordPlace ι N u := by
  have hy : ((maxUnitsToUnits S y : ℚ̄ˣ) : ℚ̄) ∈ N.1 := by
    change ((y : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) ∈ N.1
    rw [hyu]
    exact (u : N.1).2
  have hv' := valuation_placeOfEmbedding_eq S ι hv N hN (maxUnitsToUnits S y) hy
  have hu : (u : N.1) = ⟨(maxUnitsToUnits S y : ℚ̄), hy⟩ := Subtype.ext hyu.symm
  rw [ordEmb_apply, ordPlace, hu, hv', WithZero.log_exp, neg_neg]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

theorem coboundary_iff_of_level (N : FiniteSubfield) [Fact (K ≤ N)] [Normal K.1 N.1]
    (he : (placeOfEmbedding ι N).1.asIdeal.ramificationIdx (𝓞 K.1) = 1)
    (c : Gal(N.1/K.1) × Gal(N.1/K.1) → N.1ˣ) (hc : IsMulCocycle₂ c)
    (a : (Fin 2 → Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1)) →
      Additive (AlgebraicClosure (v.adicCompletion K.1))ˣ)
    (o : (Fin 2 → Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1)) → ℤ)
    (ha : ∀ u, ((Additive.toMul (a u) : (AlgebraicClosure (v.adicCompletion K.1))ˣ) :
      AlgebraicClosure (v.adicCompletion K.1)) =
        ((Units.map (embedLevel ι N).toRingHom.toMonoidHom (c (decompHom (v.adicCompletion K.1)
          (embedLevel ι N) (u 0), decompHom (v.adicCompletion K.1) (embedLevel ι N) (u 1))) :
            (AlgebraicClosure (v.adicCompletion K.1))ˣ) : AlgebraicClosure (v.adicCompletion K.1)))
    (ho : ∀ u, o u = ordPlace ι N (c (decompHom (v.adicCompletion K.1) (embedLevel ι N) (u 0),
      decompHom (v.adicCompletion K.1) (embedLevel ι N) (u 1)))) :
    (∃ w : (Fin 1 → Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1)) →
        Additive (AlgebraicClosure (v.adicCompletion K.1))ˣ, IsLocallyConstant w ∧
      ∀ u, a u = (galUnitsZ (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))).ρ (u 0)
        (w fun _ => u 1) - w (fun _ => u 0 * u 1) + w (fun _ => u 0)) ↔
    (∃ w : (Fin 1 → Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1)) → ℤ,
      IsLocallyConstant w ∧
      ∀ u, o u = (trivRep Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1) ℤ).ρ (u 0)
        (w fun _ => u 1) - w (fun _ => u 0 * u 1) + w (fun _ => u 0)) := by
  have hconst : ∀ {X : Type} (w : (Fin 1 → Gal(AlgebraicClosure (v.adicCompletion K.1)/
      v.adicCompletion K.1)) → X), IsLocallyConstant w →
      IsLocallyConstant (fun σ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1) =>
        w fun _ => σ) :=
    fun w hw => hw.comp_continuous (continuous_pi fun _ => continuous_id)
  constructor
  · rintro ⟨w, hw, hwz⟩
    have hbc : ∀ σ τ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1),
        σ • Additive.toMul (w fun _ => τ) / Additive.toMul (w fun _ => σ * τ) *
          Additive.toMul (w fun _ => σ) =
        Units.map (embedLevel ι N).toRingHom.toMonoidHom
          (c (decompHom (v.adicCompletion K.1) (embedLevel ι N) σ,
            decompHom (v.adicCompletion K.1) (embedLevel ι N) τ)) := by
      intro σ τ
      have h1 : a ![σ, τ] = (galUnitsZ (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))).ρ σ
          (w fun _ => τ) - w (fun _ => σ * τ) + w (fun _ => σ) := hwz ![σ, τ]
      have h2 : Additive.toMul (a ![σ, τ]) = σ • Additive.toMul (w fun _ => τ) /
          Additive.toMul (w fun _ => σ * τ) * Additive.toMul (w fun _ => σ) :=
        (congrArg Additive.toMul h1).trans (toMul_galUnitsZ_coboundary σ _ _ _)
      apply Units.ext
      exact (congrArg Units.val h2.symm).trans (ha ![σ, τ])
    obtain ⟨h, hh, hhc⟩ := exists_ord_coboundary_of_mulCoboundary ι N c hc
      (fun σ => Additive.toMul (w fun _ => σ)) ((hconst w hw).comp Additive.toMul) hbc
    refine ⟨fun g => h (g 0), hh.comp_continuous (continuous_apply 0), fun u => ?_⟩
    rw [ho u, ← hhc (u 0) (u 1)]
    rfl
  · rintro ⟨w, hw, hwz⟩
    have hhc : ∀ σ τ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1),
        (w fun _ => τ) - (w fun _ => σ * τ) + (w fun _ => σ) =
        ordPlace ι N (c (decompHom (v.adicCompletion K.1) (embedLevel ι N) σ,
          decompHom (v.adicCompletion K.1) (embedLevel ι N) τ)) := by
      intro σ τ
      have h1 : o ![σ, τ] = (w fun _ => τ) - (w fun _ => σ * τ) + (w fun _ => σ) := hwz ![σ, τ]
      exact h1.symm.trans (ho ![σ, τ])
    obtain ⟨b, hb, hbc⟩ := exists_mulCoboundary_of_ord ι N he c hc (fun σ => w fun _ => σ)
      (hconst w hw) hhc
    refine ⟨fun g => Additive.ofMul (b (g 0)),
      (hb.comp_continuous (continuous_apply 0)).comp Additive.ofMul, fun u => ?_⟩
    apply Additive.toMul.injective
    apply Units.ext
    rw [ha u, ← hbc (u 0) (u 1)]
    rfl

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

theorem gsLocalRes_eq_zero_iff (x : cohomology (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2) :
    (gsLocalRes S ι 2).hom (cohomologyULiftIntAddEquiv _ 2 x) = 0 ↔
      (cohomologyMapAlong (decompHomS (v.adicCompletion K.1) S ι)
        (continuous_decompHomS (Kv := v.adicCompletion K.1) S ι) (ordEmbMor S ι hv) 2).hom x = 0 := by
  obtain ⟨z, rfl⟩ := cohomologyπ_surjective _ 2 x
  have hf : IsLocallyConstant (cochainOf _ (cocycleι _ 2 z)) := isLocallyConstant_cochainOf _
  have hcoc : ∀ u, (inhomogeneousCochains.d (galUnits.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2).hom
      (cochainOf _ (cocycleι _ 2 z)) u = 0 := fun u => congrFun (d_cocycleι z) u
  obtain ⟨N, hKN, hNn, hN, c, hc, hcf⟩ := exists_level_cocycle S _ hf hcoc
  have hU : Algebra.IsUnramifiedAt (𝓞 K.1) (placeOfEmbedding ι N).1.asIdeal :=
    isUnramifiedIn_of_subset_max S hv N hN _ inferInstance (placeOfEmbedding ι N).2
  have he : (placeOfEmbedding ι N).1.asIdeal.ramificationIdx (𝓞 K.1) = 1 :=
    Ideal.ramificationIdx_eq_one _ _

  have hA : (gsLocalRes S ι 2).hom (cohomologyULiftIntAddEquiv _ 2 (cohomologyπ _ 2 z)) =
      cohomologyπ _ 2 (cocyclesMapAlong (decompHomS (v.adicCompletion K.1) S ι)
        (continuous_decompHomS (Kv := v.adicCompletion K.1) S ι) (embUnitsMorZ S ι) 2
        (cocyclesULiftInt _ z)) := by
    rw [cohomologyULiftIntAddEquiv_cohomologyπ', gsLocalRes]
    exact cohomologyMapAlong_cohomologyπ _ _ _ _
  rw [hA, cohomologyMapAlong_cohomologyπ, cohomologyπ_two_eq_zero_iff_locallyConstant, cohomologyπ_two_eq_zero_iff_locallyConstant]
  simp only [cochainOf_cocycleι_cocyclesMapAlong, cochainOf_cocycleι_cocyclesULiftInt]

  have hF : ∀ u : Fin 2 → Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1),
      (((Additive.toMul (cochainOf (galUnits.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) (cocycleι _ 2 z) (⇑(decompHomS (v.adicCompletion K.1) S ι) ∘ u)) :
        (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) =
        ((c (decompHom (v.adicCompletion K.1) (embedLevel ι N) (u 0),
          decompHom (v.adicCompletion K.1) (embedLevel ι N) (u 1)) : N.1) : ℚ̄) := by
    intro u
    rw [hcf, decompHom_embedLevel_eq S ι N hN, decompHom_embedLevel_eq S ι N hN]
    rfl
  have hord : ∀ u : Fin 2 → Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1),
      (ordEmbMor S ι hv).hom (cochainOf (galUnits.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) (cocycleι _ 2 z) (⇑(decompHomS (v.adicCompletion K.1) S ι) ∘ u)) =
        ordPlace ι N (c (decompHom (v.adicCompletion K.1) (embedLevel ι N) (u 0),
          decompHom (v.adicCompletion K.1) (embedLevel ι N) (u 1))) :=
    fun u => (ordEmbMor_hom_apply S ι hv _).trans (ordEmb_eq_ordPlace S ι hv N hN _ _ (hF u))
  have hemb : ∀ u : Fin 2 → Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1),
      ((Additive.toMul ((embUnitsMorZ S ι).hom (cochainOf (galUnits.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) (cocycleι _ 2 z)
        (⇑(decompHomS (v.adicCompletion K.1) S ι) ∘ u))) : (AlgebraicClosure (v.adicCompletion K.1))ˣ) :
          AlgebraicClosure (v.adicCompletion K.1)) =
        ((Units.map (embedLevel ι N).toRingHom.toMonoidHom (c (decompHom (v.adicCompletion K.1)
          (embedLevel ι N) (u 0), decompHom (v.adicCompletion K.1) (embedLevel ι N) (u 1))) :
            (AlgebraicClosure (v.adicCompletion K.1))ˣ) : AlgebraicClosure (v.adicCompletion K.1)) := by
    intro u
    rw [embUnitsMorZ_hom_apply]
    change ι _ = ι _
    exact congrArg ι (hF u)
  exact coboundary_iff_of_level ι N he c hc _ _ hemb hord

end

end GroundTheory.ProfCoh
