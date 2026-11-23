import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.MemMaxUnramifiedOutsideOfMemLevelOfField
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

namespace PicInf

open CategoryTheory NumberField IsDedekindDomain IntermediateField GroundTheory.Global GroundTheory.Global.SemiLocal
  FiniteSubfield

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} {S : Set (HeightOneSpectrum (𝓞 K.1))}

variable (L : IntermediateField K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) [FiniteDimensional K.1 L]

omit [FiniteDimensional K.1 L] in

theorem ordEmb_galUnitsHom_eq {v : HeightOneSpectrum (𝓞 K.1)}
    (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1)) (hv : v ∉ S)
    (x : galUnramifiedOutside K.1 ℚ̄ S) (x' : ℚ̄ →ₐ[K.1] ℚ̄)
    (hx' : ∀ z : maxUnramifiedOutside K.1 ℚ̄ S, x' z = ((x z : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄))
    (y : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :
    ordEmb S ι hv (Additive.ofMul (galUnitsHom K.1 _ x y)) = ordEmbFun (ι.comp x') (maxUnitsToUnits S y) := by
  obtain ⟨N, hKN, hgal, hNS, hyN⟩ := exists_galois_level S (y : maxUnramifiedOutside K.1 ℚ̄ S).2
  have := hKN
  have : Normal K.1 N.1 := hgal.to_normal
  let gN : N.1 ≃ₐ[K.1] N.1 := x'.restrictNormal' N.1
  have hgN : ∀ z : N.1, ((gN z : N.1) : ℚ̄) = x' z := fun z => AlgHom.restrictNormal_commutes x' N.1 z
  have hw := placeOfEmbedding_eq_inv_smul ι gN (ι.comp x') fun z => by
    rw [AlgHom.comp_apply, hgN]
  have hmem : ((maxUnitsToUnits S (galUnitsHom K.1 _ x y) : ℚ̄ˣ) : ℚ̄) ∈ N.1 := by
    change ((x (y : maxUnramifiedOutside K.1 ℚ̄ S) : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) ∈ N.1
    rw [← hx', ← hgN ⟨_, hyN⟩]
    exact (gN _).2
  have e1 := valuation_placeOfEmbedding_eq S ι hv N hNS _ hmem
  have e2 := valuation_placeOfEmbedding_eq S (ι.comp x') hv N hNS (maxUnitsToUnits S y) hyN
  rw [hw, valuation_inv_smul_placesOver] at e2
  have key : (placeOfEmbedding ι N).1.valuation N.1 ⟨_, hmem⟩ =
      (placeOfEmbedding ι N).1.valuation N.1 (gN ⟨_, hyN⟩) := by
    congr 1
    apply Subtype.ext
    change ((x (y : maxUnramifiedOutside K.1 ℚ̄ S) : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) =
      ((gN ⟨_, hyN⟩ : N.1) : ℚ̄)
    rw [hgN, hx']
  have := WithZero.exp_injective (e1.symm.trans (key.trans e2))
  rw [ordEmb_apply]
  omega

omit [FiniteDimensional K.1 L] in

theorem placeOfEmbedding_congr_of_eqOn {v : HeightOneSpectrum (𝓞 K.1)} (F : FiniteSubfield) [Fact (K ≤ F)]
    (ι₁ ι₂ : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1)) (h : ∀ z : F.1, ι₁ z = ι₂ z) :
    placeOfEmbedding ι₁ F = placeOfEmbedding ι₂ F :=
  (eq_placeOfEmbedding ι₁ F (completionEmbedding ι₂ F) fun z => by
    rw [completionEmbedding_algebraMap]
    exact (h z).symm).symm

omit [FiniteDimensional K.1 L] in

theorem exists_algEquiv_of_placeOfEmbedding_eq {v : HeightOneSpectrum (𝓞 K.1)} (F : FiniteSubfield)
    [Fact (K ≤ F)] (ι₁ ι₂ : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1))
    (h : placeOfEmbedding ι₁ F = placeOfEmbedding ι₂ F) :
    ∃ σ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1),
      ∀ z : F.1, ι₁ z = σ (ι₂ z) := by
  have key : ∀ w : PlacesOver F.1 v, w = placeOfEmbedding ι₁ F →
      ∃ c : w.1.adicCompletion F.1 →ₐ[v.adicCompletion K.1] AlgebraicClosure (v.adicCompletion K.1),
        ∀ z : F.1, c (algebraMap F.1 _ z) = ι₁ z := by
    rintro w rfl
    exact ⟨completionEmbedding ι₁ F, completionEmbedding_algebraMap ι₁ F⟩
  obtain ⟨c₁, hc₁⟩ := key (placeOfEmbedding ι₂ F) h.symm
  have := finiteDimensional_adicCompletion_placesOver (K := K) (E := F) (placeOfEmbedding ι₂ F)
  let c₂ := completionEmbedding ι₂ F
  let : Algebra ((placeOfEmbedding ι₂ F).1.adicCompletion F.1)
      (AlgebraicClosure (v.adicCompletion K.1)) := c₂.toRingHom.toAlgebra
  have : IsScalarTower (v.adicCompletion K.1) ((placeOfEmbedding ι₂ F).1.adicCompletion F.1)
      (AlgebraicClosure (v.adicCompletion K.1)) :=
    IsScalarTower.of_algebraMap_eq fun a => (c₂.commutes a).symm
  have : Algebra.IsAlgebraic ((placeOfEmbedding ι₂ F).1.adicCompletion F.1)
      (AlgebraicClosure (v.adicCompletion K.1)) :=
    Algebra.IsAlgebraic.tower_top (K := v.adicCompletion K.1) _
  obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := v.adicCompletion K.1)
    (L := (placeOfEmbedding ι₂ F).1.adicCompletion F.1) (M := AlgebraicClosure (v.adicCompletion K.1))
    (E := AlgebraicClosure (v.adicCompletion K.1)) c₁
  refine ⟨AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ), fun z => ?_⟩
  rw [AlgEquiv.ofBijective_apply]
  have e := DFunLike.congr_fun hφ (algebraMap F.1 _ z)
  change φ (c₂ (algebraMap F.1 _ z)) = c₁ (algebraMap F.1 _ z) at e
  rw [← hc₁, ← e, completionEmbedding_algebraMap]

theorem placeOfEmbedding_comp_eq_iff [Normal K.1 L] (ιs : LocalEmbeddings K)
    (v v' : HeightOneSpectrum (𝓞 K.1)) (x : galUnramifiedOutside K.1 ℚ̄ S) (x' : ℚ̄ →ₐ[K.1] ℚ̄)
    (hx' : ∀ z : maxUnramifiedOutside K.1 ℚ̄ S, x' z = ((x z : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄)) :
    (placeOfEmbedding ((ιs.fin v').comp x') (levelOfField L)).1 =
        (placeOfEmbedding (ιs.fin v) (levelOfField L)).1 ↔
      v' = v ∧ ∃ z ∈ (decompHomS (v.adicCompletion K.1) S (ιs.fin v)).range,
        ∃ u ∈ L.fixingSubgroup, x = z * u := by
  constructor
  · intro h
    have hvv : v' = v := by
      have h1 := (placeOfEmbedding ((ιs.fin v').comp x') (levelOfField L)).2
      have h2 := (placeOfEmbedding (ιs.fin v) (levelOfField L)).2
      rw [h] at h1
      exact HeightOneSpectrum.ext (h1.over.trans h2.over.symm)
    subst hvv
    refine ⟨rfl, ?_⟩
    obtain ⟨σ, hσ⟩ := exists_algEquiv_of_placeOfEmbedding_eq (levelOfField L) ((ιs.fin v').comp x')
      (ιs.fin v') (Subtype.ext h)
    refine ⟨decompHomS (v'.adicCompletion K.1) S (ιs.fin v') σ, ⟨σ, rfl⟩,
      (decompHomS (v'.adicCompletion K.1) S (ιs.fin v') σ)⁻¹ * x, ?_, by rw [mul_inv_cancel_left]⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro w hw
    have hxw : x w = decompHomS (v'.adicCompletion K.1) S (ιs.fin v') σ w := by
      apply Subtype.val_injective
      apply (ιs.fin v').injective
      have h1 := hσ ⟨(w : ℚ̄), (mem_levelOfField L).2 ⟨w, hw, rfl⟩⟩
      have h2 := decompHom_apply (Kv := v'.adicCompletion K.1)
        ((ιs.fin v').comp (maxUnramifiedOutside K.1 ℚ̄ S).val) σ w
      change (ιs.fin v') (x' (w : ℚ̄)) = σ ((ιs.fin v') (w : ℚ̄)) at h1
      rw [hx'] at h1
      change (ιs.fin v') ((x w : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) =
        (ιs.fin v') ((decompHomS (v'.adicCompletion K.1) S (ιs.fin v') σ w : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄)
      rw [h1]
      exact h2.symm
    rw [AlgEquiv.mul_apply, hxw, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  · rintro ⟨rfl, z, ⟨σ, rfl⟩, u, hu, rfl⟩
    refine congrArg Subtype.val ?_
    rw [← placeOfEmbedding_comp_algEquiv (ιs.fin v') σ]
    apply placeOfEmbedding_congr_of_eqOn
    rintro ⟨zz, hzz⟩
    obtain ⟨w, hw, rfl⟩ := (mem_levelOfField L).1 hzz
    change (ιs.fin v') (x' (w : ℚ̄)) = σ ((ιs.fin v') (w : ℚ̄))
    have e1 : (decompHomS (v'.adicCompletion K.1) S (ιs.fin v') σ * u) w =
        decompHomS (v'.adicCompletion K.1) S (ιs.fin v') σ (u w) :=
      AlgEquiv.mul_apply _ _ w
    have e2 : u w = w := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hu w hw
    have e3 : x' (w : ℚ̄) = ((decompHomS (v'.adicCompletion K.1) S (ιs.fin v') σ w :
        maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) :=
      (hx' w).trans (congrArg Subtype.val (e1.trans (congrArg _ e2)))
    exact (congrArg (ιs.fin v') e3).trans (decompHom_apply (Kv := v'.adicCompletion K.1)
      ((ιs.fin v').comp (maxUnramifiedOutside K.1 ℚ̄ S).val) σ w)

end

end PicInf

end GroundTheory.ProfCoh
