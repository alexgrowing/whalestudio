import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.ClassFieldGSFull
import GroundTheory.ProfiniteCohomology.RestrictedRamification.ClassFieldGSPresentation
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangePlaces
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerFrob
import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbolSep
import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbolNorm
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.SymbolBridge
import GroundTheory.ProfiniteCohomology.PoincareDuality.Torsion
import GroundTheory.GlobalFields.TateThesis.ChebotarevAbelian
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalInvariants
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain IntermediateField GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.LocalField
  GroundTheory.Global.IdeleGroup Function

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

universe u

section QZ

variable {G : Type} [Group G] [TopologicalSpace G] {n : ℕ}

def charQZ (χ : ContinuousMonoidHom G (Multiplicative (ZMod n))) : Additive G →ₜ+ QZ where
  toFun x := zmodToQZ n (Multiplicative.toAdd (χ (Additive.toMul x)))
  map_zero' := by simp
  map_add' x y := by simp [toMul_add, map_mul]
  continuous_toFun :=
    (continuous_of_discreteTopology (f := fun z : Multiplicative (ZMod n) ↦ zmodToQZ n z.toAdd)).comp
      (χ.continuous.comp continuous_toMul)

theorem charQZ_apply (χ : ContinuousMonoidHom G (Multiplicative (ZMod n))) (g : G) :
    charQZ χ (Additive.ofMul g) = zmodToQZ n (Multiplicative.toAdd (χ g)) :=
  rfl

end QZ

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω] [IsGalois K Ω]

theorem decompHom_apply_of_localArtinMap (v : HeightOneSpectrum (𝓞 K))
    (ι : Ω →ₐ[K] AlgebraicClosure (v.adicCompletion K)) (b : (v.adicCompletion K)ˣ)
    {g : Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K)}
    (hg : ∀ (y : AlgebraicClosure (v.adicCompletion K))
      (hy : y ∈ maximalAbelianExtension (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))),
      g y = (localArtinMap (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) b ⟨y, hy⟩ :
        AlgebraicClosure (v.adicCompletion K)))
    (y : Ω) (hy : y ∈ maximalAbelianExtension K Ω) :
    decompHom (v.adicCompletion K) ι g y =
      (artinMap K Ω (IdeleClassGroup.mk K (finiteEmbedding v b)) ⟨y, hy⟩ : Ω) := by
  obtain ⟨L, _, _, hyL⟩ := exists_finite_abelian_mem hy
  have := NumberField.of_module_finite K L
  let j : L →ₐ[K] AlgebraicClosure (v.adicCompletion K) := ι.comp L.val
  have e := artinMap_finiteEmbedding_apply L v (placeOfAlgHom j) (completionEmbeddingOfAlgHom j) b
    ⟨y, hyL⟩
  have hmem : ι y ∈ maximalAbelianExtension (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) := by
    have := apply_mem_maximalAbelianExtension (completionEmbeddingOfAlgHom j)
      (algebraMap L ((placeOfAlgHom j).1.adicCompletion L) ⟨y, hyL⟩)
    rwa [completionEmbeddingOfAlgHom_algebraMap] at this
  have e2 : (localArtinMap (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) b ⟨ι y, hmem⟩ :
      AlgebraicClosure (v.adicCompletion K)) =
      completionEmbeddingOfAlgHom j (algebraMap L ((placeOfAlgHom j).1.adicCompletion L)
        (restrictAb L (le_maximalAbelianExtension L)
          (artinMap K Ω (IdeleClassGroup.mk K (finiteEmbedding v b))) ⟨y, hyL⟩)) := by
    rw [e]
    exact congrArg (fun z ↦ (localArtinMap (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) b z :
      AlgebraicClosure (v.adicCompletion K)))
      (Subtype.ext (completionEmbeddingOfAlgHom_algebraMap j ⟨y, hyL⟩).symm)
  have key : ι (decompHom (v.adicCompletion K) ι g y) =
      ι (artinMap K Ω (IdeleClassGroup.mk K (finiteEmbedding v b)) ⟨y, hy⟩ : Ω) := by
    rw [decompHom_apply, hg _ hmem, e2, completionEmbeddingOfAlgHom_algebraMap]
    change ι ((restrictAb L (le_maximalAbelianExtension L)
      (artinMap K Ω (IdeleClassGroup.mk K (finiteEmbedding v b))) ⟨y, hyL⟩ : L) : Ω) = _
    rw [restrictAb_apply]
  exact ι.injective key

theorem liftNormal_localArtinMap_apply (v : HeightOneSpectrum (𝓞 K)) (b : (v.adicCompletion K)ˣ)
    (y : AlgebraicClosure (v.adicCompletion K))
    (hy : y ∈ maximalAbelianExtension (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))) :
    (localArtinMap (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) b).liftNormal
        (AlgebraicClosure (v.adicCompletion K)) y =
      (localArtinMap (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) b ⟨y, hy⟩ :
        AlgebraicClosure (v.adicCompletion K)) :=
  AlgEquiv.liftNormal_commutes (localArtinMap (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) b)
    (AlgebraicClosure (v.adicCompletion K)) ⟨y, hy⟩

variable {S : Set (HeightOneSpectrum (𝓞 K))} {n : ℕ}

theorem charToSIdelePos_finiteEmbedding
    (χ : ContinuousMonoidHom (galUnramifiedOutside K Ω S) (Multiplicative (ZMod n)))
    (v : HeightOneSpectrum (𝓞 K)) (ι : Ω →ₐ[K] AlgebraicClosure (v.adicCompletion K))
    (b : (v.adicCompletion K)ˣ) {g : Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K)}
    (hg : ∀ (y : AlgebraicClosure (v.adicCompletion K))
      (hy : y ∈ maximalAbelianExtension (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))),
      g y = (localArtinMap (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) b ⟨y, hy⟩ :
        AlgebraicClosure (v.adicCompletion K))) :
    charToSIdelePos χ (SIdeleClassGroupPos.mk S (finiteEmbedding v b)) =
      χ (decompHomS (v.adicCompletion K) S ι g) := by
  rw [charToSIdelePos_mk_eq χ _ (decompHom (v.adicCompletion K) ι g)
    (decompHom_apply_of_localArtinMap v ι b hg), decompHomS_eq]
  rfl

theorem charEquiv_finiteEmbedding [IsAlgClosure K Ω] (hS : S.Finite) [NeZero n]
    (h : Odd n ∨ IsTotallyComplex K)
    (χ : ContinuousMonoidHom (galUnramifiedOutside K Ω S) (Multiplicative (ZMod n)))
    (v : HeightOneSpectrum (𝓞 K)) (ι : Ω →ₐ[K] AlgebraicClosure (v.adicCompletion K))
    (b : (v.adicCompletion K)ˣ) {g : Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K)}
    (hg : ∀ (y : AlgebraicClosure (v.adicCompletion K))
      (hy : y ∈ maximalAbelianExtension (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))),
      g y = (localArtinMap (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) b ⟨y, hy⟩ :
        AlgebraicClosure (v.adicCompletion K))) :
    charEquiv Ω hS h χ (SIdeleClassGroup.mk S (finiteEmbedding v b)) =
      χ (decompHomS (v.adicCompletion K) S ι g) := by
  rw [charEquiv_mk_eq hS h χ _ (decompHom (v.adicCompletion K) ι g)
    (decompHom_apply_of_localArtinMap v ι b hg), decompHomS_eq]
  rfl

section Cup

variable {K : Type} [Field K] [NumberField K] {Ω : Type} [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} {n : ℕ}

theorem brauerInvZ_galCupClass_decompHomS [IsAlgClosure K Ω] (hS : S.Finite) [NeZero n]
    (h : Odd n ∨ IsTotallyComplex K)
    (χ : ContinuousMonoidHom (galUnramifiedOutside K Ω S) (Multiplicative (ZMod n)))
    (v : HeightOneSpectrum (𝓞 K)) (ι : Ω →ₐ[K] AlgebraicClosure (v.adicCompletion K))
    (a : (v.adicCompletion K)ˣ) :
    brauerInvZOfIsSepClosure (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))
        (galCupClass (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))
          (contCharComp (charQZ χ) (decompHomS (v.adicCompletion K) S ι)
            (continuous_decompHomS (Kv := v.adicCompletion K) S ι)) a) =
      zmodToQZ n (Multiplicative.toAdd (charEquiv Ω hS h χ (SIdeleClassGroup.mk S (finiteEmbedding v a)))) := by
  rw [brauerInvZOfIsSepClosure_galCupClass _ a _ (liftNormal_localArtinMap_apply v a),
    contCharComp_apply, charEquiv_finiteEmbedding hS h χ v ι a (liftNormal_localArtinMap_apply v a)]
  rfl

theorem placeInv_galCupClass_decompHomS {K : FiniteSubfield} {S : Set (HeightOneSpectrum (𝓞 K.1))}
    (hS : S.Finite) [NeZero n] (h : Odd n ∨ IsTotallyComplex K.1)
    (χ : ContinuousMonoidHom (galUnramifiedOutside K.1 ℚ̄ S) (Multiplicative (ZMod n)))
    (w : HeightOneSpectrum (𝓞 K.1)) (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (w.adicCompletion K.1))
    (a : (w.adicCompletion K.1)ˣ) :
    placeInv (K := K) (.inr w)
        (galCupClass (w.adicCompletion K.1) (AlgebraicClosure (w.adicCompletion K.1))
          (contCharComp (charQZ χ) (decompHomS (w.adicCompletion K.1) S ι)
            (continuous_decompHomS (Kv := w.adicCompletion K.1) S ι)) a) =
      zmodToQZ n (Multiplicative.toAdd (charEquiv ℚ̄ hS h χ (SIdeleClassGroup.mk S (finiteEmbedding w a)))) :=
  brauerInvZ_galCupClass_decompHomS hS h χ w ι a

end Cup

section Frobenius

theorem unramifiedDegree_liftNormal_localArtinMap_localUniformizer {K : Type} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    unramifiedDegree (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))
      ((localArtinMap (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))
        (localUniformizer v)).liftNormal (AlgebraicClosure (v.adicCompletion K))) =
      Multiplicative.ofAdd 1 := by
  have e := unramifiedDegree_of_mk_eq_localReciprocityLimit
    (mk_eq_localReciprocityLimit_of_forall (liftNormal_localArtinMap_apply v (localUniformizer v)))
  have ho : GroundTheory.LocalField.ord ((localUniformizer v : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 :=
    ord_eq_one_of_valued_eq_exp v (valued_localUniformizer v)
  refine e.trans ?_
  rw [ho, Int.cast_one]

variable {K : FiniteSubfield} {S : Set (HeightOneSpectrum (𝓞 K.1))} {n : ℕ}

theorem sPresentation_single [Finite S] (v : HeightOneSpectrum (𝓞 K.1)) (hv : v ∉ S) :
    sPresentation S (1, Multiplicative.ofAdd (Finsupp.single ⟨v, hv⟩ 1)) =
      SIdeleClassGroup.mk S (finiteEmbedding v (localUniformizer v)) := by
  rw [sPresentation_apply, map_one, one_mul, toAdd_ofAdd, divisorIdele_single, zpow_one]

set_option maxHeartbeats 4000000 in

theorem charEquiv_sPresentation_single_of (hS : S.Finite) [NeZero n] (h : Odd n ∨ IsTotallyComplex K.1)
    (χ : ContinuousMonoidHom (galUnramifiedOutside K.1 ℚ̄ S) (Multiplicative (ZMod n)))
    (v : HeightOneSpectrum (𝓞 K.1)) (hv : v ∉ S) (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1))
    (σ g : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1))
    (hσ : unramifiedDegree (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) σ =
      Multiplicative.ofAdd 1)
    (hg : ∀ (y : AlgebraicClosure (v.adicCompletion K.1))
      (hy : y ∈ maximalAbelianExtension (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))),
      g y = (localArtinMap (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) (localUniformizer v)
        ⟨y, hy⟩ : AlgebraicClosure (v.adicCompletion K.1)))
    (hdeg : unramifiedDegree (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) g =
      Multiplicative.ofAdd 1) :
    have := hS.to_subtype
    χ (decompHomS (v.adicCompletion K.1) S ι σ) =
      charEquiv ℚ̄ hS h χ (sPresentation S (1, Multiplicative.ofAdd (Finsupp.single ⟨v, hv⟩ 1))) := by
  intro _
  have h1 : unramifiedDegree (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) (σ⁻¹ * g) = 1 := by
    rw [map_mul, map_inv, hσ, hdeg, inv_mul_cancel]
  have h2 := decompHomS_eq_one_of_unramifiedDegree_eq_one S ι hv _ h1
  rw [map_mul, map_inv, inv_mul_eq_one] at h2
  rw [sPresentation_single, charEquiv_finiteEmbedding hS h χ v ι (localUniformizer v) hg, h2]

theorem charEquiv_sPresentation_single (hS : S.Finite) [NeZero n] (h : Odd n ∨ IsTotallyComplex K.1)
    (χ : ContinuousMonoidHom (galUnramifiedOutside K.1 ℚ̄ S) (Multiplicative (ZMod n)))
    (v : HeightOneSpectrum (𝓞 K.1)) (hv : v ∉ S) (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1))
    (σ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1))
    (hσ : unramifiedDegree (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) σ =
      Multiplicative.ofAdd 1) :
    have := hS.to_subtype
    χ (decompHomS (v.adicCompletion K.1) S ι σ) =
      charEquiv ℚ̄ hS h χ (sPresentation S (1, Multiplicative.ofAdd (Finsupp.single ⟨v, hv⟩ 1))) :=
  charEquiv_sPresentation_single_of hS h χ v hv ι σ _ hσ (liftNormal_localArtinMap_apply v _)
    (unramifiedDegree_liftNormal_localArtinMap_localUniformizer v)

end Frobenius

end

end GroundTheory.ProfCoh
