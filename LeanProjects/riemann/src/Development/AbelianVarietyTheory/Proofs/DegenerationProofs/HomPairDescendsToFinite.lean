import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsMonHomIffOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.HomPairDescent

open GlobalTheory.Spread

theorem id_pow_left_comm {S S' : Scheme.{0}} {j : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G j φ) (m : ℕ) :
    (𝟙 G' ^ m : G' ⟶ G').left ≫ φ = φ ≫ (𝟙 G ^ m : G ⟶ G).left := by
  have e₁ := congrArg (fun a => a.left) (map_pow (pushHom h G') (𝟙 G') m)
  have e₂ := congrArg (fun a => a.left) (MonObj.comp_pow (𝟙 G) m (pushHom h G' (𝟙 G')))
  rw [Category.comp_id] at e₂
  refine e₁.trans (e₂.symm.trans ?_)
  change (𝟙 _ ≫ φ) ≫ _ = _
  rw [Category.id_comp]

theorem isGrpPullback_bcMap {k R S : Type} [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (A : Over (Sp k)) [GrpObj A] (ρ : R →ₐ[k] S) :
    IsGrpPullback ((Over.pullback (spMap (algebraMap k S))).obj A) ((Over.pullback (spMap (algebraMap k R))).obj A)
      (spMap ρ.toRingHom) (bcMap A.hom ρ) :=
  (isGrpPullback_pullback A _).cancel
    ((isGrpPullback_pullback A _).congr (spMap_algHom_comp ρ).symm (bcMap_fst A.hom ρ).symm) (bcMap_snd A.hom ρ)

theorem exists_descend {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (A B : Over (Sp K))
    [QuasiCompact A.hom] [QuasiSeparated A.hom] [LocallyOfFinitePresentation B.hom]
    (f : (Over.pullback (spMap (algebraMap K Ω))).obj A ⟶ (Over.pullback (spMap (algebraMap K Ω))).obj B) :
    ∃ s : Finset Ω, ∀ L : IntermediateField K Ω, (s : Set Ω) ⊆ L →
      ∃ g : (Over.pullback (spMap (algebraMap K L))).obj A ⟶ (Over.pullback (spMap (algebraMap K L))).obj B,
        bcMap A.hom L.val ≫ g.left = f.left ≫ bcMap B.hom L.val := by
  have hfw : f.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w f
  obtain ⟨R, ψ, ⟨s, rfl⟩, hψ, hψf⟩ := exists_fg_comp_eq A.hom B.hom (f.left ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ _) hfw)
  refine ⟨s, fun L hL => ?_⟩
  have hle : Algebra.adjoin K (s : Set Ω) ≤ L.toSubalgebra := Algebra.adjoin_le hL
  let ρ : Algebra.adjoin K (s : Set Ω) →ₐ[K] L := Subalgebra.inclusion hle
  have hw : (bcMap A.hom ρ ≫ ψ) ≫ B.hom = pullback.snd _ _ ≫ spMap (algebraMap K L) := by
    rw [Category.assoc, hψ, bcMap_fst_assoc, pullback.condition]
  let g₀ : pullback A.hom (spMap (algebraMap K L)) ⟶ pullback B.hom (spMap (algebraMap K L)) :=
    pullback.lift (bcMap A.hom ρ ≫ ψ) (pullback.snd _ _) hw
  let f₀ : pullback A.hom (spMap (algebraMap K Ω)) ⟶ pullback B.hom (spMap (algebraMap K Ω)) := f.left
  have hf₀ : f₀ ≫ pullback.snd _ _ = pullback.snd _ _ := hfw
  have hψ₀ : bcMap A.hom (Algebra.adjoin K (s : Set Ω)).val ≫ ψ = f₀ ≫ pullback.fst _ _ := hψf
  refine ⟨Over.homMk g₀ (pullback.lift_snd _ _ _), ?_⟩
  change bcMap A.hom L.val ≫ g₀ = f₀ ≫ bcMap B.hom L.val
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, bcMap_fst, pullback.lift_fst,
      bcMap_comp_of_eq_assoc A.hom ρ L.val (Algebra.adjoin K (s : Set Ω)).val fun _ ↦ rfl, hψ₀]
  · rw [Category.assoc, Category.assoc, bcMap_snd, pullback.lift_snd, bcMap_snd, reassoc_of% hf₀]

theorem comp_eq_pow_of_epi {S S' : Scheme.{0}} {j : S' ⟶ S} {G H : Over S} [GrpObj G] {G' H' : Over S'}
    [GrpObj G'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (h : IsGrpPullback G' G j φ) [Epi φ]
    {a' : G' ⟶ H'} {b' : H' ⟶ G'} {a : G ⟶ H} {b : H ⟶ G}
    (ha : φ ≫ a.left = a'.left ≫ ψ) (hb : ψ ≫ b.left = b'.left ≫ φ) (m : ℕ)
    (e : a' ≫ b' = 𝟙 _ ^ m) : a ≫ b = 𝟙 _ ^ m := by
  apply Over.OverMorphism.ext
  rw [← cancel_epi φ, ← id_pow_left_comm h m, ← e, Over.comp_left, Over.comp_left, reassoc_of% ha, hb,
    Category.assoc]

end GlobalTheory.HomPairDescent

namespace GlobalTheory

open HomPairDescent Spread

theorem homPair_descends_to_finite : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (A B : Over (Sp K)) [GrpObj A] [GrpObj B], IsAbelianScheme A → IsAbelianScheme B → ∀ (i : (Over.pullback (spMap (algebraMap K Ω))).obj A ⟶ (Over.pullback (spMap (algebraMap K Ω))).obj B) (r : (Over.pullback (spMap (algebraMap K Ω))).obj B ⟶ (Over.pullback (spMap (algebraMap K Ω))).obj A), IsMonHom i → IsMonHom r → ∃ (L : IntermediateField K Ω) (_ : FiniteDimensional K L) (i' : (Over.pullback (spMap (algebraMap K L))).obj A ⟶ (Over.pullback (spMap (algebraMap K L))).obj B) (r' : (Over.pullback (spMap (algebraMap K L))).obj B ⟶ (Over.pullback (spMap (algebraMap K L))).obj A), IsMonHom i' ∧ IsMonHom r' ∧ ∀ m : ℕ, (i ≫ r = 𝟙 _ ^ m → i' ≫ r' = 𝟙 _ ^ m) ∧ (r ≫ i = 𝟙 _ ^ m → r' ≫ i' = 𝟙 _ ^ m) := by
  classical
  intro K Ω _ _ _ _ A B _ _ hA hB i r hi hr
  have := hA.proper
  have := hB.proper
  have := hA.smooth
  have := hB.smooth
  obtain ⟨s, hs⟩ := exists_descend A B i
  obtain ⟨t, ht⟩ := exists_descend B A r
  let L : IntermediateField K Ω := IntermediateField.adjoin K ((s ∪ t : Finset Ω) : Set Ω)
  have hL : ((s ∪ t : Finset Ω) : Set Ω) ⊆ L := IntermediateField.subset_adjoin _ _
  obtain ⟨i', hi'⟩ := hs L ((Finset.coe_subset.2 Finset.subset_union_left).trans hL)
  obtain ⟨r', hr'⟩ := ht L ((Finset.coe_subset.2 Finset.subset_union_right).trans hL)
  have hfin : FiniteDimensional K L :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have gA := isGrpPullback_bcMap A L.val
  have gB := isGrpPullback_bcMap B L.val
  obtain ⟨hepi, hmon⟩ := FieldBaseChange.epi_and_isMonHom_iff L Ω L.val.toRingHom
  have eA := (hepi _ _ _ _ _ gA.1).1
  have eB := (hepi _ _ _ _ _ gB.1).1
  exact ⟨L, hfin, i', r', (hmon _ _ _ _ _ _ i' i gA gB hi').1 hi, (hmon _ _ _ _ _ _ r' r gB gA hr').1 hr,
    fun m => ⟨comp_eq_pow_of_epi gA hi' hr' m, comp_eq_pow_of_epi gB hr' hi' m⟩⟩

end GlobalTheory
