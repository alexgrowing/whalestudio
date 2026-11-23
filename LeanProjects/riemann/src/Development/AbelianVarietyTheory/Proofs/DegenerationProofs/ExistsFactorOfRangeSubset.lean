import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LawsChart
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AlgOverHomSurjective
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
namespace GlobalTheory.SS.ArcInf

theorem exists_factor_of_range_subset {k : Type} [CommRing k] {G : Over (Sp k)} {A B : Type} [CommRing A]
    [Algebra k A] [CommRing B] [Algebra k B] (j : algOver k A ⟶ G) (hj : IsOpenImmersion j.left)
    (a : algOver k B ⟶ G) (hr : Set.range a.left ⊆ Set.range j.left) :
    ∃ χ : A →ₐ[k] B, algOverHom χ ≫ j = a := by
  have hf := IsOpenImmersion.lift_fac j.left a.left hr
  let l : algOver k B ⟶ algOver k A := Over.homMk (IsOpenImmersion.lift j.left a.left hr) (by
    rw [← Over.w j, ← Category.assoc, hf, Over.w a])
  obtain ⟨χ, hχ⟩ := algOverHom_surjective l
  refine ⟨χ, ?_⟩
  rw [hχ]
  ext1
  exact hf

theorem exists_extend_of_localSubring : ∀ (k : Type) [CommRing k] (G : Over (Sp k)) (O K F : Type) [CommRing O] [Algebra k O] [Field K] [Algebra k K] [Field F] [Algebra k F] (em : O →ₐ[k] K) (σ : K →ₐ[k] F) (L : Subalgebra k F), IsLocalRing L → Function.Injective em → (∀ x, σ x ∈ L → x ∈ Set.range em) → ∀ (a : algOver k K ⟶ G) (b' : algOver k L ⟶ G), algOverHom σ ≫ a = algOverHom L.val ≫ b' → ∃ b : algOver k O ⟶ G, algOverHom em ≫ b = a := by
  intro k _ G O K F _ _ _ _ _ _ em σ L hL hem hsub a b' hab
  let x0 : (Sp L) := IsLocalRing.closedPoint L
  obtain ⟨R, i, hi, hx, -⟩ := Scheme.exists_affine_mem_range_and_range_subset (X := G.left)
    (x := b'.left x0) (U := ⊤) trivial
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (i ≫ G.hom : Spec R ⟶ Spec (CommRingCat.of k))
  letI : Algebra k R := φ.hom.toAlgebra
  let j : algOver k R ⟶ G := Over.homMk i hφ.symm
  have hj : IsOpenImmersion j.left := hi
  have hrb : Set.range b'.left ⊆ Set.range j.left := by
    rintro _ ⟨y, rfl⟩
    have hs : y ⤳ x0 := IsLocalRing.specializes_closedPoint (R := L) y
    have hs' := hs.map b'.left.continuous
    exact hs'.mem_open j.left.isOpenEmbedding.isOpen_range hx
  have hra : Set.range a.left ⊆ Set.range j.left := by
    rintro _ ⟨y, rfl⟩
    let p : (Sp F) := IsLocalRing.closedPoint F
    have hy : y = (algOverHom σ).left p := Subsingleton.elim (α := PrimeSpectrum K) _ _
    have hl : (algOverHom σ).left ≫ a.left = (algOverHom L.val).left ≫ b'.left := by
      rw [← Over.comp_left, ← Over.comp_left, hab]
    apply hrb
    refine ⟨(algOverHom L.val).left p, ?_⟩
    rw [hy, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hl]
  obtain ⟨χL, hχL⟩ := exists_factor_of_range_subset j hj b' hrb
  obtain ⟨χK, hχK⟩ := exists_factor_of_range_subset j hj a hra
  have hc : σ.comp χK = L.val.comp χL := by
    apply eq_of_comp_eq hj
    rw [algOverHom_comp, algOverHom_comp, Category.assoc, Category.assoc, hχK, hχL, hab]
  have hmem : ∀ x, χK x ∈ em.range := fun x => by
    apply hsub
    have : σ (χK x) = (χL x : F) := DFunLike.congr_fun hc x
    rw [this]
    exact (χL x).2
  let χO : R →ₐ[k] O :=
    ((AlgEquiv.ofInjective em hem).symm : em.range →ₐ[k] O).comp (χK.codRestrict em.range hmem)
  have hO : em.comp χO = χK := by
    ext x
    have := AlgEquiv.ofInjective_apply em hem ((AlgEquiv.ofInjective em hem).symm ⟨χK x, hmem x⟩)
    rw [AlgEquiv.apply_symm_apply] at this
    exact this.symm
  refine ⟨algOverHom χO ≫ j, ?_⟩
  rw [← Category.assoc, ← algOverHom_comp, hO, hχK]

end GlobalTheory.SS.ArcInf
