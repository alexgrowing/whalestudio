import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInclusionCyclotomicAwayRingFiniteEtale
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LineBundleIsoDescendsToSubringOfFinset
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MorphismDescendsToSubring
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsToFinitelyGeneratedSubring
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsNoethModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrincipalObjectDescendsLargeSubfield
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsEqOfSpMapSubtypeCompEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalBundleDescendsSubringStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectDataDescendsFiniteTypeSubringStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPolarizedLevelTripleOfSubringLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidSymmetricBundleDescendsToSubringFinsetStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

namespace GlobalTheory.SiegFGData

theorem data : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (R : Type) [CommRing R] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ (R₀ : Subring R) (β₀ : cycAway n →+* R₀) (A₀ : Over (Sp R₀)) (_ : GrpObj A₀) (P₀ : LB (A₀ ⊗ A₀).left) (lv₀ : Std g n → (𝟙_ (Over (Sp R₀)) ⟶ A₀)), Algebra.FiniteType ℤ R₀ ∧ R₀.subtype.comp β₀ = β ∧ IsSymmetricPair g A₀ P₀ ∧ (∀ a b, lv₀ (a + b) = lv₀ a * lv₀ b) ∧ Out.RelAmple A₀ (diagPull A₀ P₀) ∧ IsPullbackTriple c.A c.P (lvOf c) A₀ P₀ lv₀ (spMap R₀.subtype) := by
  intro g n hn _ R _ β c hc
  have h0 : n ≠ 0 := by omega
  obtain ⟨R₁, β₁, A₁, _, P₁, lv₁, hfg, hβ, hA₁, hd₁, hP₁, htr⟩ := GlobalTheory.T.siegelObject_data_descends_finiteType_subring g n hn R β c
  have htr' := htr
  obtain ⟨φ, φ₂, hφ, sq₁, sq₂, iso, hl⟩ := htr
  have : IsNoetherianRing R₁ := Algebra.FiniteType.isNoetherianRing ℤ R₁
  have hsym : IsSymmetricPair g c.A c.P := isSymmetricPair (ζ := (cycBase h0).ζ) (by omega) (isUnit_natCast h0) c
  have hlev : IsLevel c.A (lvOf c) := isLevel_lvOf (ζ := (cycBase h0).ζ) c
  obtain ⟨hAb, hdim, hPlb, hr1, hr2, hsy⟩ := hsym
  obtain ⟨F₅, H₅⟩ := GlobalTheory.T.rigidSymmetricBundle_descends_to_subring_finset R R₁ c.A c.P A₁ P₁ φ φ₂ hA₁ hPlb hP₁ hφ ⟨sq₁, sq₂⟩ iso hr1 hr2 hsy
  obtain ⟨F₂, H₂⟩ := GlobalTheory.T.relAmple_diagonal_bundle_descends_subring R R₁ c.A c.P A₁ P₁ φ φ₂ hA₁ hPlb hP₁ hφ ⟨sq₁, sq₂⟩ iso hc.1
  classical
  let S : Subalgebra R₁ R := Algebra.adjoin R₁ ((F₅ ∪ F₂ : Finset R) : Set R)
  let R₂ : Subring R := S.toSubring
  have h12 : R₁ ≤ R₂ := fun x hx => S.algebraMap_mem ⟨x, hx⟩
  have hF : ((F₅ ∪ F₂ : Finset R) : Set R) ⊆ R₂ := Algebra.subset_adjoin
  have hfg₂ : Algebra.FiniteType ℤ R₂ := GlobalTheory.SpreadGroup.finiteType_of_fg hfg (Subalgebra.fg_adjoin_finset _)
  obtain ⟨A₂, _, lv₂, π, π₂, hA₂, hd₂, hπ, sqπ, htr₂⟩ :=
    GlobalTheory.T.pullbackPolarizedLevelTriple_of_subring_le R R₁ R₂ h12 g n c.A c.P (lvOf c) A₁ P₁ lv₁ hA₁ hd₁ hPlb hP₁ htr'
  obtain ⟨t1, t2, t3⟩ := H₅ R₂ h12 (fun x hx => hF (by simp [hx])) A₂ π π₂ hπ sqπ
  have am := H₂ R₂ h12 (fun x hx => hF (by simp [hx])) A₂ π π₂ hπ sqπ
  refine ⟨R₂, (Subring.inclusion h12).comp β₁, A₂, inferInstance, P₁.pull π₂, lv₂, hfg₂, ?_,
    ⟨hA₂, hd₂, pull_isLB hP₁ _, t1, t2, t3⟩, ?_, am, htr₂⟩
  · rw [← hβ]
    rfl
  · intro a b
    obtain ⟨ψ, ψ₂, hψ, -, -, -, hl₂⟩ := htr₂
    have : IsSeparated A₂.hom := by have := hA₂.proper; infer_instance
    refine Over.OverMorphism.ext (GlobalTheory.T.eq_of_spMap_subtype_comp_eq_of_isSeparated R R₂ A₂.left A₂.hom _ _ ?_ ?_)
    · exact (Over.w (lv₂ (a + b))).trans (Over.w (lv₂ a * lv₂ b)).symm
    · let f := spMap R₂.subtype
      let u : Over.mk ((𝟙_ (Over (Sp R))).hom ≫ f) ⟶ 𝟙_ (Over (Sp R₂)) := toUnit _
      have hu : u.left = (𝟙_ (Over (Sp R))).hom ≫ f := Over.toUnit_left
      have hid : (𝟙_ (Over (Sp R))).hom = 𝟙 _ := rfl
      have m := hψ.2 (𝟙_ (Over (Sp R))) (lvOf c a) (lvOf c b) (u ≫ lv₂ a) (u ≫ lv₂ b)
        (by rw [Over.comp_left, hu, hid, Category.id_comp]; exact (hl₂ a).symm)
        (by rw [Over.comp_left, hu, hid, Category.id_comp]; exact (hl₂ b).symm)
      rw [← MonObj.comp_mul, Over.comp_left, hu, hid, Category.id_comp, ← hlev.1] at m
      exact (hl₂ (a + b)).symm.trans m.symm

end GlobalTheory.SiegFGData
