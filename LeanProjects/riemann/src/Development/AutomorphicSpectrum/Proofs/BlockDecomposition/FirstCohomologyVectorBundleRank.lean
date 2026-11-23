import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.IsPullbackH2Structure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeAndRelDimOfIsGrpPullback

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Hodge.FirstCohomologyVectorBundle

theorem exists_base {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] {g : ℕ} (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) (B : Type) [CommRing B] [Algebra R B] :
    ∃ (A' : Over (Sp B)) (_ : GrpObj A') (φ : A'.left ⟶ A.left), IsAbelianScheme A' ∧
      SmoothOfRelativeDimension g A'.hom ∧ IsPullback φ A'.hom A.hom (spMap (algebraMap R B)) := by
  have h := isGrpPullback_pullback A (spMap (algebraMap R B))
  obtain ⟨h1, h2⟩ := GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback _ _ _ _ g h hA hg
  exact ⟨_, inferInstance, _, h1, h2, h.1⟩

theorem vb_of_bijective {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C']
    {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R} (m : CoefMap (RingHom.id R) F F')
    (h1 : Function.Bijective m.pull1) {n : ℕ} (h : VB R (H1 F) n) : VB R (H1 F') n := by
  let E1 : H1 F ≃ₗ[R] H1 F' := LinearEquiv.ofBijective m.pull1 h1
  obtain ⟨hf, hp, hr⟩ := h
  refine ⟨Module.Finite.equiv E1, Module.Projective.of_equiv E1, fun p => ?_⟩
  rw [← Module.rankAtStalk_eq_of_equiv E1]
  exact hr p

theorem vb_of_bijective' {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C']
    {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R} (m : CoefMap (RingHom.id R) F F')
    (h1 : Function.Bijective m.pull1) {n : ℕ} (h : VB R (H1 F') n) : VB R (H1 F) n := by
  let E1 : H1 F ≃ₗ[R] H1 F' := LinearEquiv.ofBijective m.pull1 h1
  obtain ⟨hf, hp, hr⟩ := h
  refine ⟨Module.Finite.equiv E1.symm, Module.Projective.of_equiv E1.symm, fun p => ?_⟩
  rw [Module.rankAtStalk_eq_of_equiv E1]
  exact hr p

theorem finrank_of_vb {k M : Type} [Field k] [AddCommGroup M] [Module k M] {n : ℕ} (h : VB k M n) :
    Module.finrank k M = n := by
  obtain ⟨hf, -, hr⟩ := h
  have e := hr ⊥
  rwa [Module.rankAtStalk_eq_finrank_of_free] at e

theorem first_cohomology_vector_bundle_rank : DescentSt → LowSt → SysBCSt → PerfSt → SteinSt → H1StructureFieldDim → SmallLiftSt → PerfVBSt → H1StructureBundle := by
  intro hD hL hB hP hS hK hT hV R _ A _ g hA hg
  have : IsProper A.hom := hA.proper
  have : IsSeparated A.hom := inferInstance
  have : Smooth A.hom := hg.smooth
  obtain ⟨P, iP, fP, S, hPerf⟩ := hP R A.left A.hom inferInstance inferInstance
  have low : ∀ {R₀ : Type} [CommRing R₀] (A₀ : Over (Sp R₀)) [GrpObj A₀], IsAbelianScheme A₀ →
      ∀ (S₀ : Sys A₀.left P), Function.Bijective (resSys A₀.hom S₀).pull1 ∧
        (Stein (OAff A₀.hom) ↔ Stein (OSys A₀.hom S₀)) := fun {R₀} _ A₀ _ h₀ S₀ => by
    have : IsProper A₀.hom := h₀.proper
    obtain ⟨b1, -, st⟩ := hL R₀ _ _ _ _ _ (hD R₀ A₀.left A₀.hom inferInstance P S₀)
    exact ⟨b1, st⟩
  refine vb_of_bijective' (resSys A.hom S) (low A hA S).1 (hV R P (OSys A.hom S) g hPerf ?_ ?_ ?_)
  · intro R' _ _
    obtain ⟨A', _, φ, hA', hg', h⟩ := exists_base A hA hg R'
    obtain ⟨S', m, -⟩ := hB R R' A.left A'.left A.hom A'.hom φ h inferInstance P S
    exact ⟨OSys A'.hom S', m, (low A' hA' S').2.1 (hS R' A' g hA' hg')⟩
  · intro k _ _
    obtain ⟨A', _, φ, hA', hg', h⟩ := exists_base A hA hg k
    obtain ⟨S', m, -⟩ := hB R k A.left A'.left A.hom A'.hom φ h inferInstance P S
    exact ⟨OSys A'.hom S', m, finrank_of_vb
      (vb_of_bijective _ (low A' hA' S').1 (hK k A' g hA' hg' (Field.toIsField k)))⟩
  · intro B _ _ _ t ht
    obtain ⟨A', _, φ, hA', hg', h⟩ := exists_base A hA hg B
    obtain ⟨S', m, -⟩ := hB R B A.left A'.left A.hom A'.hom φ h inferInstance P S
    obtain ⟨A'', _, φ', hA'', hg'', h'⟩ := exists_base A' hA' hg' (B ⧸ Ideal.span {t})
    have : IsProper A'.hom := hA'.proper
    obtain ⟨S'', m', hm'⟩ := hB B (B ⧸ Ideal.span {t}) A'.left A''.left A'.hom A''.hom φ' h' inferInstance P S'
    refine ⟨OSys A'.hom S', m, OSys A''.hom S'', m', fun y => ?_⟩
    have b2 := (low A'' hA'' S'').1
    obtain ⟨d, rfl⟩ := b2.2 y
    obtain ⟨c, hc⟩ := hT B A' g hA' hg' t ht A''.left A''.hom φ' h' d
    refine ⟨(resSys A'.hom S').pull1 c, ?_⟩
    obtain ⟨d', hd'⟩ := b2.2 (m'.coef.pull1 ((resSys A'.hom S').pull1 c))
    have e := (existsUnique_isPullO h'.w c).unique hc (hm' c d' hd'.symm)
    rw [e, hd']

end GlobalTheory.CompanionTheory.Hodge.FirstCohomologyVectorBundle
