import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasBareNormDisc
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsClopenIrreducibleCpt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentOpenStalksDomain
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NonemptyCptOverOfFlatPreimmersion
import Formalism.LocalToGlobal.ProjectiveLattices.CompSplitPfB
import Formalism.LocalToGlobal.ProjectiveLattices.CompSplitPfD
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Br

theorem exists_ringEquiv_of_genPt_eq {X : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X)
    (ξ' : Sp Ω' ⟶ X) (h : Function.Bijective (Scheme.stalkClosedPointTo ξ).hom)
    (h' : Function.Bijective (Scheme.stalkClosedPointTo ξ').hom) (he : genPt ξ = genPt ξ') :
    ∃ e : Ω ≃+* Ω', spMap e.toRingHom ≫ ξ = ξ' := by
  haveI : IsIso (Scheme.stalkClosedPointTo ξ) := (ConcreteCategory.isIso_iff_bijective _).2 h
  haveI : IsIso (Scheme.stalkClosedPointTo ξ') := (ConcreteCategory.isIso_iff_bijective _).2 h'
  have hi : Inseparable (ξ (IsLocalRing.closedPoint Ω)) (ξ' (IsLocalRing.closedPoint Ω')) := .of_eq he
  let i : CommRingCat.of Ω ≅ CommRingCat.of Ω' :=
    (asIso (Scheme.stalkClosedPointTo ξ)).symm ≪≫ X.presheaf.stalkCongr hi ≪≫
      asIso (Scheme.stalkClosedPointTo ξ')
  refine ⟨i.commRingCatIsoToRingEquiv, ?_⟩
  have e1 : Scheme.stalkClosedPointTo ξ ≫ i.hom =
      (X.presheaf.stalkCongr hi).hom ≫ Scheme.stalkClosedPointTo ξ' := by simp [i]
  have h1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  have h2 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ'
  have h3 : Spec.map (X.presheaf.stalkCongr hi).hom ≫ X.fromSpecStalk _ = X.fromSpecStalk _ :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk hi.symm.specializes
  show Spec.map i.hom ≫ ξ = ξ'
  conv_lhs => rw [← h1]
  conv_rhs => rw [← h2]
  rw [← Category.assoc, ← Spec.map_comp, e1, Spec.map_comp, Category.assoc, h3]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem bijective_stalk_of_cptOver {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {U : Set (Xo.XF c)}
    (Z : CptOver Y U) (hβ : FracBase β) : Function.Bijective (Scheme.stalkClosedPointTo Z.ξ₀).hom := by
  obtain ⟨h1, h2⟩ := j_flat_preimmersion Y hβ.1 hβ.2.2
  have hb := stalkMap_bijective_of_flat_preimmersion Y.j (Z.ξ₀ (IsLocalRing.closedPoint Z.Ω))
  have hg := Z.gen.bij
  rw [Scheme.stalkClosedPointTo_comp] at hg
  exact (Function.Bijective.of_comp_iff _ hb).1 hg

theorem genPt_eq_of_cptOver {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F}
    {Y : Model Xo c β} {Y' : Model Xo c β'} {U : Set (Xo.XF c)} (Z : CptOver Y U) (Z' : CptOver Y' U) :
    genPt Z.ξ₀ = genPt Z'.ξ₀ :=
  (((Z.closure _).1 Z'.genPt_mem).antisymm ((Z'.closure _).1 Z.genPt_mem)).eq

theorem cptOver_any : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)), U ∈ irreducibleComponents (Xo.XF c) → IsClopen U ∧ (∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), FracBase β → Nonempty (CptOver Y U)) ∧ ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (Y' : Model Xo c β') (Z : CptOver Y U) (Z' : CptOver Y' U), FracBase β → FracBase β' → Z.IsGeom → Z'.IsGeom := by
  intro E _ _ _ H D l Xo c U hU
  refine ⟨Formalism.L2.Pj.CompSplitPfB.cspB_isClopen (Formalism.L2.Pj.CompSplitPfD.cspD_comp_disj Xo c) ⟨U, hU⟩,
    fun O _ β Y hβ => nonempty_cptOver_of_fraction hβ.1 hβ.2.2 Y U hU, ?_⟩
  intro O _ β Y O' _ β' Y' Z Z' hβ hβ' hg
  obtain ⟨e, he⟩ := exists_ringEquiv_of_genPt_eq Z.ξ₀ Z'.ξ₀ (bijective_stalk_of_cptOver Z hβ)
    (bijective_stalk_of_cptOver Z' hβ') (genPt_eq_of_cptOver Z Z')
  have h2 : spMap e.toRingHom ≫ spMap Z.inc = spMap Z'.inc := by
    rw [← Z.over_inc, ← Z'.over_inc, ← he, Category.assoc]
  have h4 : CommRingCat.ofHom Z.inc ≫ CommRingCat.ofHom e.toRingHom = CommRingCat.ofHom Z'.inc :=
    Spec.map_injective (by rw [Spec.map_comp]; exact h2)
  have h3 : e.toRingHom.comp Z.inc = Z'.inc := congrArg CommRingCat.Hom.hom h4
  rintro x ⟨f, hf, hx⟩
  have h5 : f.eval₂ Z.inc (e.symm x) = 0 := by
    apply e.injective
    have := Polynomial.hom_eval₂ f Z.inc e.toRingHom (e.symm x)
    rw [h3] at this
    simpa [hx] using this
  obtain ⟨a, ha⟩ := hg (e.symm x) ⟨f, hf, h5⟩
  refine ⟨a, ?_⟩
  rw [← h3]
  simp [ha]

end GlobalTheory.CompanionTheory.Ar.Br
