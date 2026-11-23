import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasBareNormDisc
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Br

theorem exists_fieldMap_of_surjective {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ X)
    (h : Function.Surjective (Scheme.stalkClosedPointTo ξ).hom) (z : X) (hz : ξ (IsLocalRing.closedPoint Ω) = z) :
    ∃ i : Ω →+* X.residueField z, spMap i ≫ ξ = X.fromSpecResidueField z := by
  subst hz
  let g := X.descResidueField (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) ξ)
  have hsurj : Function.Surjective g.hom := by
    intro a
    obtain ⟨b, hb⟩ := h a
    refine ⟨(X.residue _).hom b, ?_⟩
    have e := congrArg CommRingCat.Hom.hom
      (X.residue_descResidueField (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) ξ))
    exact (congrArg (fun φ => φ b) e).trans hb
  let e : X.residueField (ξ (IsLocalRing.closedPoint Ω)) ≃+* Ω :=
    RingEquiv.ofBijective g.hom ⟨g.hom.injective, hsurj⟩
  refine ⟨e.symm.toRingHom, ?_⟩
  have h1 : Spec.map g ≫ X.fromSpecResidueField (ξ (IsLocalRing.closedPoint Ω)) = ξ :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField Ω X ξ
  have h2 : spMap e.symm.toRingHom ≫ Spec.map g = 𝟙 _ := by
    have h3 : g ≫ CommRingCat.ofHom e.symm.toRingHom = 𝟙 _ := by
      ext a
      exact e.symm_apply_apply a
    exact (Spec.map_comp _ _).symm.trans ((congrArg Spec.map h3).trans (Spec.map_id _))
  refine (congrArg (spMap e.symm.toRingHom ≫ ·) h1).symm.trans ?_
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ X.fromSpecResidueField _) h2).trans (Category.id_comp _))

theorem isGeom_of_fnAlgClosed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : Formalism.L2.Pj.Comp Xo c) (Z' : CptOver Y (Z : Set (Xo.XF c))), FracBase β → Formalism.L2.Pj.FnAlgClosed Xo c → Z'.IsGeom := by
  intro E _ _ _ H D l Xo c O _ β Y Z Z' _ hc x ⟨f, hf0, hf⟩
  have hsurj : Function.Surjective (Scheme.stalkClosedPointTo Z'.ξ₀).hom := by
    have h := Z'.gen.bij.2
    rw [Scheme.stalkClosedPointTo_comp] at h
    intro a
    obtain ⟨b, hb⟩ := h a
    exact ⟨_, hb⟩
  have hgp : genPt Z'.ξ₀ = Formalism.L2.Pj.genPt Z := by
    have hg := Z.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ Z.2)
    have h2 : Formalism.L2.Pj.genPt Z ⤳ genPt Z'.ξ₀ := hg.specializes Z'.genPt_mem
    have h3 : genPt Z'.ξ₀ ⤳ Formalism.L2.Pj.genPt Z := (Z'.closure _).1 hg.mem
    exact (h3.antisymm h2).eq
  obtain ⟨i, hi⟩ := exists_fieldMap_of_surjective Z'.ξ₀ hsurj _ hgp
  have hcomp : i.comp Z'.inc = algebraMap c.F (Formalism.L2.Pj.kap Z) := by
    have h1 : Formalism.L2.Pj.genSp Z ≫ Formalism.L2.Pj.strK = spMap (algebraMap c.F (Formalism.L2.Pj.kap Z)) :=
      (Spec.map_preimage _).symm
    have h2 : spMap (i.comp Z'.inc) = spMap (algebraMap c.F (Formalism.L2.Pj.kap Z)) := by
      rw [← h1]
      have e : spMap (i.comp Z'.inc) = spMap i ≫ spMap Z'.inc := by
        rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl
      rw [e, ← Z'.over_inc, ← Category.assoc, hi]
      rfl
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h2)
  have hb : IsAlgebraic c.F (algebraMap (Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.Om Z) (i x)) := by
    refine ⟨f, hf0, ?_⟩
    have h3 := Polynomial.hom_eval₂ f Z'.inc ((algebraMap (Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.Om Z)).comp i) x
    rw [hf, map_zero] at h3
    rw [Polynomial.aeval_def]
    refine Eq.trans ?_ h3.symm
    have e : algebraMap c.F (Formalism.L2.Pj.Om Z) =
        ((algebraMap (Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.Om Z)).comp i).comp Z'.inc := by
      rw [RingHom.comp_assoc, hcomp]
      exact IsScalarTower.algebraMap_eq _ _ _
    rw [e]
    rfl
  obtain ⟨k, hk⟩ := hc Z _ hb
  refine ⟨k, i.injective ?_⟩
  have h2 : algebraMap c.F (Formalism.L2.Pj.kap Z) k = i x := by
    apply (algebraMap (Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.Om Z)).injective
    rw [← hk, ← IsScalarTower.algebraMap_apply]
  rw [← h2, ← hcomp]
  rfl

end GlobalTheory.CompanionTheory.Ar.Br
