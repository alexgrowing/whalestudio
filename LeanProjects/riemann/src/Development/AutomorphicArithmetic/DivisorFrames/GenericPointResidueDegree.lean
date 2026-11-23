import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConsAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ChiLenPicPushforwardOfIsClosedImmersion
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ConsGeo

private theorem residue_bijective_of_isField {R : Type} [CommRing R] [IsLocalRing R] (h : IsField R) :
    Function.Bijective (IsLocalRing.residue R) := by
  refine ⟨?_, IsLocalRing.residue_surjective⟩
  rw [injective_iff_map_eq_zero]
  intro a ha
  rw [IsLocalRing.residue_eq_zero_iff, (IsLocalRing.isField_iff_maximalIdeal_eq).1 h] at ha
  simpa using ha

private theorem residueDegree_eq_of_isField {X W : Scheme.{0}} (f : W ⟶ X) (w : W) (x : X) (e : f w = x)
    (ψ : X.presheaf.stalk x ⟶ W.presheaf.stalk w)
    (h : W.fromSpecStalk w ≫ f = Spec.map ψ ≫ X.fromSpecStalk x)
    (hx : IsField (X.presheaf.stalk x)) (hw : IsField (W.presheaf.stalk w)) :
    f.residueDegree w =
      (letI := ψ.hom.toAlgebra; Module.finrank (X.presheaf.stalk x) (W.presheaf.stalk w)) := by
  subst e
  rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, cancel_mono] at h
  have h' : f.stalkMap w = ψ := Spec.map_injective h
  subst h'
  letI := (f.stalkMap w).hom.toAlgebra
  letI := (f.residueFieldMap w).hom.toAlgebra
  symm
  refine Algebra.finrank_eq_of_equiv_equiv
    (RingEquiv.ofBijective (X.residue (f w)).hom (residue_bijective_of_isField hx))
    (RingEquiv.ofBijective (W.residue w).hom (residue_bijective_of_isField hw)) ?_
  ext a
  exact congrArg (fun g => CommRingCat.Hom.hom g a) (Scheme.residue_residueFieldMap f w)

theorem UpperTheory.generic_point_residueDegree :
    ∀ (X W : Scheme.{0}) [IsIntegral X] [IsIntegral W] (f : W ⟶ X) (ψ : X.functionField →+* W.functionField), gpt W ≫ f = spMap ψ ≫ gpt X → f (genericPoint W) = genericPoint X ∧ f.residueDegree (genericPoint W) = embDeg ψ := by
  intro X W _ _ f ψ h
  have h' : W.fromSpecStalk (genericPoint W) ≫ f =
      Spec.map (CommRingCat.ofHom ψ) ≫ X.fromSpecStalk (genericPoint X) := h
  have e : f (genericPoint W) = genericPoint X := by
    have h1 := congrArg (fun g : Spec (W.presheaf.stalk (genericPoint W)) ⟶ X =>
      g (closedPoint (W.presheaf.stalk (genericPoint W)))) h'
    have h0 : f (W.fromSpecStalk (genericPoint W) (closedPoint (W.presheaf.stalk (genericPoint W)))) =
        X.fromSpecStalk (genericPoint X)
          (Spec.map (CommRingCat.ofHom ψ) (closedPoint (W.presheaf.stalk (genericPoint W)))) := h1
    refine ((congrArg f Scheme.fromSpecStalk_closedPoint).symm.trans h0).trans ?_
    have h2 : Spec.map (CommRingCat.ofHom ψ) (closedPoint (W.presheaf.stalk (genericPoint W))) =
        closedPoint (X.presheaf.stalk (genericPoint X)) :=
      Subsingleton.elim (α := PrimeSpectrum X.functionField) _ _
    exact (congrArg (X.fromSpecStalk (genericPoint X)) h2).trans Scheme.fromSpecStalk_closedPoint
  exact ⟨e, residueDegree_eq_of_isField f _ _ e (CommRingCat.ofHom ψ) h'
    (Field.toIsField X.functionField) (Field.toIsField W.functionField)⟩
