import Development.EtaleCohomology.EtaleSheaves.FMrangePf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Polynomial LateralTheory.E.BuildCut LateralTheory.E.SysFMPf LateralTheory.E.FMrangePf

namespace LateralTheory.E.IdempotentLifting

abbrev Aq : Type := AdjoinRoot (X ^ 2 - X : ℤ[X])

lemma monic_q : (X ^ 2 - X : ℤ[X]).Monic := by
  apply Polynomial.monic_X_pow_sub
  rw [degree_X]; decide

lemma integral_q : (algebraMap ℤ Aq).IsIntegral := by
  have := monic_q.finite_adjoinRoot
  exact fun x => Algebra.IsIntegral.isIntegral x

def toW {W : Type} [CommRing W] (e : W) (he : IsIdempotentElem e) : Aq →+* W :=
  AdjoinRoot.lift (Int.castRingHom W) e (by simp [sq, he.eq])

theorem IdemLift_of : IdemLift := by
  intro P _ _ W _ w _ e he
  let Z : Scheme.{0} := Spec (CommRingCat.of Aq)
  let t : Z ⟶ Spec (CommRingCat.of ℤ) := Spec.map (CommRingCat.ofHom (algebraMap ℤ Aq))
  have : IsIntegralHom t := IsIntegralHom.SpecMap_iff.2 integral_q
  let g : Spec (CommRingCat.of W) ⟶ Z := Spec.map (CommRingCat.ofHom (toW e he))
  let f₁ : Spec (CommRingCat.of W) ⟶ pullback (specZIsTerminal.from P) t :=
    pullback.lift w g (specZIsTerminal.hom_ext _ _)
  have H : w = f₁ ≫ pullback.fst _ _ := (pullback.lift_fst _ _ _).symm
  let d := w.normalizationDesc f₁ (pullback.fst _ _) H
  let r : Γ(Z, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of Aq)).inv (AdjoinRoot.root _)
  refine ⟨d.appTop ((pullback.snd (specZIsTerminal.from P) t).appTop r), ?_⟩
  have key : w.toNormalization ≫ d ≫ pullback.snd (specZIsTerminal.from P) t = g := by
    rw [← Category.assoc, w.toNormalization_normalizationDesc, pullback.lift_snd]
  have h1 : w.toNormalization.appTop (d.appTop ((pullback.snd (specZIsTerminal.from P) t).appTop r)) =
      g.appTop r := by
    rw [← key]; simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of W)).hom (g.appTop r) = e := by
    rw [← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply]
    simp [r, toW, AdjoinRoot.lift_root]
  unfold phi
  rw [CommRingCat.hom_comp, RingHom.comp_apply]
  exact (congrArg _ h1).trans h2

end LateralTheory.E.IdempotentLifting
