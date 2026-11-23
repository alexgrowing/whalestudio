import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaNsmul
import Development.AbelianVarietyTheory.Definitions.Uniformization.InKLbPowIffPowEqOne
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FormallyUnramifiedMulInvertibleInteger
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel GlobalTheory.UPel.HeckeImage

namespace GlobalTheory.TorsionRigid

theorem eq_one_of_pow_eq_one_of_geometric : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (m : ℕ), 0 < m → IsUnit ((m : Γ(S, ⊤))) → ∀ (T : Over S) (x : T ⟶ A), x ^ m = 1 → (∀ (κ : Type) [Field κ] [IsAlgClosed κ] (q : Sp κ ⟶ T.left), (Over.homMk q rfl : Over.mk (q ≫ T.hom) ⟶ T) ≫ x = 1) → x = 1 := by
  intro S A _ _ hA m _ hm T x hx hgeo
  let f := (ReciprocityTheory.ChartRestriction.G.Out.mulA A m).left
  haveI : FormallyUnramified f := GlobalTheory.formallyUnramified_mulA S A m hm
  haveI : Smooth A.hom := hA.smooth
  have hfA : f ≫ A.hom = A.hom := Over.w _
  haveI : LocallyOfFiniteType (f ≫ A.hom) := by rw [hfA]; infer_instance
  haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f A.hom
  have hpow : ∀ y : T ⟶ A, y ≫ ReciprocityTheory.ChartRestriction.G.Out.mulA A m = y ^ m := fun y => by
    simp [ReciprocityTheory.ChartRestriction.G.Out.mulA, MonObj.comp_pow]
  have hf : x.left ≫ f = (1 : T ⟶ A).left ≫ f := by
    have e1 := congrArg CommaMorphism.left (hpow x)
    have e2 := congrArg CommaMorphism.left (hpow 1)
    simp only [Over.comp_left] at e1 e2
    rw [e1, e2, hx, one_pow]
  let p : T.left ⟶ pullback f f := pullback.lift x.left (1 : T ⟶ A).left hf
  have hr : Set.range p ⊆ Set.range (pullback.diagonal f) := by
    rintro _ ⟨t, rfl⟩
    let κ : Type := AlgebraicClosure (T.left.residueField t)
    let q : Sp κ ⟶ T.left :=
      Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField t) κ)) ≫ T.left.fromSpecResidueField t
    have hq : (Over.homMk q rfl : Over.mk (q ≫ T.hom) ⟶ T) ≫ x = (Over.homMk q rfl : Over.mk (q ≫ T.hom) ⟶ T) ≫ 1 := by
      rw [hgeo κ q, MonObj.comp_one]
    have hq' : q ≫ x.left = q ≫ (1 : T ⟶ A).left := by
      have h0 := congrArg (fun h => h.left) hq
      simp only [Over.comp_left, Over.homMk_left] at h0
      exact h0
    have e : q ≫ p = (q ≫ x.left) ≫ pullback.diagonal f := by
      refine pullback.hom_ext ?_ ?_
      · simp only [p, Category.assoc, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
      · simp only [p, Category.assoc, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id, hq']
    refine ⟨(q ≫ x.left) (IsLocalRing.closedPoint κ), ?_⟩
    have hqt : q (IsLocalRing.closedPoint κ) = t :=
      Scheme.fromSpecResidueField_apply t _
    have e2 : p (q (IsLocalRing.closedPoint κ)) =
        pullback.diagonal f ((q ≫ x.left) (IsLocalRing.closedPoint κ)) :=
      congrArg (fun h => h (IsLocalRing.closedPoint κ)) e
    rw [hqt] at e2
    exact e2.symm
  let g := IsOpenImmersion.lift (pullback.diagonal f) p hr
  have hg := IsOpenImmersion.lift_fac (pullback.diagonal f) p hr
  have h1 : x.left = g := by
    have h0 := congrArg (· ≫ pullback.fst f f) hg
    simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, p, pullback.lift_fst] at h0
    exact h0.symm
  have h2 : (1 : T ⟶ A).left = g := by
    have h0 := congrArg (· ≫ pullback.snd f f) hg
    simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id, p, pullback.lift_snd] at h0
    exact h0.symm
  exact Over.OverMorphism.ext (h1.trans h2.symm)

end GlobalTheory.TorsionRigid
