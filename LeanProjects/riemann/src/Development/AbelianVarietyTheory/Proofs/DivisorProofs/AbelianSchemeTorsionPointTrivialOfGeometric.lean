import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionRigid

theorem eq_one_of_geometric (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) (T : Over S) (x : T ⟶ A) (c : ℕ) (hc : IsUnit (c : Γ(T.left, ⊤)))
    (hx : x ^ c = 1)
    (H : ∀ (k : Type) [Field k] [IsAlgClosed k], (c : k) ≠ 0 → ∀ (z : Sp k ⟶ S)
      (g : Over.mk z ⟶ T), g ≫ x = 1) : x = 1 := by
  have := hA.smooth
  let AT := (Over.pullback T.hom).obj A
  have hft : LocallyOfFiniteType AT.hom := by
    change LocallyOfFiniteType (pullback.snd A.hom T.hom); infer_instance
  let f := ((Over.pullback T.hom).map (mulN A c)).left
  have hfu : FormallyUnramified f := by
    have h := GlobalTheory.GrpTangent.formallyUnramified_mulN AT hc
    rw [← GlobalTheory.GrpTangent.pullback_map_mulN] at h
    exact h
  have hff : LocallyOfFiniteType f := by
    have : LocallyOfFiniteType (f ≫ AT.hom) := by
      rw [show f ≫ AT.hom = AT.hom from Over.w ((Over.pullback T.hom).map (mulN A c))]
      infer_instance
    exact locallyOfFiniteType_of_comp f AT.hom
  let sec : (T ⟶ A) → (T.left ⟶ AT.left) := fun y =>
    pullback.lift y.left (𝟙 T.left) (by rw [Over.w y, Category.id_comp])
  have sec_fst : ∀ y : T ⟶ A, sec y ≫ pullback.fst A.hom T.hom = y.left := fun y =>
    pullback.lift_fst _ _ _
  have sec_snd : ∀ y : T ⟶ A, sec y ≫ pullback.snd A.hom T.hom = 𝟙 _ := fun y =>
    pullback.lift_snd _ _ _
  have f_fst : f ≫ pullback.fst A.hom T.hom = pullback.fst A.hom T.hom ≫ (mulN A c).left :=
    pullback.lift_fst _ _ _
  have f_snd : f ≫ pullback.snd A.hom T.hom = pullback.snd A.hom T.hom :=
    pullback.lift_snd _ _ _
  have sec_f : ∀ y : T ⟶ A, sec y ≫ f = sec (y ^ c) := by
    intro y
    apply pullback.hom_ext
    · rw [Category.assoc, f_fst, ← Category.assoc, sec_fst, sec_fst,
        ← GlobalTheory.GrpTangent.comp_mulN]
      rfl
    · rw [Category.assoc, f_snd, sec_snd, sec_snd]
  have key : sec x ≫ f = sec 1 ≫ f := by rw [sec_f, sec_f, hx, one_pow]
  let Y : Over AT.left := Over.mk f
  let X : Over AT.left := Over.mk (sec 1 ≫ f)
  let fx : X ⟶ Y := Over.homMk (sec x) key
  let f1 : X ⟶ Y := Over.homMk (sec 1) rfl
  haveI : LocallyOfFiniteType Y.hom := hff
  haveI : FormallyUnramified Y.hom := hfu
  have hpt : ∀ t : T.left, t ∈ Set.range (GlobalTheory.FinEt.agreeι fx f1) := by
    intro t
    obtain ⟨k, _, _, a, ha⟩ := GlobalTheory.FinEt.exists_algClosed_point T.left t
    have hk : (c : k) ≠ 0 := (GlobalTheory.GrpTangent.isUnit_natCast_of_point hc a).ne_zero
    have h1 := H k hk (a ≫ T.hom) (Over.homMk a rfl)
    have h2 : a ≫ x.left = a ≫ (1 : T ⟶ A).left := by
      have := congrArg CommaMorphism.left
        (h1.trans (comp_one (Over.homMk a rfl : Over.mk (a ≫ T.hom) ⟶ T)).symm)
      exact this
    have h3 : a ≫ fx.left = a ≫ f1.left := by
      change a ≫ sec x = a ≫ sec 1
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, sec_fst, sec_fst, h2]
      · rw [Category.assoc, Category.assoc, sec_snd, sec_snd]
    have h4 := (GlobalTheory.FinEt.comp_eq_comp_iff_range fx f1 a).mp h3
    apply h4
    rw [ha]; rfl
  have hsec : sec x = sec 1 := by
    have := (GlobalTheory.FinEt.comp_eq_comp_iff_range fx f1 (𝟙 _)).mpr (by
      rintro _ ⟨t, rfl⟩; exact hpt _)
    simpa [fx, f1] using this
  ext1
  rw [← sec_fst x, hsec, sec_fst]

end GlobalTheory.TorsionRigid
