import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyHeckeCorrespondenceSchemeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsogenyPullbackHeckeModuliObjectStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeQuotientClassifyingMapIsogenyUniqueStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGeomPtRangeEq
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

theorem kerSet_of_isPullback {S : Scheme.{0}} {G G' C : Over S} [GrpObj G'] {ψ : G ⟶ G'} {j : C ⟶ G}
    [IsClosedImmersion j.left] (hP : IsPullback j (toUnit C) ψ η[G']) : KerSet ψ (Set.range j.left) := by
  intro k _ _ x z
  constructor
  · intro h
    have hl := hP.lift_fst z (toUnit _) h
    rintro _ ⟨a, rfl⟩
    exact ⟨(hP.lift z (toUnit _) h).left a, by rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hl]⟩
  · intro h
    have : IsReduced (Over.mk x).left := inferInstanceAs (IsReduced (Spec _))
    have h4 : j.left.ker ≤ z.left.ker := ker_le_ker_of_range_subset_of_isReduced _ _ h
    have h3 := IsClosedImmersion.lift_fac _ _ h4
    let l : Over.mk x ⟶ C := Over.homMk (IsClosedImmersion.lift _ _ h4) (by
      rw [← Over.w j, ← Category.assoc, h3, Over.w])
    have hl : l ≫ j = z := Over.OverMorphism.ext h3
    rw [← hl, Category.assoc, hP.w, ← Category.assoc, toUnit_unique (l ≫ _) (toUnit _)]
    rfl

theorem existsUnique_heckeQuot :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp (KA l)) (o : Ob D l s) (C : Over S) (j : C ⟶ o.t.G), 1 ≤ D.p + D.q → admitted l 𝔓 p → IsReduced S → IsFinite C.hom → Etale C.hom → IsClosedImmersion j.left → HeckeSet D o.t 𝔓 p i (Set.range j.left) → ∃! f : S ⟶ Xo.X, f ≫ Xo.s = s ∧ ∃ (o' : Ob D l s) (_ : ObjMap o' Xo.univ f) (ψ : o.t.G ⟶ o'.t.G), IsIsog o o' p ψ ∧ IsPullback j (toUnit C) ψ η[o'.t.G] := by
  intro E _ _ _ H D l Xo 𝔓 p i S s o C j hD hA hS hf he hj hK
  obtain ⟨Z⟩ := GlobalTheory.T.nonempty_heckeCorrespondenceScheme E H D l Xo 𝔓 p i hD hA
  obtain ⟨h, ⟨hs, n, hn⟩, -⟩ := Z.rep S s hS o (Set.range j.left) ⟨C, j, hf, he, hj, rfl⟩ hK
  have hid : spMap (RingHom.id (KA l)) = 𝟙 _ := Spec.map_id _
  obtain ⟨o', ⟨n'⟩⟩ := GlobalTheory.obj_pull E H D l (KA l) (KA l) (baseKA l) (baseKA l) (RingHom.id _) _ _
    (Z.π₁ ≫ Xo.s) s h rfl rfl (by rw [hid, Category.comp_id, hs]) Z.o₂
  obtain ⟨⟨ψ, hψ, -⟩, hall⟩ := GlobalTheory.T.exists_isogeny_pullback_heckeModuliObject E H D l p _ _ _ _ h Z.o₁ Z.o₂ o o' n n' Z.ψ
  obtain ⟨hi, hk⟩ := hall ψ hψ
  have hi := hi Z.isog
  have hk := hk Z.K Z.isog.1.1 Z.ker
  rw [← hn] at hk
  obtain ⟨m, -⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ Z.o₂ o').2 Z.π₂ h Z.m₂).1 n'
  have hfs : (h ≫ Z.π₂) ≫ Xo.s = s := by rw [Category.assoc, Z.base₂, hs]
  have := o'.proper
  refine ⟨h ≫ Z.π₂, ⟨hfs, o', m, ψ, hi, ?_⟩, ?_⟩
  · exact (etSet_of_kerSet S _ _ ψ _ inferInstance hi.1.2.1 hi.1.2.2.1 hk).2 hS C j he hj rfl
  · rintro f ⟨hf₁, o₁, m₁, ψ₁, hi₁, hP⟩
    exact (GlobalTheory.T.heckeQuotient_classifyingMap_isogeny_unique E H D l Xo 𝔓 p i S s o o₁ o' ψ₁ ψ _ f _ m₁ m hA hK hf₁ hfs hi₁ hi
      (kerSet_of_isPullback hP) hk).1

end GlobalTheory.HkFam
