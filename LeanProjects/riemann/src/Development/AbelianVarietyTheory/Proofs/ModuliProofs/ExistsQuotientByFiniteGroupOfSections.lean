import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientByFiniteGroupOfPoints
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

noncomputable section

namespace GlobalTheory

namespace SectionQuot

open PointQuot

variable {S : Scheme.{0}}

lemma exists_geomPt (Z : Over S) (z : Z.left) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (t : Sp k ⟶ S), Nonempty (Over.mk t ⟶ Z) := by
  let k := AlgebraicClosure (Z.left.residueField z)
  let p : Sp k ⟶ Z.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (Z.left.residueField z) k)) ≫
      Z.left.fromSpecResidueField z
  exact ⟨k, inferInstance, inferInstance, p ≫ Z.hom, ⟨Over.homMk p rfl⟩⟩

lemma mono_constDesc_of_geom {I : Type} {A : Over S} (x : I → (𝟙_ (Over S) ⟶ A))
    (hx : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S) (c d : I),
      toUnit (Over.mk t) ≫ x c = toUnit (Over.mk t) ≫ x d → c = d) : Mono (constDesc x) := by
  refine ⟨fun {Z} f g h => hom_ext_local f g fun z => ?_⟩
  obtain ⟨V, hV, c, hc⟩ := locally_const f z
  obtain ⟨W, hW, d, hd⟩ := locally_const g z
  have hc' := const_of_le (inf_le_left : V ⊓ W ≤ V) hc
  have hd' := const_of_le (inf_le_right : V ⊓ W ≤ W) hd
  obtain ⟨k, _, _, t, ⟨p⟩⟩ :=
    exists_geomPt (openObj Z (V ⊓ W)) (⟨z, hV, hW⟩ : (V ⊓ W : Z.left.Opens))
  obtain rfl : c = d := by
    apply hx k t
    rw [toUnit_unique (toUnit _) (p ≫ toUnit _), Category.assoc, Category.assoc,
      ← constPt_desc x c, ← constPt_desc x d, ← reassoc_of% hc', ← reassoc_of% hd', h]
  exact ⟨V ⊓ W, ⟨hV, hW⟩, hc'.trans hd'.symm⟩

end SectionQuot

open PointQuot SectionQuot in

theorem exists_quotient_by_finite_group_of_sections :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : Out.PolAV (Sp R)) (C : Type) [CommGroup C] [Finite C] (i : C →* (𝟙_ (Over (Sp R)) ⟶ P.A)), (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (c : C), toUnit (Over.mk t) ≫ i c = 1 → c = 1) → ∃ (B : Over (Sp R)) (_ : GrpObj B) (ψ : P.A ⟶ B), IsAbelianScheme B ∧ IsMonHom ψ ∧ IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left ∧ (∀ c, i c ≫ ψ = 1) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (x : Over.mk t ⟶ P.A), x ≫ ψ = 1 ↔ ∃ c, x = toUnit _ ≫ i c := by
  intro R _ _ P C _ _ i hi
  have L : Out.Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin C
  let x : Fin n → (𝟙_ (Over (Sp R)) ⟶ P.A) := fun c => i (e.symm c)
  have hr : Set.range x = i.range := by
    ext y
    exact ⟨by rintro ⟨c, rfl⟩; exact ⟨e.symm c, rfl⟩,
      by rintro ⟨c, rfl⟩; exact ⟨e c, by simp [x]⟩⟩
  have hmono : Mono (constDesc x) := mono_constDesc_of_geom x fun k _ _ t c d h => by
    apply e.symm.injective
    rw [← div_eq_one]
    apply hi k t
    rw [map_div, GrpObj.comp_div, div_eq_one]
    exact h
  obtain ⟨_, hhom⟩ := exists_grpObj_constObj x i.range hr
  have hs : FinEt.IsSplitOfRank (constObj (Sp R) (Fin n)).hom n :=
    (FinEt.isSplitOfRank_iff_exists_iso _ _).mpr ⟨Iso.refl _, Category.id_comp _⟩
  have het := hs.etale
  obtain ⟨B, _, hB, q, hq, hfin, hflat, hsurj, hker⟩ :=
    L.quotient R P (constObj (Sp R) (Fin n)) (constDesc x) hhom hmono hs.isFinite inferInstance
  have hw : constDesc x ≫ q = 1 := hker.w
  have hkill : ∀ c, i c ≫ q = 1 := fun c => by
    have : i c = x (e c) := by simp [x]
    rw [this, ← constPt_desc x (e c), Category.assoc, hw, MonObj.comp_one]
  refine ⟨B, inferInstance, q, hB, hq, hfin, ?_, hsurj, hkill,
    fun k _ _ t y => ⟨fun hy => ?_, ?_⟩⟩
  · refine MorphismProperty.of_isPullback_of_descendsAlong (P := @Etale)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      ((H1.torsor_pullback (constDesc x) q hker).map (Over.forget _)).flip
      ⟨⟨hsurj, hflat⟩, inferInstanceAs (QuasiCompact q.left)⟩ ?_
    exact MorphismProperty.of_isPullback (P := @Etale) (IsPullback.of_hasPullback _ _) het
  · obtain ⟨z⟩ : Nonempty (Over.mk t).left := inferInstanceAs (Nonempty (PrimeSpectrum k))
    have : Subsingleton (Over.mk t).left := inferInstanceAs (Subsingleton (PrimeSpectrum k))
    obtain ⟨V, hV, c, hc⟩ := locally_const_desc x (hker.lift y (toUnit _) hy) z
    rw [hker.lift_fst] at hc
    refine ⟨e.symm c, hom_ext_local _ _ fun z' => ⟨V, Subsingleton.elim z z' ▸ hV, ?_⟩⟩
    rw [hc, ← Category.assoc, toUnit_unique (_ ≫ toUnit _) (toUnit _)]
  · rintro ⟨c, rfl⟩
    rw [Category.assoc, hkill, MonObj.comp_one]

end GlobalTheory
