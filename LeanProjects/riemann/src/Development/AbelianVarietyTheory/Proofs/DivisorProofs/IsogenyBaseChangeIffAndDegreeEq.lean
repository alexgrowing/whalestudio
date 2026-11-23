import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFlatFinrankStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleSurjectiveLevelMap
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem bcMap_isPullback (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] {A B : AbVar K} (f : A ⟶ B) :
    IsPullback (pullback.fst A.X.hom (spMap (algebraMap K L))) (bcMap L f).hom.left f.hom.left
      (pullback.fst B.X.hom (spMap (algebraMap K L))) := by
  have h1 : ((Over.pullback (spMap (algebraMap K L))).map f.hom).left ≫ pullback.snd B.X.hom (spMap (algebraMap K L)) =
      pullback.snd A.X.hom (spMap (algebraMap K L)) :=
    Over.w ((Over.pullback (spMap (algebraMap K L))).map f.hom)
  have h3 : ((Over.pullback (spMap (algebraMap K L))).map f.hom).left ≫ pullback.fst B.X.hom (spMap (algebraMap K L)) =
      pullback.fst A.X.hom (spMap (algebraMap K L)) ≫ f.hom.left :=
    pullback.lift_fst _ _ _
  have h2 : f.hom.left ≫ B.X.hom = A.X.hom := Over.w f.hom
  have hout : IsPullback (pullback.fst A.X.hom (spMap (algebraMap K L)))
      (((Over.pullback (spMap (algebraMap K L))).map f.hom).left ≫ pullback.snd B.X.hom (spMap (algebraMap K L)))
      (f.hom.left ≫ B.X.hom) (spMap (algebraMap K L)) := by
    rw [h1, h2]
    exact IsPullback.of_hasPullback A.X.hom (spMap (algebraMap K L))
  exact IsPullback.of_bot hout h3.symm (IsPullback.of_hasPullback B.X.hom (spMap (algebraMap K L)))

theorem isIsogeny_bcMap_iff_and_deg_bcMap : ∀ (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] (A B : AbVar K)
    (f : A ⟶ B), (IsIsogeny (bcMap L f) ↔ IsIsogeny f) ∧ deg (bcMap L f) = deg f := by
  intro K _ L _ _ A B f
  have := GlobalTheory.LevelMap.isFinite_descendsAlong_fpqc
  have sq := bcMap_isPullback K L f
  have hB := IsPullback.of_hasPullback B.X.hom (spMap (algebraMap K L))
  have hs : Surjective (spMap (algebraMap K L)) := GlobalTheory.LevelMap.surjective_spMap _
  have hf : Flat (spMap (algebraMap K L)) := GlobalTheory.LevelMap.flat_spMap _
  have hq : QuasiCompact (spMap (algebraMap K L)) := by unfold spMap; infer_instance
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) (pullback.fst B.X.hom (spMap (algebraMap K L))) :=
by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact MorphismProperty.of_isPullback (P := @Surjective) hB.flip hs
    · exact MorphismProperty.of_isPullback (P := @Flat) hB.flip hf
    · exact MorphismProperty.of_isPullback (P := @QuasiCompact) hB.flip hq
  have hiso : IsIsogeny (bcMap L f) ↔ IsIsogeny f :=
    and_congr (MorphismProperty.iff_of_isPullback (P := @IsFinite) sq.flip hQ)
      (MorphismProperty.iff_of_isPullback (P := @Surjective) sq.flip hQ)
  refine ⟨hiso, ?_⟩
  by_cases h : IsIsogeny f
  · obtain ⟨-, hfl, -, hrk⟩ := GlobalTheory.T.dim_eq_flat_finrank_eq_deg_of_isIsogeny K A B f h
    have : IsFinite f.hom.left := h.1
    have e : deg (bcMap L f) = (bcMap L f).hom.left.finrank (baseChange L B).origin := if_pos (hiso.2 h)
    rw [e]
    exact (Scheme.Hom.finrank_of_isPullback _ _ _ _ sq (baseChange L B).origin).trans (hrk _)
  · have e1 : deg (bcMap L f) = 0 := if_neg (fun h' => h (hiso.1 h'))
    have e2 : deg f = 0 := if_neg h
    rw [e1, e2]

end GlobalTheory.AV.AbVar
