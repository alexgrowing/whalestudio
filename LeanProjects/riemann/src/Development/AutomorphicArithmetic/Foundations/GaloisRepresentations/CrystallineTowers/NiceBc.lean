import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.LocTower
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory.GalV (HTower)
open UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.Seam

private theorem fEt_of_isPullback {P Y Z' Z : Scheme.{0}} {v : P ⟶ Y} {s' : P ⟶ Z'} {s : Y ⟶ Z} {g : Z' ⟶ Z} {d : ℕ}
    (h : IsPullback v s' s g) (hs : FEt s d) : FEt s' d := by
  refine ⟨MorphismProperty.of_isPullback (P := @IsFinite) h hs.1,
    MorphismProperty.of_isPullback (P := @Etale) h hs.2.1, ?_⟩
  intro K _ _ x
  rw [← hs.2.2 K (x ≫ g)]
  refine Nat.card_congr
    { toFun := fun y => ⟨y.1 ≫ v, by rw [Category.assoc, h.w, ← Category.assoc, y.2]⟩
      invFun := fun y => ⟨h.lift y.1 x (by rw [y.2]), h.lift_snd _ _ _⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro y
    apply Subtype.ext
    apply h.hom_ext
    · simp
    · simp [y.2]
  · intro y
    apply Subtype.ext
    simp

private theorem isPullback_sΩ {k : Type} [Field k] (H : HTower k) (K : Type) [Field K] [Algebra k K] (g : H.Γ) :
    IsPullback (pullback.fst (H.s g ≫ H.q) (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (H.sΩ K g) (H.s g)
      (pullback.fst H.q (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  have hfst : H.sΩ K g ≫ pullback.fst H.q (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      pullback.fst (H.s g ≫ H.q) (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≫ H.s g :=
    pullback.lift_fst _ _ _
  have hsnd : H.sΩ K g ≫ pullback.snd H.q (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      pullback.snd (H.s g ≫ H.q) (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    pullback.lift_snd _ _ _
  refine IsPullback.of_bot (v₂₁ := pullback.snd H.q (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (v₂₂ := H.q)
    (h₃₁ := Spec.map (CommRingCat.ofHom (algebraMap k K))) ?_ hfst.symm (IsPullback.of_hasPullback _ _)
  rw [hsnd]
  exact IsPullback.of_hasPullback _ _

theorem niceBc : NiceBc := by
  intro k K _ _ τ H hN
  obtain ⟨hsm, hproj, hfet⟩ := hN
  letI : Algebra k K := τ.toAlgebra
  unfold bcAlong
  refine ⟨?_, ?_, ?_⟩
  · haveI := hsm
    show Smooth (pullback.snd H.q (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    infer_instance
  · exact GlobalTheory.ProjSpace.isProjOver_pullback_snd (algebraMap k K) hproj
  · intro g
    obtain ⟨d, hd⟩ := hfet g
    exact ⟨d, fEt_of_isPullback (isPullback_sΩ H K g) hd⟩

end UpperTheory.Gal.Seam

end
