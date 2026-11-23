import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocallyIffAffineEtalePointCoverStatement

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.locFinGeo_of :
    LocFinAff → LocFinGeo := by
  intro hA W V U π r _ _ _
  rw [GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover U (fun V' g ↦ ∃ s, s ≫ π = pullback.fst r g)]
  swap
  · rintro V' W' g k ⟨s, hs⟩
    refine ⟨pullback.lift (pullback.fst r (k ≫ g)) (pullback.snd r (k ≫ g) ≫ k)
      (by simp [pullback.condition]) ≫ s, ?_⟩
    rw [Category.assoc, hs, pullback.lift_fst]
  intro x
  obtain ⟨y, hy⟩ := U.affineCover.covers x
  set ι := U.affineCover.f (U.affineCover.idx x) with hι
  obtain ⟨U', g, hU', hg, ⟨z, hz⟩, s, hs⟩ :=
    hA (pullback.snd π (pullback.fst r ι)) (pullback.snd r ι) y
  refine ⟨U', g ≫ ι, hU', inferInstance, ⟨z, by simp [hz, hy]⟩, ?_⟩
  let φ : pullback r (g ≫ ι) ⟶ pullback (pullback.snd r ι) g :=
    pullback.lift (pullback.lift (pullback.fst r (g ≫ ι)) (pullback.snd r (g ≫ ι) ≫ g)
      (by rw [Category.assoc, ← pullback.condition]))
      (pullback.snd r (g ≫ ι)) (pullback.lift_snd _ _ _)
  refine ⟨φ ≫ s ≫ pullback.fst π (pullback.fst r ι), ?_⟩
  rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc s, hs]
  simp only [φ]
  rw [pullback.lift_fst_assoc, pullback.lift_fst]
