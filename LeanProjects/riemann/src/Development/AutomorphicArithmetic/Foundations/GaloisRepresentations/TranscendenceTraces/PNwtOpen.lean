import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.nwtOpen_of :
    WtBC → MultBC → GenBasic → NwtOpen := by
  intro hw hm hg Z S p w A _ hp
  obtain ⟨hwt, hgen⟩ := hp
  refine ⟨hw A.v A.r p A.u w A.pb hwt, ?_⟩
  intro Ω _ _ z hz
  have hsq : (z ≫ A.v) ≫ p = (z ≫ A.r) ≫ A.u := by
    rw [Category.assoc, Category.assoc, A.pb.w]
  have hz' : GenPt (pt ((z ≫ A.v) ≫ p)) := by
    rw [hsq, pt_comp]
    exact (hg.2.1 A.u (pt (z ≫ A.r))).mpr hz
  rw [hm A.v A.r p A.u A.pb]
  exact hgen Ω (z ≫ A.v) hz'
