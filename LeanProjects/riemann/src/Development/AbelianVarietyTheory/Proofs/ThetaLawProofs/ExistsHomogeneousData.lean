import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusConstMul

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.KeyHomogInhab

theorem exists_homogeneous_data : ∀ (K : Type) [Field K] (x : KeyIn K), ∀ (a : K) (M : Matrix (Fin x.P.g) (Fin x.P.g) K), a ≠ 0 → M.det ≠ 0 → ∃ (th' : x.P.L.Sec) (_ : ∀ s : Sp K, ∃ y : x.P.A.left, x.P.A.hom y = s ∧ y ∈ Out.nonzeroLocus th') (v' : Fin x.P.g → (epsR K ⟶ x.P.A)), IsLieBasis v' ∧ (∀ i, LB.Sec.f th' i = constFn x.P.A.hom _ a * LB.Sec.f x.th i) ∧ ∀ i, IsLieComb (M i) x.v (v' i) := by
  intro K _ x a M ha hM
  have := x.P.isAb.comm
  obtain ⟨e₁, -, -, -, e₅⟩ := LieComb.lieComb_algebra K x.P.A x.P.g x.v x.basis.1
  choose v' hv' using fun i => (e₁ (M i)).exists
  refine ⟨KeyNormalExists.constMul x.P.A.hom a x.th, fun s => ?_, v', (e₅ M v' x.basis hv').2 hM.isUnit,
    fun _ => rfl, hv'⟩
  obtain ⟨z, hz, hz'⟩ := x.th_ne s
  exact ⟨z, hz, KeyNormalExists.mem_nonzeroLocus_constMul _ ha.isUnit _ hz'⟩

end GlobalTheory.KeyHomogInhab
