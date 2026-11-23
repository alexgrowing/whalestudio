import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectiveSpaceMapOfModelHasDivStatement
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjectiveRepresentationPullbackCoordinates
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjCoordRepresentationGeometricFibreSpanning
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SiegTh.CrdMapBC

open GlobalTheory.ProjSpace GlobalTheory.Cartier GlobalTheory.QCoh.Qcqs

theorem secMaps_baseChangeIso {o k : Type} [CommRing o] [CommRing k] (β : o →+* k) (n : ℕ) (j : Fin (n + 1)) :
    SecMaps (baseChangeIso n β) (secPull (coord o n j) (baseChange n β)) (coord k n j) := by
  rintro ⟨i, l⟩
  refine (baseChangeIso_coord n β j i l).trans ?_
  congr 1

theorem pCrd_comp_baseChange {o k A : Type} [CommRing o] [CommRing k] [CommRing A] (β : o →+* k) {n : ℕ}
    (x : Sp A ⟶ PSpace k n) (v : Fin (n + 1) → A) (h : PCrd x v) : PCrd (x ≫ baseChange n β) v := by
  refine (RepBC.secCoord_pull (O1 o n) (coord o n) (baseChange n β) x v).1 ?_
  exact (FibreEmbed.secCoord_iff_of_secMaps (LB.isLB_pull (O1_isLB o n) _) (O1_isLB k n)
    (w := baseChangeIso n β) (fun j => secMaps_baseChangeIso β n j)
    (iSup_nonzeroLocus_secPull (iSup_nonzeroLocus_coord o n) _) (iSup_nonzeroLocus_coord k n)).2 h

theorem exists_map_of_hasDiv : ∀ (k Ω o : Type) [CommRing k] [Field Ω] [Algebra k Ω] [CommRing o] (β : o →+* k) (M : RatModel k Ω) (n : ℕ) (c : Fin (n + 1) → Ω), M.HasDiv c → ∃ h : M.Z ⟶ PSpace o n, h ≫ PSpace.str o n = M.s ≫ spMap β ∧ PCrd (M.pt ≫ h) c := by
  intro k Ω o _ _ _ _ β M n c hc
  obtain ⟨h₀, hs, hp⟩ := GlobalTheory.T.exists_projectiveSpace_map_of_model_hasDiv k Ω M n c hc
  refine ⟨h₀ ≫ baseChange n β, ?_, ?_⟩
  · rw [Category.assoc, baseChange_str, ← Category.assoc, hs]
  · rw [← Category.assoc]
    exact pCrd_comp_baseChange β _ c hp

end GlobalTheory.SiegTh.CrdMapBC
