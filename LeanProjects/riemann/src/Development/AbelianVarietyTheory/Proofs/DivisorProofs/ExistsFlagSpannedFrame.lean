import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniREqUni
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProjectionSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleGluesFromCover

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

namespace GlobalTheory.FlagCell

theorem freeMap_app_freeFrame {X : Scheme.{0}} {I J : Type} (f : I → J) (i : I) :
    Scheme.Modules.Hom.app (M := GlobalTheory.QCoh.freeModule X I) (N := GlobalTheory.QCoh.freeModule X J)
      (SheafOfModules.freeMap (R := X.ringCatSheaf) f) ⊤ (freeFrame X I i) = freeFrame X J (f i) := by
  refine (GlobalTheory.QCoh.app_app (M := structureModule X) (N := GlobalTheory.QCoh.freeModule X I)
    (P := GlobalTheory.QCoh.freeModule X J) (SheafOfModules.ιFree i) (SheafOfModules.freeMap f) ⊤ (show Γ(structureModule X, ⊤) from (1 : Γ(X, ⊤)))).trans ?_
  unfold freeFrame
  congr 2
  exact congrArg (fun φ => Scheme.Modules.Hom.app φ ⊤) (SheafOfModules.ιFree_freeMap (R := X.ringCatSheaf) f i)

theorem exists_flag_spans_of_frame : ∀ (X : Scheme.{0}) (F : X.Modules) (m : ℕ) (v : Fin m → Γ(F, ⊤)),
    IsFrame v → ∃ fl : Vert.Flag F m, Spans fl ⊤ v := by
  intro X F m v hv
  refine ⟨(GlobalTheory.FlagSurj.freeFlag X m).ofIso ((isFrame_freeFrame X (Fin m)).iso hv), fun l => ?_⟩
  refine ⟨freeFrame X (Fin l), isFrame_freeFrame X (Fin l), fun j => ?_⟩
  refine (GlobalTheory.QCoh.app_app (M := GlobalTheory.QCoh.freeModule X (Fin l)) (N := GlobalTheory.QCoh.freeModule X (Fin m)) (P := F)
    (SheafOfModules.freeMap (R := X.ringCatSheaf) (Fin.castLE (Nat.lt_succ_iff.mp l.2)))
    ((isFrame_freeFrame X (Fin m)).iso hv).hom ⊤ (freeFrame X (Fin l) j)).symm.trans ?_
  rw [freeMap_app_freeFrame, IsFrame.iso_hom_app]

end GlobalTheory.FlagCell
