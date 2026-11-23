import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartHasComplexCoordinates

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem chainTie_and_v0Onto :
    ∀ (D : D7) (Bs : DefBase D.what₂.LL) (A : DefAmb Bs) (X : CxData A) (fc : DefSub A → DefFace Bs) (s : Bool)
      (R : Read D X fc s) (cr : Crd A fc) (M : Seam R cr), (R.DcPt → M.ChainTie) ∧ (R.ReadingFormsSpanGoodSubspace → M.GoodPartHasComplexCoordinates) := by
  intro D Bs A X fc s R cr M
  refine ⟨fun h u x y => ?_, fun h => ?_⟩
  · rw [M.cφ_eq, M.cF_eq]
    exact (h u x y).symm
  · unfold Seam.GoodPartHasComplexCoordinates
    rw [← h]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, rfl⟩
    exact ⟨_, M.cF_eq y⟩

end GlobalTheory.Mem.SJ
