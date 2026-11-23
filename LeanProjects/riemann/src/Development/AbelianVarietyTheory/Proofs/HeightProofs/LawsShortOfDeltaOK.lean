import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SameSpaceOfLawsJ
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin

theorem laws_short_of_deltaOK : ∀ (D : D7) (J : CoreJ D) (T : Top D), LawsJ J → LawsP T → T.toCore = J.toCore → 0 ∉ D.host.levelPrimes → ∀ (p : ℕ) (I : Ideal (𝓞 D.host.E)), (p = D.host.pde ∨ p = D.host.pde') → ∀ dd : ∀ j n, DeltaDat (T.Q.Xo j) T.Q.c n, (∀ j, InR D j → ∀ n, DeltaOK (dd j n) p I) → LawsP ({ T with dδ := dd } : Top D) ∧ LawsSh ({ T with dδ := dd } : Top D) := by
  intro D J T hJ h hT h0 p I hp dd hd
  have h' : LawsP ({ T with dδ := dd } : Top D) := { h with }
  have hb : 0 < badN D := by
    have := D.host.qd_big
    unfold badN
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos D.host.QS_pos (by omega)) (by omega))
      (Finset.prod_pos fun x hx => Nat.pos_of_ne_zero fun h => h0 (h ▸ hx))
  refine ⟨h', GlobalTheory.ShortLaws.lawsSh_of_pinned GlobalTheory.chartIndependence_unconditional _ h' hb
    (GlobalTheory.ShortLaws.sameSpace_of_lawsJ J T hJ hT) p hp fun j hj n => ?_⟩
  obtain ⟨⟨h1, -, h3, h4, h5⟩, ⟨h6, h7⟩, h8⟩ := hd j hj n
  exact ⟨h1, h3, h4, h5, h6, h7, h8⟩

end GlobalTheory.FinalJoin
