import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.LemmaOneSevenOfFiniteOrder
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.CMFieldLemmas
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.PairwiseIndependenceComplementHolds
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FinOrdAd

namespace Formalism.MainNotions.Ext

theorem finOrdG_holds : FinOrdG := finite_order_adelic

end Formalism.MainNotions.Ext

namespace Formalism.MainNotions.UnusedSlot33

theorem division_rational_lattice (D : Formalism.BasicNotions.D7) : division_rows_rational_lattice D :=
  finiteModel_of_heckeEstimate D (finite_order_of_totally_real Formalism.MainNotions.Ext.finOrdG_holds D)

theorem family_finite_order_holds {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : ∀ x : ℝ, Fm.x1 < x → ∀ i : Fm.Ix x, division_rows_rational_lattice (Fm.D x i) :=
  fun x _ i => division_rational_lattice (Fm.D x i)

end Formalism.MainNotions.UnusedSlot33
