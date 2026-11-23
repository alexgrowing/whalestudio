import Formalism.SharpRestriction.GlobalSchurBounds.AdmittedWeylDimension
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeWeylDS

noncomputable section

namespace Formalism.MainNotions.Ext.Lw

theorem weyl_dimension_formula_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.StandardLattice.AdmittedWeylDimension D := by
  intro k u H _ _ π hHC
  obtain ⟨_, _, hU, hK⟩ := hHC
  have hU' : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k)) π :=
    ReciprocityTheory.ChartRestriction.DS.HW.hw_isURepOn_mono (ReciprocityTheory.ChartRestriction.DS.HW.hw_kset_subset _) hU
  have h := weylForU_closed k (Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos k) u) H π ⊤ hU' hK
  rw [finrank_top] at h
  rw [h]
  unfold Formalism.MainNotions.StandardLattice.dimV Formalism.MainNotions.StandardLattice.facProd Formalism.MainNotions.StandardLattice.vand
  congr 1
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => ?_
  simp only [Formalism.QuantumDeterminants.lowK, Pi.add_apply, Pi.sub_apply, ReciprocityTheory.ChartRestriction.DS.HW.hw_rhoN_allPos,
    ReciprocityTheory.ChartRestriction.DS.HW.hw_rhoC_allPos]
  ring

end Formalism.MainNotions.Ext.Lw
