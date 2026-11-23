import Development.EtaleCohomology.EtaleSheaves.EtaleSpreading.FPProof

namespace LateralTheory.E.SpreadPf.Main

theorem Spread_of (hS : LateralTheory.E.SpreadPf.Cut.EtStage) : LateralTheory.E.DescendPf.Spread :=
  LateralTheory.E.SpreadPf.Cut.Spread_of LateralTheory.E.SpreadPf.FPProof.finite_presentation_ring_maps_pre_ind_spread hS

end LateralTheory.E.SpreadPf.Main
