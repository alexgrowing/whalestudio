import Development.EtaleCohomology.EtaleSheaves.ZeroSheafMaps.EtaleSheafMapZeroOfLocallyZeroOnFreeSheafGenerat

namespace LateralTheory.E.LeafShMapZeroPf.Glue
open LateralTheory.E.LeafDegCut LateralTheory.E.LeafShMapZeroPf LateralTheory.E.LeafShMapZeroPf.Gen

theorem LeafShMapZero_of (hA : EtaleLift') (hG : EtaleSheafMapZeroOfLocallyZeroOnFreeSheafGenerators) : LeafShMapZero :=
  LateralTheory.E.LeafShMapZeroPf.LeafShMapZero_of hA (LeafGen_of hG)

end LateralTheory.E.LeafShMapZeroPf.Glue
