import Development.WeilBound.CoreStatements.VolumeEquality.DegPushAsm
import Development.WeilBound.CoreStatements.VolumeEquality.DegPushDim
import Development.WeilBound.CoreStatements.VolumeEquality.DegPushPullB
import Development.WeilBound.CoreStatements.VolumeEquality.DegPushUnit
import Development.WeilBound.CoreStatements.VolumeEquality.DegPushNumEq
import Development.WeilBound.CoreStatements.VolumeEquality.DegPushMap
import Development.WeilBound.CoreStatements.VolumeEquality.DegPushPF
import Development.WeilBound.CoreStatements.VolumeEquality.DegPushFib
import Development.WeilBound.CoreStatements.VolumeEquality.DegPushTest
import Development.WeilBound.CoreStatements.VolumeEquality.DegPushMass
import Development.WeilBound.CoreStatements.VolumeEquality.DegPushCentre
import Development.WeilBound.CoreStatements.VolumeEquality.DegPushJoin
import Development.WeilBound.CoreStatements.VolumeEquality.DegPushLat
import Development.WeilBound.CoreStatements.VolumeEquality.DegPushFibLink
import Development.WeilBound.CoreStatements.VolumeEquality.DegPushMuLink

namespace SheetDecomposition

theorem degPush : DegPush :=
  have hEq : NumEq := numEq ptDim numPull (unitZero ptDim)
  degPush_of hEq (geoPF ptDim) (fibNum hEq) trdegU testRelabel geoTest numMap muMass fieldJoin genIso
    (fibLink chartVal centre coordLat) (muLink chartVal centre coordLat)

end SheetDecomposition
