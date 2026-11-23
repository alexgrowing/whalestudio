import Development.EtaleCohomology.TateTwists.acycIffPf
import Development.EtaleCohomology.TateTwists.ColumnOf
import Development.EtaleCohomology.TateTwists.StepPf
import Development.EtaleCohomology.TateTwists.TensorVanishing
import Development.EtaleCohomology.TateTwists.acycPf
import Development.EtaleCohomology.TateTwists.conePf
import Development.EtaleCohomology.TateTwists.EtaleTensorPreservesQuasiIsoOfAcyclicAndCone

namespace LateralTheory.Fin.EtaleTensorPairQuasiIsoOfFlatQuasiIso
theorem etale_complex_acyclic_iff_local_exactness : LateralTheory.EtaleFoundations.acyc.acycIff := by
  apply LateralTheory.EtaleFoundations.acyc.acycIff_of
theorem etale_tensor_column_acyclic_of_flat : LateralTheory.EtaleFoundations.acyc.column := by
  apply LateralTheory.EtaleFoundations.acyc.column_of
theorem etale_tensor_staircase_lifting_inductive : LateralTheory.EtaleFoundations.stairPf.Step := by
  apply LateralTheory.EtaleFoundations.StepPf.Step_of
theorem etale_tensor_acyclic_of_staircase_lifting : LateralTheory.EtaleFoundations.acyc.stair := by
  apply LateralTheory.EtaleFoundations.acyc.stair_of <;> first | exact etale_tensor_staircase_lifting_inductive
theorem etale_tensor_acyclic_cone_of_flat : LateralTheory.EtaleFoundations.tqis.acyc := by
  apply LateralTheory.EtaleFoundations.tqis.acyc_of <;> first | exact etale_complex_acyclic_iff_local_exactness | exact etale_tensor_column_acyclic_of_flat | exact etale_tensor_acyclic_of_staircase_lifting
theorem etale_tensor_mappingCone_commutes : LateralTheory.EtaleFoundations.tqis.cone := by
  apply LateralTheory.EtaleFoundations.tqis.cone_of
theorem etale_tensor_quasiIso_of_acyclic_cone : LateralTheory.EtaleFoundations.EtaleTensorPairQuasiIsoOfFlatQuasiIso := by
  apply LateralTheory.EtaleFoundations.etale_tensor_preserves_quasiIso_of_acyclic_and_cone <;> first | exact etale_tensor_acyclic_cone_of_flat | exact etale_tensor_mappingCone_commutes
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleTensorPairQuasiIsoOfFlatQuasiIso := etale_tensor_quasiIso_of_acyclic_cone
end LateralTheory.Fin.EtaleTensorPairQuasiIsoOfFlatQuasiIso
