import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DensityStandardVolumeFormProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppendVMemFamAtlasTarget
open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.CxForm GlobalTheory.BcUnique
open scoped ContDiff Real Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.density_standard_volume_form_product : ∀ a : Alt (1 + 1), dens (((Complex.I / 2) • (dz (Fin.last 1) * dzb (Fin.last 1))) * a) = dens (pull headIn a) := by
  first | exact @GlobalTheory.BcUnique.DensPull.dens_mul_eq_dens_pull | exact GlobalTheory.BcUnique.DensPull.dens_mul_eq_dens_pull | (intros; apply GlobalTheory.BcUnique.DensPull.dens_mul_eq_dens_pull <;> assumption)
