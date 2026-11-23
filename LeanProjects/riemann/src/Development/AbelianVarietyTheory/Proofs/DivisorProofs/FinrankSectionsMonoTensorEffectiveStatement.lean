import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankSectionsMonoTensorEffective
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FracIdExistsTotPos
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianVarietyTorsionCardEqPowProof
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPw
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FiniteMonotoneGrowth
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankSecPullSandwich
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankEqCardKernelPointsOfEtale
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfQuasiAffine
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
open GlobalTheory.AbLaw GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_sections_mono_tensor_effective : ∀ {K : Type} [Field K] {Y : Scheme.{0}} [IsIntegral Y] (f : Y ⟶ Spec (CommRingCat.of K)) {L D : LB Y}, L.IsLB → D.IsLB → ∀ (s : LB.Sec D) {x : Y}, x ∈ Out.nonzeroLocus s → Module.Finite K (SecOnR f (tens L D) ⊤) → Module.Finite K (SecOnR f L ⊤) ∧ Module.finrank K (SecOnR f L ⊤) ≤ Module.finrank K (SecOnR f (tens L D) ⊤) := by
  first | exact @GlobalTheory.TensMul.finite_finrank_le_tens | exact GlobalTheory.TensMul.finite_finrank_le_tens | (intros; apply GlobalTheory.TensMul.finite_finrank_le_tens <;> assumption)
