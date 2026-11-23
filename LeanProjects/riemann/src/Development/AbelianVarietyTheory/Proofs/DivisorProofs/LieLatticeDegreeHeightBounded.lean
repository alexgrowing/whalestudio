import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiFibrationLieLatticeFullStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepLatZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiFibLieLatticeFull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianDegreeAdelicSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaHeightAdelicSumBound
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LieRead

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieRead

theorem deg_lieLat_add_omHt_le : Hypotheses2 → HypothesesH → OnObj fun D O _ _ H _ => ∃ C : ℝ, ∀ y : Pt O.s, y ∈ H.int → ∀ (K : Type) [Field K] [NumberField K] (F : SemiFib K) (ι : K →+* Qb) (h : HermFam K (Fin F.P₀.g → K)), FibTie O y F ι → F.IsHerm h → |deg h F.lieLat + omHt O O.met.hm y| ≤ C := by
  intro p2 pH D O hO hf A T H hR
  obtain ⟨C, hC⟩ := GlobalTheory.T.omega_height_adelic_sum_bound p2 pH D O hO hf A T H hR
  refine ⟨C, fun y hy K _ _ F ι h hT hH => ?_⟩
  have e := GlobalTheory.T.hermitian_degree_adelic_sum K F.P₀.g F.lieLat h (SemiFib.full_lieLat K F)
  have := hC y hy K F ι h hT hH
  rw [e]
  convert this using 2
  ring

end GlobalTheory.LieRead

end
