import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassNumberDvdFinrank
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeNormOfKummer
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classNumber_dvd_finrank_alt : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (𝔮 : Ideal (𝓞 K)), 𝔮 ≠ ⊥ → IsRayField K L 𝔮 → classNumber K ∣ Module.finrank K L := by
  first | exact @GlobalTheory.Mem.ClassDvd.classNumber_dvd_finrank | exact GlobalTheory.Mem.ClassDvd.classNumber_dvd_finrank | (intros; apply GlobalTheory.Mem.ClassDvd.classNumber_dvd_finrank <;> assumption)
