import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalGaloisDataShaLengthEq
import Mathlib
import Formalism.GaloisCohomology.Statement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localGaloisData_shaLength_eq : ∀ {F Ω Ω' : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field Ω'] [Algebra F Ω'] [IsAlgClosure F Ω'] (l : ℕ) [Fact l.Prime] (D : Formalism.GaloisCohomology.LData F Ω l), ∃ D' : Formalism.GaloisCohomology.LData F Ω' l, ∀ e : ℤ, Formalism.GaloisCohomology.shaLen D' e = Formalism.GaloisCohomology.shaLen D e := by
  first | exact @GlobalTheory.ShaTransport.exists_lData_shaLen_eq | exact GlobalTheory.ShaTransport.exists_lData_shaLen_eq | (intros; apply GlobalTheory.ShaTransport.exists_lData_shaLen_eq <;> assumption)
