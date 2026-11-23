import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleRepresentativesFiniteLevelCosets
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAdmissibleIntegralBasisChangeOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissibleRepresentatives_finite_level_cosets : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), ∃ (ι : Type) (_ : Finite ι) (f : AutY X R j → ι), ∀ h h' : AutY X R j, admitted Pr j P h → admitted Pr j P h' → f h = f h' → h⁻¹ * h' ∈ Jat (Pr := Pr) sharp j P := by
  first | exact @GlobalTheory.Mem.Col2.IdxFin.exists_finite_index_of_adm_cosets | exact GlobalTheory.Mem.Col2.IdxFin.exists_finite_index_of_adm_cosets | (intros; apply GlobalTheory.Mem.Col2.IdxFin.exists_finite_index_of_adm_cosets <;> assumption)
