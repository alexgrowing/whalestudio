import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPrimeDegreeOne
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_prime_degree_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (W : HeightOneSpectrum (𝓞 E)), SplitsFully E (W.under (𝓞 F)) → ∃ p : ℕ, p.Prime ∧ Ideal.absNorm W.asIdeal = p ∧ (p : 𝓞 E) ∉ W.asIdeal ^ 2 := by
  first | exact @GlobalTheory.SplitFullyNorm.exists_prime_absNorm_eq_of_splitsFully | exact GlobalTheory.SplitFullyNorm.exists_prime_absNorm_eq_of_splitsFully | (intros; apply GlobalTheory.SplitFullyNorm.exists_prime_absNorm_eq_of_splitsFully <;> assumption)
