import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitsAdicCompletionHomExtOfIsOpenKer
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.units_adicCompletion_hom_ext_of_isOpen_ker : ∀ (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (B : Type) [Group B] (f g : (v.adicCompletion F)ˣ →* B), IsOpen (f.ker : Set (v.adicCompletion F)ˣ) → IsOpen (g.ker : Set (v.adicCompletion F)ˣ) → (∀ c : Fˣ, f (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom c) = g (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom c)) → ∀ x, f x = g x := by
  first | exact @GlobalTheory.units_adicCompletion_hom_ext | exact GlobalTheory.units_adicCompletion_hom_ext | (intros; apply GlobalTheory.units_adicCompletion_hom_ext <;> assumption)
