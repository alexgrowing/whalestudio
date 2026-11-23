import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Imports
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

theorem norm_isHomogeneous_poly_coords :
    ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L],
      ∃ f : MvPolynomial (Fin (Module.finrank K L)) K, f.IsHomogeneous (Module.finrank K L) ∧
        ∀ x : L, Algebra.norm K x =
          MvPolynomial.eval (fun i => (Module.finBasis K L).repr x i) f := by
  first
  | exact @_root_.GlobalTheory.IdealPowerMembership.main
  | exact _root_.GlobalTheory.IdealPowerMembership.main
  | (apply _root_.GlobalTheory.IdealPowerMembership.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IdealPowerMembership.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IdealPowerMembership.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IdealPowerMembership.main ..)

end GlobalTheory
