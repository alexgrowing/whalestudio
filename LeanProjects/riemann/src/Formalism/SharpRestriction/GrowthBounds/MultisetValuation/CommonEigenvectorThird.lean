import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.TripleSumComm
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.BiadditiveSecondVariable
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.FrobeniusCongruenceWitt
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.SxMuAltInt

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

variable (p : ℕ) [hp : Fact p.Prime]

theorem restTwoSums : TwoSumsCondition p :=
  restTwoSums_of (p := p)
    (fun K' _ _ vp hvp μ h0 h1 n => sx_mu_alt (p := p) (K' := K') vp hvp μ h0 h1 n)
    (fun n' B hev a b hab => sx_dual (p := p) B hev a b hab)
    (fun n' r0 r1 K' _ R s x hx => sx_frob_sum (p := p) R s x hx)
    (fun a => frobenius_congruence_witt (p := p) a)

theorem restGc : RestGc p :=
  gcCondition_of_twoSums (p := p) (restTwoSums p)

variable {p}

theorem restGcA (X : Sys p) : RestGcA X :=
  restGcA_of (X := X) (restGc p)

theorem th_restGcV (X : Sys p) : ea_RestGcV X :=
  th_restGcV_of (X := X) (restGc p)

theorem theta_kernel_expansion (D : Formalism.BasicNotions.D7) (X : Sys p) (Y : Pend X) (hA : admitted D X Y) : Conclusion1 D X Y :=
  baseChange_preserves_unitary_of D X Y hA (restBeta p) (restGc p)

theorem expansions_multiply (D : Formalism.BasicNotions.D7) (X : Sys p) (Y : Pend X) (hA : admitted D X Y) : ExpansionsMultiply D X Y :=
  expansion_all_places_of_computation D X Y hA (restBeta p) (restGcA X)

end Formalism.MainNotions.FormalGroupSystem.Pf
