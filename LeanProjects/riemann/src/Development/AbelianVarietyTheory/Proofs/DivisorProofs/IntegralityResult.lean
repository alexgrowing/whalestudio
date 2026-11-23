import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule

set_option autoImplicit false

noncomputable section

open GlobalTheory.HalfGeo
open Formalism.MainNotions.DIV.Cons (intO)
open scoped NNReal

namespace GlobalTheory.HalfGeo.IntProof

theorem intO_eq (p : ℕ) [Fact p.Prime] : intO ℂ_[p] = (𝓞_ℂ_[p]).toSubring :=
  Subring.ext fun a => (GlobalTheory.PadicComplexHost.mem_iff_norm p a).symm

theorem intSt : IntSt := by
  intro p _
  rw [intO_eq p]
  haveI : HenselianLocalRing 𝓞_ℂ_[p] := GlobalTheory.henselianLocalRing_of_valuationRing_of_isAlgClosed _ ℂ_[p]
  exact ⟨GlobalTheory.PadicComplexHost.not_isUnit_p p, GlobalTheory.PadicComplexHost.isAdicComplete p, inferInstance,
    PadicComplexInt.integers p, ⟨GlobalTheory.HTLat.padicIntHom p⟩⟩

end GlobalTheory.HalfGeo.IntProof
