import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootOfUnityEtaleLocallyPowPrimitiveRoot
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootOfUnity_etaleLocally_pow_primitiveRoot : ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ ω : (Γ(U, ⊤))ˣ, ω ^ q = 1 →
    Loc U fun V g => ∃ (ζ : Prim q Γ(V, ⊤)) (a : ℕ), (Units.map g.appTop.hom.toMonoidHom ω : Γ(V, ⊤)) = ζ.1 ^ a := by
  first | (exact @GlobalTheory.EtC.RootLoc.root_loc_pow_prim) | (exact GlobalTheory.EtC.RootLoc.root_loc_pow_prim) | (intros; apply GlobalTheory.EtC.RootLoc.root_loc_pow_prim <;> assumption)
