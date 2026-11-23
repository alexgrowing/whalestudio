import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleToSheafifyLocallyBijectiveAndLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistModuleFreeAndGeneratorSummandStatement

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in

theorem _root_.GlobalTheory.EtC.flatS_tw : ∀ (q : ℕ) [NeZero q] (i : ℤ),
    _root_.GlobalTheory.EtC.FlatS (_root_.GlobalTheory.EtC.tw q i) := by
  intro q _ i
  obtain ⟨h1, h2, -⟩ := _root_.GlobalTheory.EtC.toSheafify_loc_bij_lift (ZMod q)
    (Scheme.Γ ⋙ _root_.GlobalTheory.EtC.twF q i)
  refine ⟨_, toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ _root_.GlobalTheory.EtC.twF q i), h1, h2,
    fun U hU => ?_⟩
  obtain ⟨x⟩ := hU
  haveI : Nontrivial Γ(U, ⊤) := (U.presheaf.germ ⊤ x trivial).hom.domain_nontrivial
  haveI := (_root_.GlobalTheory.TwFree.twist_free q i Γ(U, ⊤)).1
  change Module.Flat (ULift.{1} (ZMod q))
    ((_root_.GlobalTheory.EtC.Prim q Γ(U, ⊤) →₀ ULift.{1} (ZMod q)) ⧸
      _root_.GlobalTheory.EtC.twRel q i Γ(U, ⊤))
  infer_instance

end GlobalTheory.EtC
