import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkEquivInl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKilled
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjInvariantApproxIdentityRealLieSmoothinStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameInvariantKilledSmoothSpaceCentreMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliDetEqLinearCombinationNatNodesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameKilledCapelliSpaceFiniteDimensionalOfFinitenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliKilledSlowlyIncreasingSmoothingMemStatement

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth Filter Topology

theorem GlobalTheory.CapKilled.finite_of_finiteness : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (b : ℕ),
    (∀ (L : Subgroup (GL (Fin b) (Af E))), IsOpen (L : Set (GL (Fin b) (Af E))) → ∀ W : Submodule ℂ (Kinf E b → ℂ),
      FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E b) → ℂ), X.Finite → ∀ N : ℕ,
        FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E b L W X N))) →
    ∀ (L : Subgroup (GL (Fin b) (Af E))), IsOpen (L : Set (GL (Fin b) (Af E))) → ∀ W : Submodule ℂ (Kinf E b → ℂ),
      FiniteDimensional ℂ W → ∀ q : (E →+* ℂ) → ℂ → Polynomial ℂ, (∀ τ u, q τ u ≠ 0) →
      ∃ V : Submodule ℂ (Sm E b), FiniteDimensional ℂ V ∧ ∀ ψ : Sm E b, (∀ γ g, ψ.1 (ratGL E b γ * g) = ψ.1 g) →
        (∀ k ∈ L, finRep E b k ψ = ψ) → (∀ g : GA E b, (fun k : Kinf E b => (cptRep E b k ψ).1 g) ∈ W) →
        (∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖ψ.1 (g * infGL E b y)‖ ≤ C * height y ^ N) →
        (∀ τ u, Polynomial.aeval (cap τ u) (q τ u) ψ = 0) → ψ ∈ V := by
  intro E _ _ _ b hP L hL W hW q hq
  have hfin : FiniteDimensional ℂ (GlobalTheory.CapKilled.space E b L W q) :=
    GlobalTheory.T.tameKilledCapelliSpace_finiteDimensional_of_finiteness E b hP (GlobalTheory.T.capelliDet_eq_linearCombination_nat_nodes E b) L hL W hW q hq (GlobalTheory.T.tameInvariantKilledSmoothSpace_centre_mem E b L W hW q)
  refine ⟨GlobalTheory.CapKilled.space E b L W q, hfin, fun ψ h1 h2 h3 h4 h5 => ?_⟩
  let ν : Measure (Lie E b) := Measure.addHaar
  obtain ⟨α, hα, hlim⟩ := GlobalTheory.T.exists_conjInvariant_approxIdentity_realLieSmoothing E b ν
  let V' : Submodule ℂ (GA E b → ℂ) := (GlobalTheory.CapKilled.space E b L W q).map (Sm E b).subtype
  have hc : IsClosed (V' : Set (GA E b → ℂ)) := Submodule.closed_of_finiteDimensional V'
  have hM : ψ ∈ leftInv E b ⊓ fixL E b L ⊓ GlobalTheory.CapKilled.ktype E b W ⊓ GlobalTheory.CapKilled.killed E b q :=
    ⟨⟨⟨h1, h2⟩, h3⟩, GlobalTheory.CapKilled.mem_killed.2 h5⟩
  have hmem : ∀ n, smoothing ν (α n) ψ.1 ∈ V' := fun n => by
    obtain ⟨h, hv⟩ := GlobalTheory.T.capelliKilled_slowlyIncreasing_smoothing_mem E b ν (α n) (hα n).1 (hα n).2 L W hW q ψ hM h4
    exact ⟨_, hv, rfl⟩
  have hψ : ψ.1 ∈ V' :=
    hc.mem_of_tendsto (tendsto_pi_nhds.2 fun g => hlim ψ.1 ψ.2 g) (Eventually.of_forall hmem)
  obtain ⟨χ, hχ, e⟩ := hψ
  have e' : χ = ψ := Subtype.ext e
  exact e' ▸ hχ

end
