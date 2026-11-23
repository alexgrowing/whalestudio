import Formalism.CoboundaryTransfers.GammaStableTransfers.MemCoboundariesOfIsOneCoboundary
import Formalism.CoboundaryTransfers.GammaStableTransfers.GammaStableOfGammaQUnitHolds
import Formalism.CoboundaryTransfers.GammaStableTransfers.DiffOneSmulOfTower
import Formalism.CoboundaryTransfers.GammaStableTransfers.TorsionKilledCriterionHolds
import Formalism.CoboundaryTransfers.GammaStableTransfers.BridgeCL
import Formalism.CoboundaryTransfers.GammaStableTransfers.BridgeLIFT
import Formalism.CoboundaryTransfers.GammaStableTransfers.DepthPageFirstZetaFactorEqPrimePower
import Formalism.CoboundaryTransfers.GammaStableTransfers.Transfer
import Formalism.CoboundaryTransfers.GammaStableTransfers.WachLatticeNonemptyGamma
import Formalism.CoboundaryTransfers.GammaStableTransfers.IntegralWachDefinitions

noncomputable section

namespace Formalism.CoboundaryTransfers

theorem wach_api : Complex ∧ Submods ∧ CocZf ∧ HomMaps ∧ GammaQNOf ∧ DiagramChase₂ ∧ CoboundaryTransfer ∧
    GradedStep ∧ GammaOnto ∧ ColBound ∧ LiftHf ∧ Mono ∧ IntDefs ∧ NonemptyQ ∧ NonemptyU ∧
    NonemptyG :=
  ⟨differentialsComplex_holds, cochainsSubmodules_holds, cocyclesFinite_holds, homPreservesCochains_holds, gammaStableOfGammaQUnit_holds, cocycleLiftOfExact_holds,
    torsionKilledCriterion_holds, gammaGradedStep_holds, gammaImageProduct_holds, cokernelLengthBound_holds, finiteClassesLift_holds, liftsAt_mono,
    integral_wach_definitions, wach_lattice_nonempty_Q, wach_lattice_nonempty_unramified, wach_lattice_nonempty_gamma⟩

theorem lift_wach (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (B : Base O A) (M : ℕ)
    (D₀ D₁ D₂ : Type)
    [AddCommGroup D₀] [Module A D₀] [Module O D₀] [IsScalarTower O A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module O D₁] [IsScalarTower O A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module O D₂] [IsScalarTower O A D₂]
    (W₀ : WachMod B M D₀) (W₁ : WachMod B M D₁) (W₂ : WachMod B M D₂) (S : SES W₀ W₁ W₂)
    (e : ℕ) (hW : CokerKilled S e) (hQ : RatSurj S)
    (δ : D₀ →ₗ[O] D₀) (R : Polynomial O) (a k : ℕ) (u : O)
    (hk : B.PhiX k) (ha : M ≤ k * (a + 1))
    (hδ : ∀ y, B.X • δ y = W₀.γ y - y)
    (hR : ∀ y, W₀.QInv y → Polynomial.aeval δ (Polynomial.X * R) y ∈ W₀.N)
    (hZ : ∀ y, W₀.QInv y → (B.p : O) • y ∈ W₀.N → y ∈ W₀.N)
    (hZu : ∀ y, W₀.QInv y → (∏ i ∈ Finset.Icc 1 a, (1 - u ^ i)) • y ∈ W₀.N → y ∈ W₀.N)
    (hgr : ∀ i, 1 ≤ i → i ≤ a → ∀ n ∈ W₀.N, ∃ n' ∈ W₀.N,
      W₀.γ (B.X ^ i • n) = u ^ i • (B.X ^ i • n) + B.X ^ (i + 1) • n')
    (hφ : ∀ n ∈ W₀.N, ∃ z ∈ W₀.N,
      B.X ^ (a + 1) • n = B.X ^ (a + 1) • z - W₀.φ (B.X ^ (a + 1) • z)) :
    Lifts S ((B.p : O) ^ e * (R.eval 0 * ∏ i ∈ Finset.Icc 1 a, (1 - u ^ i))) :=
  cocycleLiftOfExact_holds O A B M D₀ D₁ D₂ W₀ W₁ W₂ S e _ hW hQ
    (torsionKilledCriterion_holds O A B M D₀ W₀ δ R a k _ hk ha hδ hR hZ hZu
      (gammaImageProduct_holds O A B M D₀ W₀ u a hgr) hφ)

end Formalism.CoboundaryTransfers
