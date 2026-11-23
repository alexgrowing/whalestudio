import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFunctionCuttingDivisor
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_function_cutting_divisor : ∀ {S S' : Scheme.{0}} (g : S' ⟶ S) (M : LB S) (Dv : GlobalTheory.EffCartierData S) (k N : ℕ)
    (σ : (lbPow (GlobalTheory.CechPic.tens (lbPow M k) (GlobalTheory.CechPic.dual Dv.lb)) N).Sec) (V : S'.Opens)
    (e : ∀ i, Γ(S', V ⊓ (M.pull g).U i)), M.IsLB → e ∈ secOn (M.pull g) V → (∀ i, IsUnit (e i)) →
    ∃ t : Γ(S', V), (∀ (A : S'.affineOpens) (hA : A.1 ≤ V), resG S' hA t ∈ ((Dv.idealSheaf ^ N).comap g).ideal A) ∧
      ∀ (A : S'.affineOpens) (hA : A.1 ≤ V), A.1 ≤ g ⁻¹ᵁ nonzeroLocus σ →
        ((Dv.idealSheaf ^ N).comap g).ideal A = Ideal.span {resG S' hA t} := by
  first | exact @GlobalTheory.SecIdeal.exists_local_generator_of_sec | exact GlobalTheory.SecIdeal.exists_local_generator_of_sec | (intros; apply GlobalTheory.SecIdeal.exists_local_generator_of_sec <;> assumption)
