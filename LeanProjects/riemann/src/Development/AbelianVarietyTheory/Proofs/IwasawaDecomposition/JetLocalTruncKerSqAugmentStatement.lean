import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JetLocalTruncKerSqAugment
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulCoeEqZero
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory Formalism.L2.Pj GlobalTheory.Serre GlobalTheory.RayEv GlobalTheory.ExpUniqCh0

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_local_trunc_ker_sq_augment : ∀ {S : Type} [Field S] {ρ : Type} (m : ℕ),
    IsLocalRing (Jet S ρ m) ∧ RingHom.ker (jetTrunc : Jet S ρ (m + 1) →ₐ[S] Jet S ρ m) ^ 2 = ⊥ ∧
    (Algebra.ofId S (Jet S ρ 0)).comp (jetAug : Jet S ρ 0 →ₐ[S] S) = AlgHom.id S (Jet S ρ 0) := by
  first | exact @GlobalTheory.JetBasic.jet_basic | exact GlobalTheory.JetBasic.jet_basic | (intros; apply GlobalTheory.JetBasic.jet_basic <;> assumption)
