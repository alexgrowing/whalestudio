import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JetOrderOneTangentDecomp
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
theorem _root_.GlobalTheory.T.jet_order_one_tangent_decomp : ∀ {S : Type} [CommRing S] {ρ : Type} [Fintype ρ] [DecidableEq ρ],
    (∀ r : ρ, (jetTrunc : Jet S ρ (0 + 1) →ₐ[S] Jet S ρ 0) (Ideal.Quotient.mk _ (MvPolynomial.X r)) = 0) ∧
    ∀ p : Jet S ρ (0 + 1), (jetTrunc : Jet S ρ (0 + 1) →ₐ[S] Jet S ρ 0) p = 0 →
      (∀ r, ((jetTan r : Jet S ρ (0 + 1) →ₐ[S] DualNumber S) p).fst = 0) ∧
      p = ∑ r, ((jetTan r : Jet S ρ (0 + 1) →ₐ[S] DualNumber S) p).snd •
        (Ideal.Quotient.mk _ (MvPolynomial.X r) : Jet S ρ (0 + 1)) := by
  first | exact @GlobalTheory.JetOneTan.jetOne_tan_span | exact GlobalTheory.JetOneTan.jetOne_tan_span | (intros; apply GlobalTheory.JetOneTan.jetOne_tan_span <;> assumption)
