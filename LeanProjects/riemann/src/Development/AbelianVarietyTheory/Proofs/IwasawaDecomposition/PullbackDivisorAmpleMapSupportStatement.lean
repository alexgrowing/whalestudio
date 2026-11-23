import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackDivisorAmpleMapSupport
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_divisor_ample_map_support : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (X : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (BY : GlobalTheory.EffCartierData Y.X) (k n : ℕ)
    (ρ : gen Y ⟶ gen X) (X' : Scheme.{0}) (b : X' ⟶ X.X) (q : gen Y ⟶ X'),
    Y.jQ ≫ ρ = X.jQ → GlobalTheory.IsAmpleLB (polOf Y k BY) → 0 < n →
    (((BY.idealSheaf ^ n).comap (genι Y)).map (ρ ≫ genι X)).comap (ρ ≫ genι X) = (BY.idealSheaf ^ n).comap (genι Y) →
    FinalTheorems.Blowup b (((BY.idealSheaf ^ n).comap (genι Y)).map (ρ ≫ genι X)) → q ≫ b = ρ ≫ genι X →
    ∀ x : X', (q ⁻¹' {x}).Finite := by
  first | exact @GlobalTheory.BlowQF.finite_preimage_of_blowup | exact GlobalTheory.BlowQF.finite_preimage_of_blowup | (intros; apply GlobalTheory.BlowQF.finite_preimage_of_blowup <;> assumption)
