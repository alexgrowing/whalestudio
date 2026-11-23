import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationPairingEquivariant
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobPullHomExtAffine
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.AbDual GlobalTheory.Cris GlobalTheory.AbDatum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_pairing_equivariant : GlobalTheory.CovTop.Hypotheses2 → ∀ (O : Type) [CommRing O] (c : O →+* O) (T : Scheme.{0}) (A : Over T) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (i : OAct O A) (P : LB (A ⊗ A).left), IsSelfDual c i P →
    ∀ (H : T.Modules)
    (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV))
    (ρ : O →+* End H) (β : H ⟶ dual H), IsDRAct e i ρ → IsPolPairing e P β →
    ∀ x : O, VB.act ρ x ≫ β = β ≫ dualMap (VB.act ρ (c x)) := by
  first | exact @GlobalTheory.AbDatum.Adjoint.main | exact GlobalTheory.AbDatum.Adjoint.main | (intros; apply GlobalTheory.AbDatum.Adjoint.main <;> assumption)
