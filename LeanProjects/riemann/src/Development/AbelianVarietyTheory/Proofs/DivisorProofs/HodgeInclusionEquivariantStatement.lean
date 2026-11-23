import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeInclusionEquivariant
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobPullHomExtAffine
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.AbDual GlobalTheory.Cris GlobalTheory.AbDatum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_inclusion_equivariant : GlobalTheory.CovTop.Hypotheses2 → ∀ (O : Type) [CommRing O] (T : Scheme.{0}) (A : Over T) [GrpObj A] [QuasiSeparated A.hom] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (i : OAct O A) (H : T.Modules)
    (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV))
    (ρ : O →+* End H) (a : omega A ⟶ H), IsDRAct e i ρ → IsHodgeIncl e a → IsEquivariant (omegaAct i) ρ a := by
  first | exact @GlobalTheory.AbDatum.isEquivariant_hodgeIncl | exact GlobalTheory.AbDatum.isEquivariant_hodgeIncl | (intros; apply GlobalTheory.AbDatum.isEquivariant_hodgeIncl <;> assumption)
