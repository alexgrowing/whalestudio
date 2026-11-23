import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeRhamRingAction
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobPullHomExtAffine
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.AbDual GlobalTheory.Cris GlobalTheory.AbDatum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_de_rham_ring_action : ∀ (O : Type) [CommRing O] (T : Scheme.{0}) (A : Over T) [GrpObj A], IsAbelianScheme A → ∀ (i : OAct O A) (H : T.Modules)
    (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV)), IsDRIso A H e →
    ∃ ρ : O →+* End H, IsDRAct e i ρ := by
  first | exact @GlobalTheory.AbDatum.exists_isDRAct | exact GlobalTheory.AbDatum.exists_isDRAct | (intros; apply GlobalTheory.AbDatum.exists_isDRAct <;> assumption)
