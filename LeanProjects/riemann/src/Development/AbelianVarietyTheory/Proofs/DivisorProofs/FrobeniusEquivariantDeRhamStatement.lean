import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusEquivariantDeRham
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobPullHomExtAffine
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.AbDual GlobalTheory.Cris GlobalTheory.AbDatum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_equivariant_de_rham : ∀ (O : Type) [CommRing O] (T : Scheme.{0}) (A : Over T) [GrpObj A] (i : OAct O A) (H : T.Modules)
    (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV))
    (p : ℕ) [Fact p.Prime] (h0 : (p : Γ(T, ⊤)) = 0) (ρ : O →+* End H) (Ψ : (frobPull p h0).obj H ⟶ H),
    IsDRAct e i ρ → IsLinFrob e p h0 Ψ → IsEquivariant (pullAct ρ (frob T p h0)) ρ Ψ := by
  first | exact @GlobalTheory.AbDatum.linFrob_isEquivariant | exact GlobalTheory.AbDatum.linFrob_isEquivariant | (intros; apply GlobalTheory.AbDatum.linFrob_isEquivariant <;> assumption)
