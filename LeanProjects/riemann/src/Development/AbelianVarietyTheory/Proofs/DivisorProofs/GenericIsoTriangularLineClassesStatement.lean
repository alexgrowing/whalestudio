import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericIsoTriangularLineClasses
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTriSelf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.Vert GlobalTheory.TriFrame GlobalTheory.FlagCell
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO SCF)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_iso_triangular_line_classes : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B : Vert.Model O) (A : B.X.Opens) (G G' : B.X.Modules) (hG : IsVB G 1) (hG' : IsVB G' 1) (ψ : G' ⟶ G) (φ : B.GenIso G G'), φ.inv = B.genRes.map ψ → genericPoint B.X ∈ A → ∀ (σ : Fin 1 → Γ(G', A)) (hσ' : IsFrame σ) (hσ : IsFrame fun i => ψ.app A (σ i)) (L L' : LB B.X) (ρ : ∀ k, Γ(B.X, A ⊓ L.U k)) (ρ' : ∀ k, Γ(B.X, A ⊓ L'.U k)), IsGenOn A L ρ → IsGenOn A L' ρ' → Tri hσ (fun _ => L) (fun _ => ρ) → Tri hσ' (fun _ => L') (fun _ => ρ') → ∀ D : VertDiv B, IsRatio A D L L' ρ ρ' → (φ.div hG hG').cls = D.cls := by
  first | exact @GlobalTheory.GenDivRatio.cls_div_eq_of_isRatio | exact GlobalTheory.GenDivRatio.cls_div_eq_of_isRatio | (intros; apply GlobalTheory.GenDivRatio.cls_div_eq_of_isRatio <;> assumption)
