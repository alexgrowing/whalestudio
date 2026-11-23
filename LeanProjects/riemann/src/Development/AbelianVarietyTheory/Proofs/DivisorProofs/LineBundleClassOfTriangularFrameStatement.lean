import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleClassOfTriangularFrame
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTriSelf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.Vert GlobalTheory.TriFrame GlobalTheory.FlagCell
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO SCF)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_bundle_class_of_triangular_frame : ∀ (X : Scheme.{0}) [IsIntegral X] (A : X.Opens) (G : X.Modules) (σ : Fin 1 → Γ(G, A)) (hσ : IsFrame σ) (L : LB X) (hL : L.IsLB) (ρ : ∀ k, Γ(X, A ⊓ L.U k)), genericPoint X ∈ A → IsGenOn A L ρ → Tri hσ (fun _ => L) (fun _ => ρ) → ∀ hG : IsVB G 1, CechPic.cls _ hG.isLB_det = CechPic.cls L hL := by
  first | exact @GlobalTheory.TriFrame.cls_det_eq_of_tri | exact GlobalTheory.TriFrame.cls_det_eq_of_tri | (intros; apply GlobalTheory.TriFrame.cls_det_eq_of_tri <;> assumption)
