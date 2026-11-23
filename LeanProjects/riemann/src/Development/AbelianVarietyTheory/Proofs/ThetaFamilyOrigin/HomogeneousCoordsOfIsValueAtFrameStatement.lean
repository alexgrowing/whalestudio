import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.HomogeneousCoordsOfIsValueAtFrame
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsVVGenOfIsThetaFamily
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsIndepSections
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneousCoords_of_isValueAt_frame : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : ℕ) (J : Type) (t : J → LB.Sec (Out.LPow P.A P.L N (Out.baseOver (Sp K)))) (ρ : P.A.left ⟶ ((Out.baseOver (Sp K)) ⊗ P.A).left) (e : ρ ≫ (snd (Out.baseOver (Sp K)) P.A).left = 𝟙 P.A.left) (x : (Out.baseOver (Sp K)) ⟶ P.A) (τ : LB.Gen (LB.LinComb P.L (Y := (Out.baseOver (Sp K)).left) (K := Fin 1) (fun _ => x.left) (fun _ => (N : ℤ)))) (w : J → Γ((Out.baseOver (Sp K)).left, ⊤)), (∀ a, Out.IsValueAt P.A P.L N (t a) x τ (w a)) → Crd (lbPow P.L N) (fun a => PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e ((N : ℕ) : ℤ) (t a)) (x.left : Sp K ⟶ P.A.left) (fun a => (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (w a)) := by
  first | exact @GlobalTheory.ZH.CrdDown.crd_down_of_isValueAt | exact GlobalTheory.ZH.CrdDown.crd_down_of_isValueAt | (intros; apply GlobalTheory.ZH.CrdDown.crd_down_of_isValueAt <;> assumption)
