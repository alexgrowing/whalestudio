import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataMumfordSideGeneratorValues
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfMulComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorData_mumfordSide_generator_values : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D' W) (A : Matrix (Fin r) (Fin r) ℤ) (f : D'.P.A ⟶ D'.P.A), f = GlobalTheory.TensAct.matAct T A → W = (W + W.transpose) * A → ∃ t : LB.Gen (LB.LinComb D.toPre.P.L (fun p : Fin 4 × ((Fin r × Fin r) × Fin 4) => (![(padd D'.P.A (𝟙 _) f).left, 𝟙 D'.P.A.left, f.left, (toUnit D'.P.A ≫ η[D'.P.A]).left] : Fin 4 → (D'.P.A.left ⟶ D'.P.A.left)) p.1 ≫ tensφ T.pr p.2) (fun p => (![1, -2, -1, 2] : Fin 4 → ℤ) p.1 * tensε W p.2)), t.IsGen ∧ ∀ (y : D'.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good D.toPre.P.L z J → val t (D'.xK y) z J = ∏ a : Fin 4, (∏ i, ∏ j, val (D.toPre.tau (T.xe ((![y + GlobalTheory.TensAct.latAct T A y, y, GlobalTheory.TensAct.latAct T A y, 0] : Fin 4 → D'.X) a) i) (T.xe ((![y + GlobalTheory.TensAct.latAct T A y, y, GlobalTheory.TensAct.latAct T A y, 0] : Fin 4 → D'.X) a) j)) (𝟙 _) z J ^ W i j) ^ (-(![1, -2, -1, 2] : Fin 4 → ℤ) a) := by
  first | exact @GlobalTheory.MumSide.mside | exact GlobalTheory.MumSide.mside | (intros; apply GlobalTheory.MumSide.mside <;> assumption)
