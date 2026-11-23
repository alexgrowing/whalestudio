import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtTranslateTorsion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.expandsAt_translate_torsion_alt : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → I ≠ ⊤ → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ) (x : (𝟙_ (Over (Spec (CommRingCat.of R)))) ⟶ G) (gp : GtPt D.toPre (𝟙_ (Over (Spec (CommRingCat.of R))))), x ^ k = 1 → gp.b ^ k = 1 → (∀ e : ℕ, ∃ xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G), xe ≫ fstG I e G = toUnit _ ≫ x ∧ xe ≫ (U.gt e).pG = toUnit _ ≫ gp.b ∧ ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) xe.left) (LB.pullGen D.toPre.P.L _ _ (gp.s χ) (toUnit (Over.mk (thick R I e))).left)) → ∃ (ν : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![eSec D.toPre.P.A, gp.b.left] (DegPre.lineε k))) (uL : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![𝟙 G.left, (𝟙 G * (toUnit G ≫ x)).left] ![(k : ℤ), -(k : ℤ)])) (uM : ∀ α, LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (D.toPre.famφB α) (fun i => (𝟙 D.toPre.P.A * (toUnit D.toPre.P.A ≫ gp.b)).left ≫ D.toPre.famφB α i)) (DegPre.deltaε k))), ν.IsGen ∧ uL.IsGen ∧ (∀ α, (uM α).IsGen ∧ LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ (uM α) (eSec D.toPre.P.A)) (LB.mulGen D.toPre.P.L _ _ _ _ (gp.s α) ν)) ∧ ∀ (σ σ' : H0 U.LG.L k) (f f' : ∀ α, D.toPre.SecB k α), GeneratorPullback.SecRel U.LG.L _ _ σ' _ _ σ (𝟙 G * (toUnit G ≫ x)).left _ _ uL → (∀ α, GeneratorPullback.SecRel D.toPre.P.L _ _ (f' α) _ _ (f α) (𝟙 D.toPre.P.A * (toUnit D.toPre.P.A ≫ gp.b)).left _ _ (uM α)) → ∀ e, U.ExpandsAt e k σ f → U.ExpandsAt e k σ' f' := by
  first | exact @GlobalTheory.expandsAt_translate_torsion | exact GlobalTheory.expandsAt_translate_torsion | (intros; apply GlobalTheory.expandsAt_translate_torsion <;> assumption)
