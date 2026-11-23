import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLiftPrincipallyPolarisedAbelianSquareZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_principally_polarised_abelian_square_zero : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (T : Type) [CommRing T] [IsNoetherianRing T] (P₀ : Out.PolAV (Geo.Tor.Sp T)) (io : T →+* O) (P : Out.PolAV (Geo.Tor.Sp O)) (φ : P.A.left ⟶ P₀.A.left), Geo.Tor.IsGrpPullback P.A P₀.A (Geo.Tor.spMap io) φ → Geo.Tor.LBIso P.L (P₀.L.pull φ) → P.g = P₀.g → 1 ≤ P.g → ∀ (R' : Type) [CommRing R'] (π : R' →+* O), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∃ (G : Over (Spec (CommRingCat.of R'))) (_ : GrpObj G) (_ : IsCommMonObj G) (Q : LB (G ⊗ G).left) (ψ : P.A.left ⟶ G.left) (ψ₂ : (P.A ⊗ P.A).left ⟶ (G ⊗ G).left), IsAbelianScheme G ∧ Q.IsLB ∧ (∃ t : (Q.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) ∧ (∃ t : (Q.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) ∧ Geo.Tor.LBIso Q (Q.pull (lift (snd G G) (fst G G)).left) ∧ Out.RelAmple G (Q.pull (lift (𝟙 G) (𝟙 G)).left) ∧ (∀ (Z : Over (Spec (CommRingCat.of R'))) (x : Z ⟶ G), (∃ t : (Q.pull (lift (snd G Z ≫ x) (fst G Z)).left).Gen, t.IsGen) → x = 1) ∧ Geo.Tor.IsGrpPullback P.A G (Spec.map (CommRingCat.ofHom π)) ψ ∧ Geo.Tor.IsSquare ψ ψ₂ ∧ Geo.Tor.LBIso (abelian₂ P.A P.L) (Q.pull ψ₂) := by
  first | exact @GlobalTheory.AbelianLift.exists_lift | exact GlobalTheory.AbelianLift.exists_lift | (intros; apply GlobalTheory.AbelianLift.exists_lift <;> assumption)
