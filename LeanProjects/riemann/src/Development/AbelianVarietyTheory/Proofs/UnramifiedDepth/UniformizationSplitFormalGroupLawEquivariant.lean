import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsTorusExtensionPointsOfUniformisationStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ToricPointExtensionAbelianPartFormalGroupHomStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFormalGroupSeriesToricPointExtensionStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ToricPointExtensionTangentSeqSplitExactStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ToricPointExtensionTangentSeqEquivariantStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private noncomputable def starMat {X : Type} [AddCommGroup X] {r : ℕ} (β : Module.Basis (Fin r) ℤ X)
    (OE : Type) [CommRing OE] [StarRing OE] [Module OE X] : OE →+* Matrix (Fin r) (Fin r) ℤ where
  toFun a := Matrix.of fun i k => β.repr (star a • β i) k
  map_one' := by
    ext i k
    simp [Matrix.one_apply, Finsupp.single_apply]
  map_mul' a b := by
    ext i k
    have h : star (a * b) • β i = ∑ j, β.repr (star a • β i) j • (star b • β j) := by
      rw [star_mul, mul_smul]
      conv_lhs => rw [← β.sum_repr (star a • β i)]
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
    simp only [Matrix.of_apply, Matrix.mul_apply, h, map_sum, map_zsmul, Finsupp.coe_finsetSum,
      Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  map_zero' := by
    ext i k
    simp
  map_add' a b := by
    ext i k
    simp [add_smul]

theorem unif_extSer_equivariant : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegData R I) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Out.UnifPre I D A G) [IsAdicComplete I R] (d g : ℕ) (F : FGLaw R d) (FB : FGLaw R g) (x : Fam G d) (xB : Fam D.toPre.P.A g), NilChart G F.F x → NilChart D.toPre.P.A FB.F xB → ∃ (r : ℕ) (J : Fin d → PS R 1 r) (Q : Fin g → PS R 1 d), ExtSer F.F FB.F J Q ∧ ∀ (OE : Type) [CommRing OE] [StarRing OE] [Module OE D.toPre.X] (io : Out.RingAct G OE) (oD : D.OAct OE) (oA : A.OAct OE), U.OLinear OE oD oA io → ∀ (α : OE → Fin d → PS R 1 d) (αB : OE → Fin g → PS R 1 g), (∀ a, Reads x x (io.act a) (α a)) → (∀ a, Reads xB xB (oD.onB.act a) (αB a)) → ∃ N : OE →+* Matrix (Fin r) (Fin r) ℤ, ∀ a, lin Q * lin (α a) = lin (αB a) * lin Q ∧ lin (α a) * lin J = lin J * (N a).map (Int.castRingHom R) := by
  intro R _ _ I D A G _ _ U _ d g F FB x xB hx hxB
  obtain ⟨E, hE⟩ := GlobalTheory.T.exists_torus_extension_points_of_uniformisation R I D A G U
  let β : Module.Basis (Fin (Module.finrank ℤ D.toPre.X)) ℤ D.toPre.X := Module.finBasis ℤ D.toPre.X
  obtain ⟨Q, hQ, hQ'⟩ := GlobalTheory.T.toricPointExtension_abelianPart_formalGroup_hom R I G D.toPre.P.A D.toPre.X E d g F FB x xB hx hxB
  obtain ⟨J, hJ, hJ'⟩ := GlobalTheory.T.exists_formalGroupSeries_toricPointExtension R I G D.toPre.P.A D.toPre.X E d g F FB x xB hx hxB _ β
  refine ⟨_, J, Q, ⟨hJ, hQ, GlobalTheory.T.toricPointExtension_tangentSeq_splitExact R I G D.toPre.P.A D.toPre.X E d g F FB x xB hx hxB _ β J Q
    hJ.1 hQ.1 hQ' hJ'⟩, ?_⟩
  intro OE _ _ _ io oD oA hO α αB hα hαB
  refine ⟨starMat β OE, fun a => ?_⟩
  obtain ⟨h1, h2⟩ := GlobalTheory.T.toricPointExtension_tangentSeq_equivariant R I G D.toPre.P.A D.toPre.X E d g F FB x xB hx hxB _ β J Q
    hJ.1 hQ.1 hQ' hJ' (io.act a) (α a) (hα a)
  refine ⟨h1 _ _ (hαB a) (fun S _ _ h => (hE OE io oD oA hO a S h).1), ?_⟩
  exact h2 (DistribSMul.toAddMonoidHom D.toPre.X (star a)) (fun S _ _ h => (hE OE io oD oA hO a S h).2)

end GlobalTheory
