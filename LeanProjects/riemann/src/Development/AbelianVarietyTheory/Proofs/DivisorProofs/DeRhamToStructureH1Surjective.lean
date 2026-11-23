import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeOneFormFrameAndSquareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalOneFormsClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWedgePrimitiveOneFormsEqZeroAbelianSchemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConnectionSumWedgeCurvatureAbelianSchemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivativeCurvatureClosednessRelationsAddStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvatureSumWedgeWellDefinedAndDeRhamLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectionCurvatureSumWedgeSemilinearPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveH1StructureAbelianStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AbCoh

theorem wsum_append {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    {n n' : ℕ} (u v : Fin n → Glob1 F) (u' v' : Fin n' → Glob1 F) :
    wsum F (Fin.append u u') (Fin.append v v') = wsum F u v + wsum F u' v' := by
  funext T
  simp only [wsum, Fin.sum_univ_add, Fin.append_left, Fin.append_right, Pi.add_apply]

theorem toHO1_surjective : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → Function.Surjective (toHO1 A.hom) := by
  intro R _ A _ g hA hg x
  obtain ⟨m, u, v, hx⟩ := GlobalTheory.T.exists_connection_sumWedgeCurvature_abelianScheme R A g hA hg x
  obtain ⟨-, -, hAA, hgAA⟩ := GlobalTheory.T.abelianScheme_oneFormFrame_and_square R A g hA hg
  have hcl : Closed1 (OAff (A ⊗ A).hom) = ⊤ := GlobalTheory.T.abelianScheme_globalOneForms_closed R (A ⊗ A) (g + g) hAA hgAA
  have hμ := GlobalTheory.T.connectionCurvatureSumWedge_semilinearPullback R R _ _ A.hom (A ⊗ A).hom (RingHom.id R) (μ[A]).left (ovw μ[A]) x m u v hx
  have h1 := GlobalTheory.T.connectionCurvatureSumWedge_semilinearPullback R R _ _ A.hom (A ⊗ A).hom (RingHom.id R) (fst A A).left (ovw (fst A A)) x m u v hx
  have h2 := GlobalTheory.T.connectionCurvatureSumWedge_semilinearPullback R R _ _ A.hom (A ⊗ A).hom (RingHom.id R) (snd A A).left (ovw (snd A A)) x m u v hx
  have hsum := (GlobalTheory.T.derivativeCurvatureClosedness_relations_add R _ (OAff (A ⊗ A).hom)).2.1 _ _ m m _ _ _ _ h1 h2
  have hprim : pullHO1 (ovw μ[A]) x = pullHO1 (ovw (fst A A)) x + pullHO1 (ovw (snd A A)) x :=
    GlobalTheory.T.primitive_h1_structure_abelian R A g hA hg x
  rw [← hprim] at hsum
  have heq := (GlobalTheory.T.curvatureSumWedge_wellDefined_and_deRhamLift R _ (OAff (A ⊗ A).hom)).1 hcl _ m (m + m) _ _ _ _ hμ hsum
  rw [wsum_append] at heq
  have h0 : wsum (OAff A.hom) u v = 0 := GlobalTheory.T.sum_wedge_primitive_oneForms_eq_zero_abelianScheme R A g hA hg m u v heq
  exact (GlobalTheory.T.curvatureSumWedge_wellDefined_and_deRhamLift R _ (OAff A.hom)).2 x m u v hx h0

end GlobalTheory.AbCoh
