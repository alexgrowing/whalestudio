import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionSplitClosedFibreRationalTwoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangeSemiAbelianCubicalPolarisedDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenTranslateTwoTorsionSplitClosedFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_even_translate : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (P : GlobalTheory.UU.CP G) (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (P₁ : GlobalTheory.UU.CP G₁) (A₁ : PolAV (Sp (FractionRing R'))) (gen₁ : (Over.pullback (jK R')).obj G₁ ≅ A₁.A), GlobalTheory.LN.CDvr R' ∧ FinExt ρ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ IsMonHom gen₁.hom ∧ LBIso (A₁.L.pull gen₁.hom.left) (P₁.L.L.pull (pullback.fst G₁.hom (jK R'))) ∧ LBIso (abelian₂ G₁ P₁.L.L) ((abelian₂ G P.L.L).pull β₂) ∧ EvenOn P₁ := by
  intro R _ _ _ hR G _ _ hG P A gen hgen hL
  obtain ⟨R', _, _, _, ρ, hR', hρ, hall⟩ := GlobalTheory.T.exists_finiteExtension_splitClosedFibre_rationalTwoTorsion R hR G hG A gen hgen
  obtain ⟨G₁, _, _, β, β₂, P₁, A₁, gen₁, hG₁, hpb, hsq, hgen₁, hL₁, hLam₁⟩ :=
    GlobalTheory.T.exists_baseChange_semiAbelian_cubical_polarised_data R hR G hG P A gen hgen hL R' ρ hR' hρ
  obtain ⟨hsp, htw⟩ := hall G₁ β hpb
  obtain ⟨P₂, A₂, gen₂, hgen₂, hL₂, hLam₂, hev⟩ := GlobalTheory.T.exists_even_translate_two_torsion_split_closed_fibre R' hR' G₁ hG₁ hsp htw P₁ A₁ gen₁ hgen₁ hL₁
  refine ⟨R', inferInstance, inferInstance, inferInstance, ρ, G₁, inferInstance, inferInstance, β, β₂, P₂, A₂, gen₂,
    hR', hρ, hpb, hsq, hgen₂, hL₂, ?_, hev⟩
  exact LBIso.trans (LB.isLB_linComb P₂.L.isLB _ _) (LB.isLB_linComb P₁.L.isLB _ _)
    (pull_isLB (LB.isLB_linComb P.L.isLB _ _) _) hLam₂ hLam₁

end GlobalTheory.Mum
