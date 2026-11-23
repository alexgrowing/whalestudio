import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRadicalSpanProdRelativeRegularParametersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealAlongLocalSpecVanishingIdealComplEqSpanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAbelianLocusOfMemRangeSiegelModuliChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLocusPointMemRangeSiegelModuliOpenImmersiStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

namespace GlobalTheory.BdEqChart

theorem boundary_eq : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (S : Scheme.{0}) [S.IsSeparated] (j : F.X ⟶ S) [IsOpenImmersion j] (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R] (b : cycAway n →+* R) (ξ : Sp R ⟶ S) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing R) ⟶ F.X) (A₁ : Over (Sp (FractionRing R))) [GrpObj A₁] (i₁ : A₁.left ⟶ G₁.left) (β : A₁.left ⟶ F.univ.A.left), IsSemiAbelian G₁ → IsGrpPullback A₁ G₁ (jK R) i₁ → IsGrpPullback A₁ F.univ.A y β → y ≫ j = jK R ≫ ξ → (∀ I : Ideal (S.presheaf.stalk (ξ (closedPoint R))), I.IsRadical → (I.map (Scheme.stalkClosedPointTo ξ).hom).IsRadical) → ∀ (m : ℕ) (t : Fin m → R), IsRelParam b t → (∀ p : Sp R, p ∈ abLocus G₁ ↔ ∏ k, t k ∉ p.asIdeal) → (∀ p : Sp R, ξ p ∈ Set.range j ↔ ∏ k, t k ∉ p.asIdeal) ∧ idlAlong (Scheme.IdealSheafData.vanishingIdeal j.opensRange.compl) ξ = Ideal.span {∏ k, t k} := by
  intro g n F S _ j _ R _ _ _ _ b ξ G₁ _ _ y A₁ _ i₁ β hG h₁ h₂ hy hrad m t ht hab
  have key : ∀ p : Sp R, ξ p ∈ Set.range j ↔ ∏ k, t k ∉ p.asIdeal := fun p =>
    ⟨fun h => (hab p).1 (GlobalTheory.T.mem_abelianLocus_of_mem_range_siegelModuli_chart g n F S j R ξ G₁ y A₁ i₁ β hG h₁ h₂ hy p h),
     fun h => GlobalTheory.T.abelian_locus_point_mem_range_siegelModuli_openImmersion g n F S j R b ξ G₁ y A₁ i₁ β hG h₁ h₂ hy p ((hab p).2 h)⟩
  refine ⟨key, GlobalTheory.T.idealAlongLocalSpec_vanishingIdeal_compl_eq_span S j.opensRange R ξ _ (GlobalTheory.T.isRadical_span_prod_relativeRegularParameters _ R b m t ht) (fun p => ?_) hrad⟩
  rw [Scheme.Hom.coe_opensRange]
  exact key p

end GlobalTheory.BdEqChart
