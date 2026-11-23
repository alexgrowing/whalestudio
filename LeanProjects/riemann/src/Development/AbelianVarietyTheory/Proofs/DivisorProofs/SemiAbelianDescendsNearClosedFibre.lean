import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSome
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSectionTranslatesCoverSemiAbelianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartIsOpenImmersionOverBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothNeighbourhoodTranslatesCoverGroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentDatumCarriesTranslateChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentOfChartsPulledBackFromFlatStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem smooth_of_charts_cover : ∀ (Y G U : Scheme.{0}) (J : Type) (ψ : J → (U ⟶ G)) (g : G ⟶ Y) (h : U ⟶ Y), (∀ j, IsOpenImmersion (ψ j)) → (∀ x : G, ∃ j, x ∈ Set.range (ψ j)) → (∀ j, ψ j ≫ g = h) → Smooth h → Smooth g := by
  intro Y G U J ψ g h ho hc hw hs
  let 𝒰 : G.OpenCover := Scheme.Cover.mkOfCovers J (fun _ => U) ψ (fun x => by
    obtain ⟨j, hj⟩ := hc x; exact ⟨j, hj⟩) ho
  haveI : IsZariskiLocalAtSource @Smooth.{0} := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_openCover (P := @Smooth) 𝒰 ?_
  intro j
  have h2 : 𝒰.f j ≫ g = h := hw j
  rw [h2]; exact hs

theorem descends_near_closed_fibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → ∀ φ, N.Datum φ → ∃ (G : Over (Sp R)) (β : G'.left ⟶ G.left) (i : N.U ⟶ G), Smooth G.hom ∧ IsPullback β G'.hom G.hom π ∧ IsOpenImmersion i.left ∧ N.u ≫ β = pullback.fst _ _ ≫ i.left ∧ pullback.fst G'.hom (pullback.fst π π) ≫ β = φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) ≫ β := by
  intro R _ _ _ hA S π hp hs hS G' _ _ hG N hL φ hφ
  obtain ⟨n, a, x, hx, hcov⟩ := GlobalTheory.T.finite_section_translates_cover_semiAbelian R hA S π hp hs hS G' hG N hL
  haveI : IsNoetherianRing R := hA.1
  haveI : IsIntegrallyClosed R := hA.2.2.1
  haveI : Smooth N.U.hom := N.smooth
  obtain ⟨G, β, ψ, hψ, hcovG, hpb, hφβ⟩ := GlobalTheory.T.exists_descent_of_charts_pulled_back_from_flat R S G'.left π G'.hom hp hs hS φ.hom.left (Over.w φ.hom)
    N.U inferInstance (Option (Fin n)) (N.chart x) (fun j => (GlobalTheory.T.chart_isOpenImmersion_over_base S π G' N n x j).1)
    (fun j => (GlobalTheory.T.chart_isOpenImmersion_over_base S π G' N n x j).2) (GlobalTheory.T.smoothNeighbourhood_translates_cover_group S π G' N n x hcov)
    (GlobalTheory.T.descentDatum_carries_translateChart S π G' N n a x (fun i => (hx i).2) φ hφ)
  refine ⟨G, β, Over.homMk (ψ none) (hψ none).2.1, ?_, hpb, (hψ none).1, ?_, hφβ⟩
  · exact smooth_of_charts_cover _ _ _ _ ψ G.hom N.U.hom (fun j => (hψ j).1) hcovG (fun j => (hψ j).2.1) N.smooth
  · simpa using (hψ none).2.2

end GlobalTheory.Mum
