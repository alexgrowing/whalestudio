import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasValues
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopfChar
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopfLin
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatLie
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueTangentDualNumberStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

theorem PositivityTheory.HtPt.Htat.ExistsHodgeTate.exists_isHT (hHenselian : type_of% @GlobalTheory.T.exists_henselian_flat_over_prime) (hBaseChange : type_of% @GlobalTheory.T.exists_base_change_group) (hRegular : type_of% @GlobalTheory.T.regular_at_base_change) : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Smooth G.hom → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (χ : T →* Rˣ), ∃ w : Module.Dual R L, Γ.IsHT i M N χ w := by
  intro R _ _ _ _ T _ _ Γ S G _ _ x N i hT hS L _ _ M χ
  haveI : Smooth G.hom := hS
  obtain ⟨s, hs⟩ := (PositivityTheory.HtPt.Htat.ht_char_section_of hHenselian hBaseChange hRegular) R T Γ χ
  obtain ⟨l, hl⟩ := PositivityTheory.HtPt.Htat.ht_linear R T Γ S G x N i hT L M χ s hs
  have hP := (PositivityTheory.HtPt.Htat.lie_proj S G R x L M).2.1
  obtain ⟨w, hw⟩ := Module.projective_lifting_property
    (Submodule.mkQ (Ideal.span {(N : R)})) l (Submodule.mkQ_surjective _)
  refine ⟨w, s, hs, fun e => ?_⟩
  obtain ⟨v, ⟨hv1, hv2⟩, -⟩ := GlobalTheory.T.existsUnique_tangent_dual_number R T Γ S G x N i hT L M e
  refine ⟨v, hv1, hv2, ?_⟩
  rw [hl e v ⟨hv1, hv2⟩]
  have := LinearMap.congr_fun hw e
  simp only [LinearMap.comp_apply] at this
  rw [← this]
  rfl

theorem PositivityTheory.HtPt.Htat.ht_exists_of (hHenselian : type_of% @GlobalTheory.T.exists_henselian_flat_over_prime) (hBaseChange : type_of% @GlobalTheory.T.exists_base_change_group) (hRegular : type_of% @GlobalTheory.T.regular_at_base_change) : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Smooth G.hom → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (χ : T →* Rˣ), ∃ w : Module.Dual R L, Γ.IsHT i M N χ w :=
  @PositivityTheory.HtPt.Htat.ExistsHodgeTate.exists_isHT hHenselian hBaseChange hRegular
