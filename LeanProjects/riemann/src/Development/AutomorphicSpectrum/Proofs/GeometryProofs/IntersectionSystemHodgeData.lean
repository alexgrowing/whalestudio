import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataHodgeSecondStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramMatrixTwoFramesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtIffValueAtStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsIffCentresStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.InteriorPointPolarisedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Cusp.GramChosen

theorem gramAt_eq_hodge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ) (τ : CMType H) (b : Fin Dc.N → W τ) (h : genPt Or.𝔐.ξ ⤳ centre z) (G : Matrix (Fin Dc.N) (Fin Dc.N) ℂ), CoordsAt Or.𝔐.ξ Dc.y z w → Or.𝔐.Interior z → (Lat.comap (fun p => Or.𝔐.V (Or.bg τ) p ⊔ Or.𝔐.V (Or.sm τ) p) (Or.i τ)).IsFrameAt b ⟨centre z, h⟩ → Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (fun k => Or.i τ (b k)) G → gramAt (Dc.h τ) b w = G := by
  intro E _ _ _ H D l Xo c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or z w τ b h G hco hint hfr hG
  classical
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hw : w ∈ mcPts (mCoordIdeal Dc.y) :=
    (GlobalTheory.T.complex_points_iff_centres Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y Or.𝔐.tie w).2 ⟨z, h, hco⟩
  have hnb : w ∉ Dc.Bd := fun hb => (Or.bd z w hco).1 hb hint
  have hex : ∃ a, InFrameDomain Dc.y ((Dc.h τ).chart a) ((Dc.h τ).fr a) w :=
    (Dc.h τ).cover w ⟨hw, hnb⟩
  have hsib := GlobalTheory.T.component_data_hodge_second E H D l Xo c Y II K J Ω W Dc Hd S₀ Or z w τ ((Dc.h τ).chart hex.choose)
    ((Dc.h τ).fr hex.choose) ((Dc.h τ).b hex.choose) h hco ((Dc.h τ).isFrame _) hex.choose_spec
  have hmem : ∀ q, b q ∈ Submodule.span (regAt Or.𝔐.ξ ⟨centre z, h⟩) (Set.range ((Dc.h τ).b hex.choose)) := by
    intro q
    rw [← hsib.2, hfr.2]
    exact Submodule.subset_span ⟨q, rfl⟩
  choose cf hcf using fun q => (Submodule.mem_span_range_iff_exists_fun _).1 (hmem q)
  have hS : ∃ S : Matrix (Fin Dc.N) (Fin Dc.N) Ω, ∀ q, b q = ∑ p, S p q • (Dc.h τ).b hex.choose p :=
    ⟨Matrix.of fun p q => (cf q p : Ω), fun q => by rw [← hcf q]; rfl⟩
  have hreg : ∀ p q, hS.choose p q = (cf q p : Ω) := by
    intro p q
    have h0 : ∑ p, (hS.choose p q - (cf q p : Ω)) • (Dc.h τ).b hex.choose p = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← hS.choose_spec q, sub_eq_zero]
      rw [← hcf q]
      rfl
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hsib.1 _ h0 p)
  choose s hs using fun p q => RingHom.mem_range.1 (cf q p).2
  have hval : ∀ p q, ValAt Or.𝔐.ξ z (hS.choose p q)
      ((Scheme.stalkClosedPointTo z).hom (s p q)) := fun p q =>
    ⟨h, s p q, by rw [hreg, hs], rfl⟩
  have hmat : (Matrix.of fun p q => valAt Dc.y (hS.choose p q) w) =
      Matrix.of fun p q => (Scheme.stalkClosedPointTo z).hom (s p q) := by
    ext p q
    exact valAt_eq hw ((GlobalTheory.T.valAt_iff_value_at Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y Or.𝔐.tie z w h hco _ _).1 (hval p q))
  rw [gramAt, dif_pos hex, dif_pos hS, hmat]
  refine (GlobalTheory.T.gram_matrix_two_frames E H D l Xo c Y S₀ Ω K J Dc.y Or.𝔐 z Dc.N (fun k => Or.i τ ((Dc.h τ).b hex.choose k))
    (fun k => Or.i τ (b k)) _ G hS.choose _ (GlobalTheory.T.interior_point_polarised E H D l Xo c Y S₀ Ω K J Dc.y Or.𝔐 z hint)
    (Or.metric τ hex.choose z w hco hint hex.choose_spec) hG ?_ hval).symm
  intro q
  rw [hS.choose_spec q, map_sum]
  exact Finset.sum_congr rfl fun p _ => map_smul _ _ _

end GlobalTheory.CompanionTheory.Ar.Cusp.GramChosen
