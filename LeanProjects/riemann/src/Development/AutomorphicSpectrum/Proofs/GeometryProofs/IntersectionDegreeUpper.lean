import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExists
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeLatticeFlagStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.TrivFlagHodgeStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompCoverCmSignsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionDatumDegreeSumStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompactDatumIntersectionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem span_eq_of_card_nef {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {m r : ℕ} {s : Fin m → V} {b : Fin r → V}
    {U : Submodule Ω V} (hs : LinearIndependent Ω s) (hb : LinearIndependent Ω b)
    (hU : Submodule.span Ω (Set.range b) = U) (hm : ∀ k, s k ∈ U) (h : r = m) :
    Submodule.span Ω (Set.range s) = U := by
  subst hU
  haveI : FiniteDimensional Ω (Submodule.span Ω (Set.range b)) := FiniteDimensional.span_of_finite _ (Set.finite_range _)
  refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨k, rfl⟩
    exact hm k
  · rw [finrank_span_eq_card hs, finrank_span_eq_card hb]
    simp [h]

end GlobalTheory.CompanionTheory.Ar.Cusp

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.intersection_degree_upper : Top.Given → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ B : ℕ), admitted Xo l c Y Or B₁ → 4 * Dc.f + 2 ≤ B → NefOnFibres (mCoordIdeal Dc.y) (muTwDeg Hd B) := by
  intro hG hW E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or B₁ B hA hB
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨hY, hgood, hS₀, -, hB₁, hS, -⟩ := hA
  obtain ⟨v1, v2, v3, v4⟩ := GlobalTheory.T.compact_datum_intersection E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B
  let g : Cpt Or.𝔐.ξ := ⟨genPt Or.𝔐.ξ, specializes_rfl⟩
  obtain ⟨ch, hch⟩ := Or.𝔐.tie.cover g
  obtain ⟨m, f, cc, -, -, hsum, hl⟩ := Hd.locally ch hch.1
  have hm : Nonempty (Fin m) := by
    by_contra h0
    rw [not_nonempty_iff] at h0
    simp at hsum
  obtain ⟨bb, -, u, -, hΛ⟩ := hl hm.some
  have hs : ∀ τ k, ∃ s : Or.𝔐.Li, s ∈ Or.𝔐.Vgen (Or.sm τ) ∧
      Or.i τ (bb τ (tailIdx Dc.j_le_N k)) - s ∈ Or.𝔐.Vgen (Or.bg τ) := fun τ k => by
    have h1 : Or.i τ (bb τ (tailIdx Dc.j_le_N k)) ∈ Or.𝔐.Vgen (Or.bg τ) ⊔ Or.𝔐.Vgen (Or.sm τ) := by
      rw [← Or.i_range τ]
      exact LinearMap.mem_range_self _ _
    obtain ⟨x, hx, z, hz, hxz⟩ := Submodule.mem_sup.1 h1
    exact ⟨z, hz, by rw [← hxz, add_sub_cancel_right]; exact hx⟩
  choose s hs using hs
  obtain ⟨w1, w2⟩ := GlobalTheory.T.intersection_datum_degree_sum E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B bb s _ hs hΛ
  have hspan : ∀ τ, LinearIndependent Ω (s τ) ∧ Submodule.span Ω (Set.range (s τ)) = Or.𝔐.Vgen (Or.sm τ) := fun τ => by
    obtain ⟨U, hU, b, hb, hfr⟩ := v4 (Or.sm τ) g trivial
    exact ⟨w1 τ, GlobalTheory.CompanionTheory.Ar.Cusp.span_eq_of_card_nef (w1 τ) (hfr g trivial hU).1 hb (fun k => (hs τ k).1) (Or.rk_sm τ)⟩
  have hj1 := Dc.one_le_j
  have hj2 := Dc.j_le
  have hj3 := Dc.two_le_N
  have hN := Or.N_eq
  have hpq : 1 ≤ D.p ∧ 1 ≤ D.q := by
    rcases Or.side with ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> omega
  have hside : Or.sm = Sum.inl ∨ Or.sm = Sum.inr := by
    rcases Or.side with ⟨-, h, -⟩ | ⟨-, h, -⟩
    · exact .inr h
    · exact .inl h
  refine GlobalTheory.T.hodge_comp_cover_cm_signs hG hW E H D Xo l c Y (S₀ ∪ Dc.SB B) Ω K J Dc.y (Or.𝔐.withS _ v1 v2 v3 v4) Or.deg Or.sm _ s _ _
    hY hpq.1 hpq.2 Or.cover (fun p hp => ?_) (fun p hp hpS => ?_) hside hspan w2
  · rcases Finset.mem_union.1 hp with h | h
    · exact hgood.1 p h
    · exact hgood.2 p (Finset.mem_filter.1 h).1
  · rw [Finset.mem_union, not_or] at hpS
    have h1 : ¬ (p : ℤ) ∣ 2 * discr E * l.M' := fun h => hpS.1 ((hS₀ p).2 ⟨hp, h⟩)
    have h2 : 4 * Dc.f + 2 ≤ p := by
      by_contra h
      exact hpS.2 (Finset.mem_filter.2 ⟨(hS p).2 ⟨hp, by omega, hpS.1⟩, by omega⟩)
    refine ⟨fun h => h1 ((h.mul_left 2).mul_right _), h2, lt_of_le_of_ne hp.two_le ?_⟩
    rintro rfl
    exact h1 ((Dvd.intro _ rfl : ((2 : ℕ) : ℤ) ∣ ((2 : ℕ) : ℤ) * discr E).mul_right _)
