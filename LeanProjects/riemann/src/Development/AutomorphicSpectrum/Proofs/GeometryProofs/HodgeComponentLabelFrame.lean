import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptAwayFromPrimesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem not_inFibre_centre {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (z : Spec (CommRingCat.of ℂ) ⟶ X) (h : genPt ξ ⤳ centre z)
    (r : ℕ) (hr : r.Prime) : ¬ InFibre ξ r ⟨centre z, h⟩ := by
  have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hr.ne_zero
  have hu : IsUnit ((r : X.presheaf.stalk (centre z))) := by
    have h1 : IsUnit ((Scheme.stalkClosedPointTo z).hom (r : X.presheaf.stalk (centre z))) := by
      have e : (Scheme.stalkClosedPointTo z).hom (r : X.presheaf.stalk (centre z)) = (r : ℂ) := map_natCast _ r
      exact e ▸ hr0.isUnit
    exact isUnit_of_map_unit (Scheme.stalkClosedPointTo z).hom _ h1
  obtain ⟨u, hu⟩ := hu
  have hg : genMap ξ ⟨centre z, h⟩ (u : X.presheaf.stalk (centre z)) = (r : Ω) := by
    rw [hu, map_natCast]
  refine not_not.2 ⟨Nat.cast_ne_zero.2 hr.ne_zero, ⟨_, hg⟩, ⟨((u⁻¹ : (X.presheaf.stalk (centre z))ˣ) : X.presheaf.stalk (centre z)), ?_⟩⟩
  rw [← hg]
  exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])

theorem frame_valAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X) (lab : CMType H ⊕ CMType H) (r : ℕ) (s : Fin r → 𝔐.Li) (h : genPt 𝔐.ξ ⤳ centre z), (𝔐.V lab).IsFrameAt s ⟨centre z, h⟩ → ∀ i, ∃ v : epsAt z ⟶ 𝔐.t.G, 𝔐.M.ValAt z (s i) v := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K _ J _ y 𝔐 z lab r s h hs i
  have hinj : Function.Injective (algebraMap (𝓞 c.F) c.F) := RingOfIntegers.coe_injective
  obtain ⟨h1, -, h3⟩ := GlobalTheory.T.hodge_cpt_away_from_primes E H D l Xo c (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) Y S Ω K J y 𝔐 hinj
    ⟨centre z, h⟩ (fun r hr => not_inFibre_centre 𝔐.ξ z h r hr)
  have hmem : s i ∈ 𝔐.V lab ⟨centre z, h⟩ := by
    rw [hs.2]
    exact Submodule.subset_span ⟨i, rfl⟩
  rw [h1 lab] at hmem
  have hlat : s i ∈ 𝔐.M.lat ⟨centre z, h⟩ := by
    rw [h3]
    exact (le_iSup (fun s' => 𝔐.dR s' ⟨centre z, h⟩) lab) hmem
  exact (𝔐.M.exists_valAt_iff z (s i)).2 ⟨h, hlat⟩

end GlobalTheory.CompanionTheory.Ar.HodgeVal
