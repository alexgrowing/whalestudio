import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptMultihomogForm
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticePatchAtPrimesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptAwayFromPrimesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeGlueOverPrimesStatement

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace LevelTowerAlt

theorem component_data_height_identity : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B : ℕ), (∀ p ∈ S₀ ∪ Dc.SB B, p.Prime) ∧ (∀ p ∈ S₀ ∪ Dc.SB B, 4 ≤ Or.𝔐.R p) ∧ (∀ p ∈ S₀ ∪ Dc.SB B, FullTorsion Or.𝔐.t.G Or.𝔐.ξ (p ^ Or.𝔐.R p)) ∧ ∀ s, (Or.𝔐.VS (S₀ ∪ Dc.SB B) s).IsVB (labelRk D s) (Or.𝔐.Vgen s) := by
  intro E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or B
  have hS : ∀ p ∈ Dc.SB B, p ∈ Dc.S := fun p hp => (Finset.mem_filter.1 hp).1
  have hpr : ∀ p ∈ S₀ ∪ Dc.SB B, p.Prime := fun p hp => (Finset.mem_union.1 hp).elim (Or.𝔐.S_prime p)
    fun h => Dc.S_prime p (hS p h)
  refine ⟨hpr, fun p hp => (Finset.mem_union.1 hp).elim (Or.𝔐.R_ge p) fun h => Or.R_ge p (hS p h),
    fun p hp => (Finset.mem_union.1 hp).elim (Or.𝔐.tors p) fun h => Or.tors p (hS p h), fun s => ?_⟩
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : IsLocallyNoetherian Or.𝔐.X :=
    GlobalTheory.CompanionTheory.Ar.Cmp.HInterior.isLocallyNoetherian_of_coordTie Or.𝔐.ξ _ Or.𝔐.tie Or.𝔐.all
  have hvb : (Or.𝔐.V s).IsVB (labelRk D s) (Or.𝔐.Vgen s) := Or.𝔐.vb s
  obtain ⟨L, hL, h0, h1⟩ := GlobalTheory.T.lattice_glue_over_primes Or.𝔐.X Ω Or.𝔐.ξ Or.𝔐.Li (Dc.SB B) (Or.𝔐.V s) (fun p => Or.𝔐.HT p s)
    (labelRk D s) (Or.𝔐.Vgen s) Or.𝔐.tie.gen (fun p hp => Dc.S_prime p (hS p hp))
    (fun q _ => by
      obtain ⟨U, hU, b, hb, hf⟩ := hvb q trivial
      exact ⟨U, hU, b, hb, fun q' _ h => hf q' trivial h⟩)
    (fun p hp => Or.ht_vb p (hS p hp) s)
    (fun p hp q hq => by
      obtain ⟨e1, e2, -⟩ := GlobalTheory.T.hodge_cpt_away_from_primes E H D l (Xo l) c _ _ Y S₀ Ω K J Dc.y Or.𝔐
        (FaithfulSMul.algebraMap_injective _ _) q hq
      rw [e1 s]; exact e2 p (Dc.S_prime p (hS p hp)) s)
  have e : Or.𝔐.VS (S₀ ∪ Dc.SB B) s = L := by
    funext q
    have P := GlobalTheory.T.lattice_patch_at_primes Or.𝔐.X Ω Or.𝔐.ξ Or.𝔐.Li (S₀ ∪ Dc.SB B) (Or.𝔐.dR s) (fun p => Or.𝔐.HT p s) q hpr
    have P₀ := GlobalTheory.T.lattice_patch_at_primes Or.𝔐.X Ω Or.𝔐.ξ Or.𝔐.Li S₀ (Or.𝔐.dR s) (fun p => Or.𝔐.HT p s) q Or.𝔐.S_prime
    by_cases h : ∃ p ∈ Dc.SB B, InFibre Or.𝔐.ξ p q
    · obtain ⟨p, hp, hq⟩ := h
      rw [h1 p hp q hq]
      exact P.2 p (Finset.mem_union_right _ hp) hq
    · push Not at h
      rw [h0 q h]
      by_cases h' : ∃ p ∈ S₀, InFibre Or.𝔐.ξ p q
      · obtain ⟨p, hp, hq⟩ := h'
        exact (P.2 p (Finset.mem_union_left _ hp) hq).trans (P₀.2 p hp hq).symm
      · push Not at h'
        exact (P.1 fun p hp => (Finset.mem_union.1 hp).elim (h' p) (h p)).trans (P₀.1 h').symm
  rw [e]; exact hL

end LevelTowerAlt
