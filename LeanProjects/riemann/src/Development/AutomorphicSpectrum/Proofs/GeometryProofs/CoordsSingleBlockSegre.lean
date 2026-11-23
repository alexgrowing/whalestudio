import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase.Reindex

theorem coordTie_one_block (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (N : ℕ)
    (x : Fin (N + 1) → Ω) (h : CoordTie ℤ ξ x) :
    CoordTie ℤ ξ (fun c' : (k : Unit) → (fun _ : Unit => Fin (N + 1)) k =>
      ∏ k, (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2) ⟨k, c' k⟩) := by
  have he : Function.Surjective (fun c' : Unit → Fin (N + 1) => c' ()) :=
    fun j => ⟨fun _ => j, rfl⟩
  have hfun : (fun c' : (k : Unit) → (fun _ : Unit => Fin (N + 1)) k =>
      ∏ k, (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2) ⟨k, c' k⟩) =
      fun c' : Unit → Fin (N + 1) => x (c' ()) := by
    funext c'
    simp
  rw [hfun]
  have hc : ∀ (c : Unit → Fin (N + 1)) p,
      InChart ξ (fun c' : Unit → Fin (N + 1) => x (c' ())) c p ↔ InChart ξ x (c ()) p :=
    fun c p => and_congr Iff.rfl (he.forall (p := fun c' => x c' / x (c ()) ∈ regAt ξ p)).symm
  refine ⟨h.gen, fun p => ?_, fun c h0 => ?_, fun c h0 a => ?_⟩
  · obtain ⟨c, hp⟩ := h.cover p
    exact ⟨fun _ => c, (hc _ p).2 hp⟩
  · obtain ⟨U, hU, hq⟩ := h.affine (c ()) h0
    exact ⟨U, hU, fun q => (hq q).trans (exists_congr fun _ => (hc c _).symm)⟩
  · have hr : (Set.range fun j : Unit → Fin (N + 1) => x (j ()) / x (c ())) =
        Set.range fun j => x j / x (c ()) :=
      he.range_comp fun j => x j / x (c ())
    simpa only [hc, hr] using h.ring (c ()) h0 a

end GlobalTheory.CompanionTheory.Ar.SncBase.Reindex
