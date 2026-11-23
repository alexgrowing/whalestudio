import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleOfLocallyAmpleOnAffineCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRingHom
open CategoryTheory AlgebraicGeometry Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.BdDim GlobalTheory.SiegelTor GlobalTheory.ZM GlobalTheory.CM GlobalTheory.Models
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_of_locally_ample_on_affine_cover : ∀ (X : Scheme.{0}) (O : Type) [CommRing O] (I : Type) [Finite I] (Y : I → Scheme.{0}) (s : X ⟶ Sp O) (u : ∀ i, Y i ⟶ X) (a : I → O) (L : LB X), CompactSpace X → QuasiSeparatedSpace X → L.IsLB → Ideal.span (Set.range a) = ⊤ → (∀ i, IsOpenImmersion (u i)) → (∀ i, Set.range (u i) = s ⁻¹' {x : Sp O | a i ∉ x.asIdeal}) → (∀ i, ∃ N : ℕ, 0 < N ∧ IsGenerated (lbPow (L.pull (u i)) N)) → ∃ m : ℕ, 0 < m ∧ IsGenerated (lbPow L m) := by
  first | exact @GlobalTheory.BdDim.GenCover.exists_isGenerated_pow_of_basicOpen_cover | exact GlobalTheory.BdDim.GenCover.exists_isGenerated_pow_of_basicOpen_cover | (intros; apply GlobalTheory.BdDim.GenCover.exists_isGenerated_pow_of_basicOpen_cover <;> assumption)
