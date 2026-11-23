import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtIffOfSpecializes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreConstOfSpecialisationInvariant
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.FibLat
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.UPoinc.GFib

theorem latAt_const_on_fibre : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (Y : RatModel o Ω) (G : Over Y.Z) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (Z : Scheme.{0}) (q : Y.Z ⟶ Z) (z : Z), _root_.IsPreconnected (q.base ⁻¹' {z}) → (∃ r₀ : ℕ, ∀ w, q.base w = z → RkAt G w r₀) → ∀ (I T : Type) (f : I → (G ⟶ G)), (∀ e, IsMonHom (f e)) → ∀ (gγ : T → (Over.mk Y.pt ⟶ G)) (ζ : oˣ) (L : ℕ), 0 < L → ζ ^ L = 1 → IsUnit (L : o) → (∀ t, gγ t ^ L = 1) → (∀ t w, q.base w = z → ExtNear (gγ t) w) → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (m : I → X →+ X) (c : T → X →+ ZMod L) (w w' : Y.Z), q.base w = z → q.base w' = z → LatAt f gγ ζ L m c w → LatAt f gγ ζ L m c w' := by
  intro o Ω _ _ _ _ Y G _ _ hG Z q z hpre hrk I T f hf gγ ζ L hL hζ hu hγ hext X _ _ _ m c w w' hw hw'
  obtain ⟨r₀, hr⟩ := hrk
  haveI : IsNoetherianRing o := by
    haveI := ArithBase.ded (o := o) (Ω := Ω)
    infer_instance
  haveI := Y.lft
  haveI := Y.qc
  haveI : IsLocallyNoetherian Y.Z := LocallyOfFiniteType.isLocallyNoetherian Y.s
  haveI : CompactSpace Y.Z := QuasiCompact.compactSpace_of_compactSpace Y.s
  haveI : IsNoetherian Y.Z := {}
  exact GlobalTheory.fibre_const_of_specializes_invariant Y.Z Z q.base q.continuous z hpre
    (fun v => LatAt f gγ ζ L m c v)
    (fun a b ha hb hab => latAt_iff_of_specializes hG hL hζ hu hf hγ m c hab (hr a ha) (hr b hb)
      (fun t => hext t b hb)) w w' hw hw'

end GlobalTheory.UPoinc.GFib
