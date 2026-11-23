import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj

theorem qkPt_g_eq_of_equiv : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∀ p p' : QkPt D F k, p.y = p'.y → QkPt.Equiv D F p p' → p.g = p'.g := by
  intro V _ _ D hB F _ _ k hk p p' hy ⟨z, hz, h, hi, ha⟩
  letI := GlobalTheory.TorusExt.gtGroup D F
  have hkz : k • z = 0 := by
    rw [hy] at hz
    exact left_eq_add.mp hz
  have z0 : z = 0 := by
    have : ((k : ℤ)) • z = 0 := by rw [natCast_zsmul]; exact hkz
    rcases smul_eq_zero.mp this with h0 | h0
    · omega
    · exact h0
  subst z0
  have h0 : h = 0 := by
    rw [(GlobalTheory.TorusExt.isIota_iff_eq hB 0 h).1 hi, map_zero]
  rw [(GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).1 ha, h0, add_zero]

end GlobalTheory.TInj
