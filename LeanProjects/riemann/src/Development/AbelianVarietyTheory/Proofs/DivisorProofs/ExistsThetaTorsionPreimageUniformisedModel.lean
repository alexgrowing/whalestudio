import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelLabelledTorsionPoints
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UTorsClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MulEqOneOfComb
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem exists_qkPt_of_utest : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (a : S.Gam), ∃ (pk : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) pk x ∧ x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left := by
  intro o Ω _ _ _ S ρ p _ y₀ u a
  haveI : CharZero u.V := ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V _)).charZero
  obtain ⟨x, hx, hadd, -⟩ := utest_torsion_points o Ω S ρ p y₀ u
  obtain ⟨f, f₁, f₂, -⟩ := uTors_closed u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) _ (GlobalTheory.RealCompare.one_le_rN S)
  have hx1 : x a ^ (S.r * S.N) = 1 := by
    have := u.A.isAb.comm
    obtain ⟨h0, hsm⟩ := ThetaReal.pt_nsmul x hadd
    rw [← hsm, ThetaReal.nsmul_self, h0]
  obtain ⟨q, hq⟩ := f₂ _ hx1
  exact ⟨q, x a, (f₁ _ _).2 hq.symm, hx a⟩

end GlobalTheory.Poinc
