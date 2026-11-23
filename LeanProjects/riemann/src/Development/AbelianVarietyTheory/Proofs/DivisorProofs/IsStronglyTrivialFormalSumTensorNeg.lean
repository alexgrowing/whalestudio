import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosVec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TensBalNeg

theorem triv_neg : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (T : Tens D D' W) (c : GlobalTheory.TensBal.Vec r →₀ ℤ), GlobalTheory.TensBal.Triv T c → GlobalTheory.TensBal.Triv T (-c) := by
  intro R _ _ D D' r W T c ⟨Ξ, hΞ, h1, h2⟩
  have hF : FormEq (fun v : c.support => (GlobalTheory.TensBal.vecHom T v.1).left) (fun v => -(c v.1))
      (fun v : (-c).support => (GlobalTheory.TensBal.vecHom T v.1).left) (fun v => (-c) v.1) := by
    intro U _ h
    rw [Finset.prod_coe_sort c.support (fun v => h (GlobalTheory.TensBal.vecHom T v).left ^ (-(c v))),
      Finset.prod_coe_sort (-c).support (fun v => h (GlobalTheory.TensBal.vecHom T v).left ^ ((-c) v)),
      Finsupp.support_neg]
    simp only [Finsupp.neg_apply]
  obtain ⟨Ξ', hΞ', hv⟩ := exists_gen D.P.isLB hF (LB.invGen D.P.L _ _ Ξ) (LB.isGen_invGen D.P.L _ _ Ξ hΞ)
  refine ⟨Ξ', hΞ', fun z J hJ => ?_, fun z J hJ y y' => ?_⟩
  · rw [hv _ _ z J hJ, val_inv, h1 z J hJ, inv_one]
  · rw [hv _ _ z J hJ, val_inv, h2 z J hJ y y', Finsupp.support_neg, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [Finsupp.neg_apply, neg_neg, zpow_neg, inv_inv]

end GlobalTheory.TensBalNeg
