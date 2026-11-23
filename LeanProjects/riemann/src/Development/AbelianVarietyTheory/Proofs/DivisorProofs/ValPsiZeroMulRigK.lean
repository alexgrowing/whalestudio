import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSumPolAV
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

noncomputable section

namespace GlobalTheory.MumFam

theorem val_psi_zero_mul_rigK : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult →
    ∀ (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
      val (D.psi 0) (𝟙 _) z J * val D.rigK (𝟙 _) z J = 1 := by
  intro R _ _ D hB z J hJ
  have h1 := GlobalTheory.PolDeg.Data.val_tau_zero (GlobalTheory.PolDeg.Wit.ofDeg D hB) 0 z J hJ
  have h2 : val ((GlobalTheory.PolDeg.Wit.ofDeg D hB).tau 0 0) (𝟙 _) z J = val (D.tau 0 0) (𝟙 _) z J :=
    (GlobalTheory.PolDeg.Wit.exists_tau D 0 0).choose_spec.2 _ _ z J hJ
  rw [h2] at h1
  unfold DegPre.tau at h1
  rw [val_mul hJ, val_mul hJ, val_mul hJ] at h1
  simp only [val_inv] at h1
  rw [congrArg (fun w => val (D.psi w) (𝟙 _) z J) (add_zero (0 : D.X)), mul_inv_cancel, _root_.one_mul,
    ← mul_inv_rev, inv_eq_one] at h1
  rw [mul_comm]
  exact h1

end GlobalTheory.MumFam
