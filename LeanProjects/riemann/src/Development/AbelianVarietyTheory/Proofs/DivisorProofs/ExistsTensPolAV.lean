import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowPolAV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommGroupSixTermRelationToZpowForm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegPreOfPolAV
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.MumFam.TensPol

open GlobalTheory.CechPic GlobalTheory.SiegelOfPolarised GlobalTheory.PrimNorm GlobalTheory.PrimNormPol GlobalTheory.SiegelPower

def siegLamData (hG : Out.GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R] (Q : Data R) :
    SiegPre 0 1 (1 : R) (𝟙 (Sp R)) where
  A := Q.B
  ab := Q.isAb
  P := abelian₂ Q.B Q.M.L
  isLB := LB.isLB_linComb Q.M.isLB _ _
  rig₁ := hasGen_lam_pull Q.M.isLB _ _ (by simp [diff₂])
  rig₂ := hasGen_lam_pull Q.M.isLB _ _ (by simp [diff₂])
  symm := lbIso_lam_pull Q.M.isLB _ _ (diff₂_comm _ _)
  lev := fun _ => 1
  lev_add := fun _ _ => (_root_.mul_one _).symm
  lev_tors := fun _ => one_pow _
  geom := by
    intro K _ _ x β z _ hz
    obtain rfl : z = 1 := Units.ext (by simpa using hz)
    refine ⟨fun a => ⟨fun _ => ⟨a, (one_smul _ _).symm⟩, fun _ => MonObj.comp_one _⟩,
      fun y hy => ⟨0, (MonObj.comp_one _).trans ((pow_one y).symm.trans hy).symm⟩, fun a b => ?_⟩
    rw [MonObj.comp_one, one_zpow, show unitOn (1 : Kˣ) = 1 from map_one _]
    exact GlobalTheory.EighthPowerFactor.weilIs_one_one hG Q.isAb (pull_isLB (LB.isLB_linComb Q.M.isLB _ _) _) _

theorem lbIso_diag_data {R : Type} [CommRing R] [IsDomain R] (Q : Data R) :
    LBIso ((abelian₂ Q.B Q.M.L).pull (lift (𝟙 Q.B) (𝟙 Q.B)).left)
      (LB.LinComb Q.M.L (K := Fin 2) ![𝟙 Q.B.left, (GrpObj.inv (X := Q.B)).left] ![1, 1]) := by
  have hL := Q.M.isLB
  have hT : ∃ t : LB.Gen (Theta Q.B Q.M.L), t.IsGen := ⟨Q.cub.t, Q.cub.isGen⟩
  have hc := fun x y z => diff₃_ptCls (T := Q.B) hL hT x y z
  have hrM : Out.Rigidified Q.B Q.M.L := ⟨Q.M.rig, Q.M.rigGen⟩
  have p1 : ptCls Q.M.L Q.B 1 = 1 := ptCls_one hL hrM Q.B
  have einv : GrpObj.inv (X := Q.B) = (𝟙 Q.B)⁻¹ := by simp [Hom.inv_def]
  have key : diff₂ (ptCls Q.M.L Q.B) (𝟙 Q.B) (𝟙 Q.B) =
      ptCls Q.M.L Q.B (𝟙 Q.B) * ptCls Q.M.L Q.B (𝟙 Q.B)⁻¹ := by
    have a := diff₂_mul_right hc (𝟙 Q.B) (𝟙 Q.B) (𝟙 Q.B)⁻¹
    rw [mul_inv_cancel] at a
    have b : diff₂ (ptCls Q.M.L Q.B) (𝟙 Q.B) 1 = 1 := by
      simp only [diff₂, _root_.mul_one, p1, inv_one, mul_inv_cancel]
    have c : diff₂ (ptCls Q.M.L Q.B) (𝟙 Q.B) (𝟙 Q.B)⁻¹ =
        1 * (ptCls Q.M.L Q.B (𝟙 Q.B))⁻¹ * (ptCls Q.M.L Q.B (𝟙 Q.B)⁻¹)⁻¹ * 1 := by
      rw [diff₂, mul_inv_cancel, p1]
    rw [b, c] at a
    exact GlobalTheory.AdjPolLocal.le_val_one_add_pow_sub a
  refine lbIso_nested hL _ _ _ _ _ _ ?_
  rw [Fintype.prod_unique, zpow_one, Fin.prod_univ_two]
  refine (prod_lam _ _ (cls Q.M.L)).trans ?_
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, zpow_one]
  refine key.trans ?_
  rw [einv]
  rfl

theorem relAmple_diag {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] (Q : Data R)
    (hD : ((abelian₂ Q.B Q.M.L).pull (lift (𝟙 Q.B) (𝟙 Q.B)).left).IsLB) :
    RelAmple Q.B ((abelian₂ Q.B Q.M.L).pull (lift (𝟙 Q.B) (𝟙 Q.B)).left) := by
  have := Q.isAb.proper
  have hMa : IsAmpleLB Q.M.L := isAmpleLB_of_relAmple_of_isAffine Q.B Q.M.isLB Q.ample
  have hN : IsAmpleLB (LB.LinComb Q.M.L (K := Fin 2) ![𝟙 Q.B.left, (GrpObj.inv (X := Q.B)).left] ![1, 1]) := by
    have := GlobalTheory.GraphVolume.isAmpleLB_graph hMa (GrpObj.inv (X := Q.B)).left (N := 1) le_rfl
    rwa [Nat.cast_one] at this
  have hDa := hN.of_lbIso hD (lbIso_diag_data Q)
  refine relAmple_of_isAmpleLB Q.B hD fun U hU => ?_
  have : CompactSpace (Q.B.hom ⁻¹ᵁ U) :=
    isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage (f := Q.B.hom) _ U.isOpen hU.isCompact)
  exact hDa.pull_of_isOpenImmersion _

end GlobalTheory.MumFam.TensPol

namespace GlobalTheory.MumFam.TensPol

open GlobalTheory.CechPic GlobalTheory.SiegelOfPolarised GlobalTheory.PrimNorm GlobalTheory.PrimNormPol GlobalTheory.SiegelPower

end GlobalTheory.MumFam.TensPol
