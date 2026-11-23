import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IotaPointsAdditive

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.IotaExists

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorsionFormCompare

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {W : (Spec (CommRingCat.of R)).Opens}

theorem val_tauW (ψW : PsiOn D W) (a b : D.X) {Z : Scheme.{0}} (r : Z ⟶ W.toScheme) {z : Z} {J}
    (hJ : Good D.P.L z J) :
    val (ψW.tau a b) r z J = val (ψW.psi (a + b)) r z J * (val (ψW.psi a) r z J)⁻¹ * (val (ψW.psi b) r z J)⁻¹ *
      (val (D.rigW W) r z J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))

theorem tauW_symm (ψW : PsiOn D W) (a b : D.X) {Z : Scheme.{0}} (r : Z ⟶ W.toScheme) {z : Z} {J}
    (hJ : Good D.P.L z J) : val (ψW.tau a b) r z J = val (ψW.tau b a) r z J :=
  (val_tauW ψW a b r hJ).trans ((congrArg₂ (· * ·) ((mul_right_comm _ _ _).trans (congrArg₂ (· * ·)
    (congrArg₂ (· * ·) (congrArg (fun x => val (ψW.psi x) r z J) (add_comm a b)) rfl) rfl)) rfl).trans
      (val_tauW ψW b a r hJ).symm)

theorem existsUnique_iota (hB : D.TauBimult) (ψW : PsiOn D W) (T : Over W.toScheme) (y : D.X) :
    ∃! g : GtPt D (overW W T), GtPt.IsIotaW ψW y g := by
  let ρ : overW W T ⟶ TW W := Over.homMk T.hom rfl
  have vv : ∀ χ z J, Good D.P.L z J →
      val (LB.pullGen D.P.L _ _ (ψW.tau y χ) T.hom) (𝟙 (overW W T).left) z J = val (ψW.tau χ y) ρ.left z J :=
    fun χ z J hJ => ((val_pull hJ _ _ _).trans
      (congrArg (fun r => val (ψW.tau y χ) r z J) (Category.id_comp _))).trans (tauW_symm ψW y χ _ hJ)
  obtain ⟨g, hb, hv⟩ := TorusModel.exists_pt (D := D) (T := overW W T) (cP D _ y)
    (fun χ => LB.pullGen D.P.L _ _ (ψW.tau y χ) T.hom)
    (fun χ => pullGen_isGen _ _ _ _ (IotaAdditive.tau_isGen ψW y χ) _) (fun χ U _ h => by
      have p : ∀ x y w v : (TW W).left ⟶ D.P.A.left, ∏ i : ((PUnit ⊕ PUnit) ⊕ PUnit) ⊕ PUnit.{1},
          h (ρ.left ≫ Sum.elim (Sum.elim (Sum.elim (fun _ => x) (fun _ => y)) (fun _ => w)) (fun _ => v) i) ^
            Sum.elim (Sum.elim (Sum.elim (fun _ => (-1 : ℤ)) (fun _ => - -1)) (fun _ => - -1)) (fun _ => -1) i =
          (h (ρ.left ≫ x))⁻¹ * h (ρ.left ≫ y) * h (ρ.left ≫ w) * (h (ρ.left ≫ v))⁻¹ := fun x y w v => by
        simp [Fintype.prod_sum_type]
      refine (p (cP D _ (y + χ)).left (cP D _ y).left (cP D _ χ).left (1 : TW W ⟶ D.P.A).left).trans ?_
      rw [TorusModel.prod_pt, ← Over.comp_left, ← Over.comp_left, ← Over.comp_left, ← Over.comp_left,
        comp_cP, comp_cP, comp_cP, MonObj.comp_one, add_comm y χ, cPoint_add, mul_right_comm _ (h (cP D _ y).left)])
    (fun z J hJ => by
      have C : IsCub (th D (T := overW W T) z J) := isCub_cubV D.cub hJ
      have t := IotaAdditive.tau_mul hB ψW 0 0 y ρ hJ
      rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at t
      exact (vv 0 z J hJ).trans (mul_eq_left.1 t.symm))
    (fun χ χ' z J hJ => (congrArg₂ (· * ·) (vv _ z J hJ) rfl).trans
      ((IotaAdditive.tau_mul hB ψW χ χ' y ρ hJ).trans (congrArg₂ (· * ·) (vv _ z J hJ) (vv _ z J hJ)).symm))
  refine ⟨g, ⟨hb, fun χ => corr_of_val D.P.isLB fun z J hJ => hv χ _ _ z J hJ⟩, fun g' H => ?_⟩
  exact TorusModel.pt_ext (H.1.trans hb.symm) fun χ z J hJ =>
    (val_corr hJ (H.2 χ) (𝟙 _)).trans (hv χ _ _ z J hJ).symm

theorem iota_existsUnique : AllFlat fun {E} _ _ _ {H} {R} _ _ _ {t} P {W} ψW k => ∀ (T : Over W.toScheme) (y : P.D.toPre.X), ∃! g : GtPt P.D.toPre (overW W T), GtPt.IsIotaW ψW y g :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ P _ _ _ ψW _ _ T y => existsUnique_iota P.D.tau_bimult ψW T y

end GlobalTheory.IotaExists
