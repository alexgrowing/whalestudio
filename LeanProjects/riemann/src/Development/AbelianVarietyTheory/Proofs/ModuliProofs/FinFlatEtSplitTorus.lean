import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IotaPointsAdditive
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsUniquePairIff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TorusTorsion

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusModel

section Points

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T T' : Over (Sp R)}

theorem val_unitGen {X Y Z : Scheme.{0}} {L : LB X} (u : Γ(Y, ⊤)ˣ) (r : Z ⟶ Y) {z : Z} {J} (hJ : Good L z J) :
    val (GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.unitGen L u) r z J = gm r z ⊤ u :=
  gm_res _ z le_top (hJ.mem PEmpty.elim _) _

theorem isGen_unitGen {X Y : Scheme.{0}} (L : LB X) (u : Γ(Y, ⊤)ˣ) : (GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.unitGen L u).IsGen :=
  fun i j => by
    obtain rfl : i = j := funext fun k => k.elim
    exact ((congrArg₂ (· * ·) (Fintype.prod_empty _) rfl).trans (_root_.one_mul _)).symm

theorem TorusVal.val_eq {g : GtPt D T} {χ : D.X} {u : Γ(T.left, ⊤)ˣ} (h : TorusVal g χ u) {Z : Scheme.{0}}
    (r : Z ⟶ T.left) {z : Z} {J} (hJ : Good D.P.L z J) : val (g.s χ) r z J = gm r z ⊤ u :=
  (val_corr hJ h.2 r).trans (val_unitGen u r hJ)

theorem exists_torusPt (u : D.X →+ Additive Γ(T.left, ⊤)ˣ) :
    ∃ g : GtPt D T, ∀ χ, TorusVal g χ (Additive.toMul (u χ)) := by
  obtain ⟨g, hb, hv⟩ := exists_pt (D := D) (T := T) 1 (K := PEmpty) (φ := fun _ => PEmpty.elim) (ε := PEmpty.elim)
    (fun χ => GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.unitGen D.P.L (Additive.toMul (u χ))) (fun χ => isGen_unitGen _ _)
    (fun χ U i h => (GlobalTheory.FieldRestrictionTest.formEq_zero (D := D) (T := T) χ U h).symm)
    (fun y J hJ => by rw [val_unitGen _ _ hJ, map_zero, toMul_zero, map_one]) (fun χ χ' y J hJ => by
      have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
      rw [C.face₃, val_unitGen _ _ hJ, val_unitGen _ _ hJ, val_unitGen _ _ hJ, map_add, toMul_add, map_mul,
        _root_.mul_one])
  exact ⟨g, fun χ => ⟨hb, corr_of_val D.P.isLB fun y J hJ => hv χ _ _ y J hJ⟩⟩

theorem isZero_iff' (g : GtPt D T) : g.IsZero ↔ g.b = 1 ∧ ∀ χ y J, Good D.P.L y J → cv g χ y J = 1 :=
  and_congr Iff.rfl (forall_congr' fun _ => ⟨fun h _ _ hJ => (val_corr hJ h _).trans (val_one _),
    fun h => corr_of_val D.P.isLB fun y J hJ => (h y J hJ).trans (val_one _).symm⟩)

theorem exists_nsmul_zero (k : ℕ) (u : D.X →+ Additive Γ(T.left, ⊤)ˣ) (hu : k • u = 0) {g : GtPt D T}
    (hg : ∀ χ, TorusVal g χ (Additive.toMul (u χ))) : ∃ h : GtPt D T, GtPt.IsNsmul k g h ∧ h.IsZero := by
  choose gs hgs using fun i : ℕ => exists_torusPt (D := D) (T := T) (i • u)
  have z : ∀ i : ℕ, i • u = 0 → (gs i).IsZero := fun i hi => (isZero_iff' _).2 ⟨(hgs i 0).1, fun χ y J hJ => by
    have := TorusVal.val_eq (hgs i χ) (𝟙 _) hJ
    rw [hi] at this
    exact this.trans (map_one _)⟩
  refine ⟨gs k, ⟨fun i => gs i, z 0 (zero_smul _ _), fun i => (TorusModel.isAdd_iff _ _ _).2 ⟨?_, fun χ y J hJ => ?_⟩,
    rfl⟩, z k hu⟩
  · rw [(hgs _ 0).1, (hgs _ 0).1, (hg 0).1]
    exact (_root_.mul_one (1 : T ⟶ D.P.A)).symm
  · have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
    have hb : g.b = 1 := (hg 0).1
    rw [show th D y J (cP D _ χ) (gs (i.castSucc : Fin (k + 1))).b g.b = 1 by rw [hb, C.face₃], _root_.mul_one]
    refine (TorusVal.val_eq (hgs _ χ) _ hJ).trans (Eq.trans ?_
      (congrArg₂ (· * ·) (TorusVal.val_eq (hgs _ χ) _ hJ) (TorusVal.val_eq (hg χ) _ hJ)).symm)
    rw [Fin.val_succ, Fin.val_castSucc, succ_nsmul, AddMonoidHom.add_apply, toMul_add, map_mul]

theorem isPull_of_units (h : T' ⟶ T) {g : GtPt D T} {g' : GtPt D T'} {u : D.X → Γ(T.left, ⊤)ˣ}
    {u' : D.X → Γ(T'.left, ⊤)ˣ} (hg : ∀ χ, TorusVal g χ (u χ)) (hg' : ∀ χ, TorusVal g' χ (u' χ))
    (e : ∀ χ, h.left.appTop.hom (u χ).val = (u' χ).val) : GtPt.IsPull h.left g g' := by
  refine (TorusModel.isPull_iff h g g').2 ⟨?_, fun χ y J hJ => ?_⟩
  · rw [(hg 0).1, (hg' 0).1]
    exact (MonObj.comp_one h).symm
  · refine (TorusVal.val_eq (hg' χ) _ hJ).trans (Eq.trans (Units.ext ?_) (TorusVal.val_eq (hg χ) _ hJ).symm)
    rw [gm_val _ y ⊤ trivial, gm_val _ y ⊤ trivial, ← e χ]
    rfl

variable {W : (Sp R).Opens}

end Points

end GlobalTheory.TorusTorsion
