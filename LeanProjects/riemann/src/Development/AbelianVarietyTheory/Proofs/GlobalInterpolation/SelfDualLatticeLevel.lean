import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualStabiliserIndex
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualLatticeIndex

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeLevel

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.MainNotions.StandardLattice

theorem isSelfDualLat_iff {E : Type} [Field E] [NumberField E] {n : Type} [Fintype n]
    (σ : E →+* E) (J : Matrix n n E) (N : Submodule (𝓞 E) (n → E)) :
    SelfDualStabiliserIndex.IsSelfDualLat σ J N ↔ SelfDualLatticeIndex.IsSelfDualLat σ J N :=
  and_congr_right fun _ => and_congr_right fun _ => eq_comm

theorem self_dual_lattice_iff_x0 (D : D7) (N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E)) :
    (letI := D.host.cmStar
     SelfDualStabiliserIndex.IsSelfDualLat (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 N) ↔
      SelfDualLatticeIndex.IsSelfDualDefiniteLattice D N :=
  isSelfDualLat_iff _ _ _

theorem indexAt_iff (D : D7) (Lv : LevelData D) (u : D.what₂.Word) :
    SelfDualStabiliserIndex.IndexAt D Lv u ↔ SelfDualLatticeIndex.IndexAt D Lv u :=
  forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun N =>
    imp_congr (self_dual_lattice_iff_x0 D N) Iff.rfl

theorem indexKU_iff : SelfDualStabiliserIndex.IndexKU ↔ SelfDualLatticeIndex.StabiliserLevelIndexFormula :=
  forall_congr' fun D => forall_congr' fun Lv => forall_congr' fun u => indexAt_iff D Lv u

end GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeLevel
