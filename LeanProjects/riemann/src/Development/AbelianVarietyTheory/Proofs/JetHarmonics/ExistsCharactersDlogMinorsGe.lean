import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.ThmASt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLeadingMinorsGeOfLeRank
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitOfBijectiveMulNatural
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EqOneOfPowEqOneOfCompEqOne
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

namespace HodgeTateStep

variable {O : Type} [CommRing O]

theorem ptMap_fst_dualScale (a : O) :
    ptMap (TrivSqZeroExt.fstHom O O O) ≫ ptMap (dualScale a) =
      ptMap (TrivSqZeroExt.fstHom O O O) := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun x => ?_
  simp [dualScale]

variable {G : Over (Spec (CommRingCat.of O))} [GrpObj G]

noncomputable def scaleLie (a : O) (x : LieG G) : LieG G :=
  ⟨ptMap (dualScale a) ≫ x.1, by rw [← Category.assoc, ptMap_fst_dualScale]; exact x.2⟩

noncomputable def torsionEnd (a : G ⟶ G) [IsMonHom a] (N : ℕ) : torsion G N ⟶ torsion G N :=
  KernelNoTorsion.torsionLift (torsion.ι G N ≫ a) (by
    rw [← MonObj.pow_comp, KernelNoTorsion.torsionι_pow, MonObj.one_comp])

theorem torsionEnd_ι (a : G ⟶ G) [IsMonHom a] (N : ℕ) :
    torsionEnd a N ≫ torsion.ι G N = torsion.ι G N ≫ a :=
  KernelNoTorsion.torsionLift_ι _ _

def HasDlog (p : ℕ) {L : Type} (e : L → LieG G)
    (κ : torsion G (p ^ 1) ⟶ Gm (Spec (CommRingCat.of O))) (y : L → O) : Prop :=
  IsCharTors G (p ^ 1) κ ∧ ∀ (l : L) (R : Type) [CommRing R] [Algebra O R], (p : R) = 0 →
    ∀ w : specO O (DualNumber R) ⟶ torsion G (p ^ 1),
      w ≫ torsion.ι G (p ^ 1) = ptMap (dualBC (Algebra.ofId O R)) ≫ (e l).1 →
      (unitOf (w ≫ κ) : DualNumber R) =
        TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (algebraMap O R (y l))

theorem HasDlog.mul {p : ℕ} {L : Type} {e : L → LieG G}
    {κ κ' : torsion G (p ^ 1) ⟶ Gm (Spec (CommRingCat.of O))} {y y' : L → O}
    (h : HasDlog p e κ y) (h' : HasDlog p e κ' y') : HasDlog p e (κ * κ') (y + y') := by
  refine ⟨fun T a b c hc => ?_, ?_⟩
  · rw [MonObj.comp_mul, MonObj.comp_mul, MonObj.comp_mul, h.1 T a b c hc, h'.1 T a b c hc]
    exact mul_mul_mul_comm _ _ _ _
  · intro l R _ _ hp w hw
    rw [MonObj.comp_mul, GmPoints.unitOf_mul, Units.val_mul, h.2 l R hp w hw, h'.2 l R hp w hw]
    ext <;> simp [add_comm, Algebra.algebraMap_eq_smul_one, add_smul]

end HodgeTateStep

end GlobalTheory
