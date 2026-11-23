import Mathlib
import Formalism.LocalToGlobal.Divisibility.DivisionCompatibleToSub2Indef2
import Formalism.LocalToGlobal.IndefiniteReal.PrimitivePackageFullHecke
import Formalism.LocalToGlobal.GroupLattices.JointServices.LevelOperatorFixesImage

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Cx NumberField

namespace GlobalTheory

theorem prim_rows_surjective : ∀ (D : D7) [IsTotallyComplex D.what₂.LL] (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (s : ℕ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → PrimRows3 R F → ∀ (Zs : DefSub A3.fam3.amb3) (S1 : IndefData (A3.side3 F.P1 F.ψ1 Zs)), (R.toCx3 F).zs = Zs → HEq ((R.toCx3 F).data F.cr true) S1 → Function.Surjective ((A3.side3 F.P1 F.ψ1 Zs).Pq A3.A.μ0).mulVec ∧ Function.Surjective (S1.ι A3.A.μ0).mulVec := by
  intro D _ G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hok hsep hW hP Zs S1 hz hS
  subst hz
  have hS' := eq_of_heq hS
  subst hS'
  have hR := complex_data_conditions_base_level_of_primitive_links hok hsep hW hP
  exact ⟨(hR.wf true).Pq_surj _, (CxData.rowMat_bij _ _ true (hR.what₂ true).1 (hR.ratMu true) _).2⟩

end GlobalTheory
