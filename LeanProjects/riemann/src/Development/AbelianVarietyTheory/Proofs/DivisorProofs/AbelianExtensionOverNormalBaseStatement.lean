import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianExtensionOverNormalBase
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobPullHomExtAffine
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.AbDual GlobalTheory.Cris GlobalTheory.AbDatum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_extension_over_normal_base : GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.SemiAbelianHomExtension → ∀ (O : Type) [CommRing O] (c : O →+* O)
    (S : Scheme.{0}) [IsIntegral S] [AlgebraicGeometry.IsNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S →
    ∀ (K : Type) [Field K] (η : Sp K ⟶ S), GlobalTheory.IsGenericPointHom η →
    ∀ (A : Over S) [GrpObj A] (i : OAct O A), IsAbelianScheme A →
    ∀ (Q : Out.PolAV (Sp K)) (j : OAct O Q.A) (φ : Q.A.left ⟶ A.left), GlobalTheory.CurveRootGeometry.IsActPull j i η φ →
      GlobalTheory.CurveRootGeometry.IsRosati c Q j →
    ∃ P : LB (A ⊗ A).left, IsSelfDual c i P ∧ ∀ m : (Q.A ⊗ Q.A).left ⟶ (A ⊗ A).left,
      m ≫ (fst A A).left = (fst Q.A Q.A).left ≫ φ → m ≫ (snd A A).left = (snd Q.A Q.A).left ≫ φ →
      LBIso (P.pull m) (abelian₂ Q.A Q.L) := by
  first | exact @GlobalTheory.SelfDualSpread.exists_selfDual | exact GlobalTheory.SelfDualSpread.exists_selfDual | (intros; apply GlobalTheory.SelfDualSpread.exists_selfDual <;> assumption)
