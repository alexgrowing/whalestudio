import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormGoodRowsFiniteGroupAction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLiftFormsFiniteGroupAction
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem gUnit_of_models : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.toRealDat.IsModels → R.PGUnit F := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F hM
  have hE := GlobalTheory.norm_gE_rows R.toRealDat hM.HE hM.gE hM.ν0
  have hW := GlobalTheory.gW_norm_eq R.toRealDat hM.HW hM.gW hM.νW
  refine ⟨fun g x y => ?_, fun j g x y => ?_⟩
  ·     exact congrArg _ (LinearIsometry.inner_map_map (⟨R.gE g, hE g⟩ : R.HE.H →ₗᵢ[ℂ] R.HE.H) (Tw.out x) (Tw.out y))
  ·     exact congrArg _ (LinearIsometry.inner_map_map
      (⟨R.gW j (sg0 D A3.A) g, hW j (sg0 D A3.A) g⟩ : (R.HW j (sg0 D A3.A)).H →ₗᵢ[ℂ] (R.HW j (sg0 D A3.A)).H) (Tw.out x) (Tw.out y))

end GlobalTheory
