import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefOverOfGenerated
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ModelFunctionFieldCompatibility
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.ConstLat
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConstLat

theorem exists_const_fn : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y), ∃ κ : F →+* V.X.functionField,
    ∀ (z : Sp (AlgebraicClosure F) ⟶ V.G) (f : F), valAt (z ≫ V.j) (κ f) = valAt z (V.φ (algebraMap F Y.Fn f)) := by
  intro F _ _ Y V
  haveI := CoverHt.isPreimmersion_j V
  have hη := GlobalTheory.HtGen.Crit.j_gen_specializes V
  let ρ : V.X.functionField ≃+* V.G.functionField := RingEquiv.ofBijective (SmallSec.fnMap V.j hη)
    ⟨(SmallSec.fnMap V.j hη).injective, SmallSec.fnMap_surjective V.j hη⟩
  refine ⟨(ρ.symm : V.G.functionField →+* V.X.functionField).comp (V.φ.comp (algebraMap F Y.Fn)), fun z f => ?_⟩
  change valAt (z ≫ V.j) (ρ.symm (V.φ (algebraMap F Y.Fn f))) = _
  rw [ModelFn.valAt_comp V.j hη z]
  exact congrArg (valAt z) (ρ.apply_symm_apply _)

end GlobalTheory.ConstLat

end
