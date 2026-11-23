import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstantEmbeddingCover
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.ConstLat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_constant_embedding_cover : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y), ∃ κ : F →+* V.X.functionField,
    ∀ (z : Sp (AlgebraicClosure F) ⟶ V.G) (f : F), valAt (z ≫ V.j) (κ f) = valAt z (V.φ (algebraMap F Y.Fn f)) := by
  first | exact @GlobalTheory.ConstLat.exists_const_fn | exact GlobalTheory.ConstLat.exists_const_fn | (intros; apply GlobalTheory.ConstLat.exists_const_fn <;> assumption)
