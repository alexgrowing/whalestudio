import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchPowAlt

noncomputable section

open NumberField IsDedekindDomain
open GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

namespace UpperTheory.Gal.InertialTypesAlt.G

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private def evalEquiv {v : Pl F} (w : PlacesOver E v) (hw : ∀ u : PlacesOver E v, u = w) :
    CompletionsOver E v ≃+* w.1.adicCompletion E :=
  letI : Unique (PlacesOver E v) := ⟨⟨w⟩, hw⟩
  RingEquiv.piUnique fun u : PlacesOver E v => u.1.adicCompletion E

private theorem evalEquiv_symm_cont {v : Pl F} (w : PlacesOver E v) (hw : ∀ u : PlacesOver E v, u = w) :
    Continuous (evalEquiv w hw).symm :=
  letI : Unique (PlacesOver E v) := ⟨⟨w⟩, hw⟩
  (Homeomorph.piUnique fun u : PlacesOver E v => u.1.adicCompletion E).symm.continuous

private def cmpEquiv (n : ℕ) {v : Pl F} (w : PlacesOver E v) (hw : ∀ u : PlacesOver E v, u = w) :
    GL (Fin n) (CompletionsOver E v) ≃ₜ* Gw n w.1 where
  toFun := GM.cmp w
  invFun := mapGL n ((evalEquiv w hw).symm : w.1.adicCompletion E →+* CompletionsOver E v)
  left_inv g := Units.ext (Matrix.ext fun _ _ => (evalEquiv w hw).symm_apply_apply _)
  right_inv g := Units.ext (Matrix.ext fun _ _ => (evalEquiv w hw).apply_symm_apply _)
  map_mul' := map_mul _
  continuous_toFun := Continuous.units_map _ (continuous_id.matrix_map (continuous_apply w))
  continuous_invFun := Continuous.units_map _ (continuous_id.matrix_map (evalEquiv_symm_cont w hw))

end

theorem cmpIso : CmpIso := by
  intro F E _ _ _ _ _ n v w hw
  refine ⟨⟨cmpEquiv n w hw, fun _ => rfl⟩, fun g => ⟨fun h => h w, fun h u => ?_⟩, fun h => funext fun g => ?_⟩
  · obtain rfl := hw u
    exact h
  · letI : Unique (PlacesOver E v) := ⟨⟨w⟩, hw⟩
    exact finprod_unique _

end UpperTheory.Gal.InertialTypesAlt.G
