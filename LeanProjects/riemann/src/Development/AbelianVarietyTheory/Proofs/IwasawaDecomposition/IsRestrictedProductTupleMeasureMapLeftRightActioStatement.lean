import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRestrictedProductTupleMeasureMapLeftRightActio
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRestrictedProductTupleMeasure_map_leftRightAction : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (ν : Measure (Fin n → Fin M → AF F ⊗[F] E)) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (g : GL (Fin M) (AF F ⊗[F] E)) (γ : GL (Fin n) (AF F ⊗[F] E)), IsProd b ν mi mv → IsProd b (ν.map (lrAct g.val γ.val)) (mi.map (lrAct (g.val.map prInf) (γ.val.map prInf))) (fun v => (mv v).map (lrAct (g.val.map (prV v)) (γ.val.map (prV v)))) := by
  first | exact @GlobalTheory.GaugeEx.ProdTransport.isProd_map_lrAct | exact GlobalTheory.GaugeEx.ProdTransport.isProd_map_lrAct | (intros; apply GlobalTheory.GaugeEx.ProdTransport.isProd_map_lrAct <;> assumption)
