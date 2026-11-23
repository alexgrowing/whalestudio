import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericEmbeddingLocalizedModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Models GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_embedding_localized_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (R : Type) [CommRing R] (a : 𝓞 c.F) (b : 𝓞 c.F →+* R) (ω : R →+* c.F) (C : Model Xo c ω), IsDedFrac ω → ω.comp b = algebraMap (𝓞 c.F) c.F → @IsLocalization.Away (𝓞 c.F) _ a R _ b.toAlgebra → ∀ jX : Xo.XF c ⟶ pullback Z.s (spMap b), jX ≫ pullback.fst _ _ = Z.j → IsOpenImmersion (pullback.fst Z.s (spMap b)) ∧ IsLocallyNoetherian (pullback Z.s (spMap b)) ∧ IsNormalScheme (pullback Z.s (spMap b)) ∧ (∃ z : pullback Z.s (spMap b) ⟶ Sp ℤ, LocallyOfFiniteType z ∧ Flat z) ∧ IsPreimmersion jX ∧ Flat jX ∧ IsDominant jX ∧ QuasiCompact jX ∧ jX ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap ω ∧ (∀ u : Xo.XF c ⟶ pullback Z.s (spMap b), u ≫ pullback.fst _ _ = Z.j → u = jX) := by
  first | exact @GlobalTheory.modelAway_basic | exact GlobalTheory.modelAway_basic | (intros; apply GlobalTheory.modelAway_basic <;> assumption)
