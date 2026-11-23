import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamificationIndexValuationCompat
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecMulMapEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramification_index_valuation_compat : ∀ (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (i : k →+* k') (𝔭 : HeightOneSpectrum (𝓞 k)) (𝔓 : HeightOneSpectrum (𝓞 k')) (ε : ℕ) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (em : k →+* K) (e : ℕ), (∀ z : k, 𝔓.valuation k' (i z) = 𝔭.valuation k z ^ ε) → 0 < e → (∀ z : k, (IsDiscreteValuationRing.maximalIdeal V).valuation K (em z) = 𝔭.valuation k z ^ e) → ∃ (W L : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Field L) (_ : Algebra W L) (_ : IsFractionRing W L) (f : V →+* W) (g : K →+* L) (em' : k' →+* L) (e' d : ℕ), (∀ z : V, algebraMap W L (f z) = g (algebraMap V K z)) ∧ em'.comp i = g.comp em ∧ 0 < e' ∧ e' * ε = d * e ∧ (∀ z : k', (IsDiscreteValuationRing.maximalIdeal W).valuation L (em' z) = 𝔓.valuation k' z ^ e') ∧ ∀ y : K, (IsDiscreteValuationRing.maximalIdeal W).valuation L (g y) = (IsDiscreteValuationRing.maximalIdeal V).valuation K y ^ d := by
  first | exact @GlobalTheory.CommonValuation.exists_common_valuation | exact GlobalTheory.CommonValuation.exists_common_valuation | (intros; apply GlobalTheory.CommonValuation.exists_common_valuation <;> assumption)
