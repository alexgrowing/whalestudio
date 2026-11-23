import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LyingOver

theorem valuation_pow_of_isPlaceOver : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [Field L] [NumberField L] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)), IsPlaceOver A v → IsPlaceOver A v' → ∃ e : ℕ, 0 < e ∧ ∀ x : K, v'.valuation L (algebraMap K L x) = v.valuation K x ^ e := by
  intro K L Ω _ _ _ _ _ _ _ _ _ A v v' hv hv'
  have hcomap : v'.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = v.asIdeal := by
    ext x
    rw [Ideal.mem_comap, ← hv x, ← hv' (algebraMap (𝓞 K) (𝓞 L) x)]
    have : ((algebraMap (𝓞 K) (𝓞 L) x : 𝓞 L) : L) = algebraMap K L (x : K) := rfl
    rw [this, ← IsScalarTower.algebraMap_apply]
  haveI : v'.asIdeal.LiesOver v.asIdeal := ⟨hcomap.symm⟩
  refine ⟨v.asIdeal.ramificationIdx' v'.asIdeal,
    Nat.pos_of_ne_zero (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver v'.asIdeal v.ne_bot), ?_⟩
  intro x
  exact (IsDedekindDomain.HeightOneSpectrum.valuation_liesOver L v v' x).symm

end GlobalTheory.LyingOver
