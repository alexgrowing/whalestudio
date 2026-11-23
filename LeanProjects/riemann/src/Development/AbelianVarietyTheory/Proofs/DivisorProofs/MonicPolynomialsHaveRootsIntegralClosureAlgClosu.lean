import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLtTopOfEssFiniteType
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory

theorem aic_integralClosure_algebraicClosure :
    ∀ (D : Type) [CommRing D] [IsDomain D], AIC (integralClosure D (AlgebraicClosure (FractionRing D))) := by
  intro D _ _ p hp hd
  have hmap : (p.map (algebraMap (integralClosure D (AlgebraicClosure (FractionRing D))) (AlgebraicClosure (FractionRing D)))).natDegree = p.natDegree := hp.natDegree_map _
  have hdeg : (p.map (algebraMap (integralClosure D (AlgebraicClosure (FractionRing D))) (AlgebraicClosure (FractionRing D)))).degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree (hp.map _).ne_zero, hmap]; exact_mod_cast hd.ne'
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root _ hdeg
  have hrDp : IsIntegral (integralClosure D (AlgebraicClosure (FractionRing D))) r := ⟨p, hp, by rwa [Polynomial.eval₂_eq_eval_map]⟩
  have hrD : IsIntegral D r := isIntegral_trans r hrDp
  refine ⟨⟨r, hrD⟩, ?_⟩
  apply Subtype.val_injective
  have key := Polynomial.eval₂_at_apply (p := p) (algebraMap (integralClosure D (AlgebraicClosure (FractionRing D))) (AlgebraicClosure (FractionRing D))) ⟨r, hrD⟩
  rw [← Polynomial.eval_map] at key
  have hr' : (p.map (algebraMap (integralClosure D (AlgebraicClosure (FractionRing D))) (AlgebraicClosure (FractionRing D)))).eval r = 0 := hr
  exact key.symm.trans hr'

end GlobalTheory
