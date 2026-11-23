import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ChainRuleAndJacobianCriterion
open scoped TensorProduct Polynomial

namespace GlobalTheory.EtaleCoordRank

open KaehlerDifferential TensorProduct

theorem finrank_and_linearIndependent_D_unit_mul : ∀ (R B K : Type) [CommRing R] [CommRing B] [Field K] [Algebra R B] [Algebra B K] (d : ℕ) (t : Fin d → B), (MvPolynomial.eval₂Hom (algebraMap R B) t).Etale → Module.finrank K (K ⊗[B] Ω[B⁄R]) = d ∧ ∀ (ι : Type) (e : ι ↪ Fin d) (u : ι → Bˣ), (∀ i, algebraMap B K (t (e i)) = 0) → LinearIndependent K (fun i => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B ((u i : B) * t (e i))) := by
  intro R B K _ _ _ _ _ d t h
  have key : ∃ b : Module.Basis (Fin d) B Ω[B⁄R], ∀ i, b i = D R B (t i) := by
    letI : Algebra (MvPolynomial (Fin d) R) B := (MvPolynomial.eval₂Hom (algebraMap R B) t).toAlgebra
    haveI : IsScalarTower R (MvPolynomial (Fin d) R) B :=
      IsScalarTower.of_algebraMap_eq fun r => by
        change algebraMap R B r = MvPolynomial.eval₂Hom (algebraMap R B) t (MvPolynomial.C r)
        simp
    haveI : Algebra.Etale (MvPolynomial (Fin d) R) B := h
    obtain ⟨⟨b, hb⟩, _⟩ := GlobalTheory.EtaleCoordJacobian.exists_basis_of_etale R B (Fin d)
    refine ⟨b, fun i => ?_⟩
    rw [hb]
    congr 1
    change MvPolynomial.eval₂Hom (algebraMap R B) t (MvPolynomial.X i) = t i
    simp
  obtain ⟨b, hb⟩ := key
  let b' : Module.Basis (Fin d) K (K ⊗[B] Ω[B⁄R]) := b.baseChange K
  refine ⟨by rw [Module.finrank_eq_card_basis b', Fintype.card_fin], ?_⟩
  intro ι e u ht
  have hli : LinearIndependent K (fun i => b' (e i)) := b'.linearIndependent.comp e e.injective
  have hfun : (fun i => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B ((u i : B) * t (e i))) =
      (fun i => Units.map (algebraMap B K : B →* K) (u i)) • (fun i => b' (e i)) := by
    funext i
    simp only [Pi.smul_apply', Units.smul_def, Units.coe_map, MonoidHom.coe_coe, b',
      Module.Basis.baseChange_apply, hb]
    rw [Derivation.leibniz, tmul_add, tmul_smul, tmul_smul, ← algebraMap_smul K (u i : B),
      ← algebraMap_smul K (t (e i)), ht, zero_smul, add_zero]
  rw [hfun]
  exact hli.units_smul _

end GlobalTheory.EtaleCoordRank
