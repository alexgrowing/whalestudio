import Formalism.WachLatticeTwists.HodgeTateChains.GammaIterateMatrixCongruence

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

open Matrix

def StatWSandwich : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (As AA WC OC : Type) [CommRing As] [CommRing AA] [CommRing WC]
    [CommRing OC] [Algebra ℤ_[ℓ] WC] (jA : As →+* AA) (ι : AA →+* WC) (φ : WC →+* WC)
    (Gg : Type) [Group Gg] (H : Subgroup Gg) (act : Gg →* (WC ≃+* WC))
    (r : ℕ) (ρ : Gg →* (Matrix (Fin r) (Fin r) ℤ_[ℓ])ˣ) (πs ξ x : As) (M0 h0 : ℕ)
    (W : HypW ℓ As AA WC jA ι φ Gg H act r ρ πs ξ M0 h0) (ϑ : AA →+* OC) (c : OC),
    LemmaAProp ι φ r → Function.Injective ι → φ (ι (jA x)) = ι (jA x * jA ξ) →
    (∀ a : WC, ι (jA ξ) * a = 0 → a = 0) →
    (ϑ (jA x)) ^ (ℓ ^ n0 ℓ (M0 + h0) * (ℓ - 1)) * c = (ℓ : OC) →
    ∃ (A : Matrix (Fin r) (Fin r) AA) (Y' : Matrix (Fin r) (Fin r) OC),
      A.map ι = (ι (jA x)) ^ M0 • W.Xx ∧
      A.map ϑ * Y' = (ℓ : OC) • (1 : Matrix (Fin r) (Fin r) OC) ∧
      Y' * A.map ϑ = (ℓ : OC) • (1 : Matrix (Fin r) (Fin r) OC)

def UnitCongruenceGivesPerturbation : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (R : Type) [CommRing R] [Algebra ℤ_[ℓ] R] (Xm : Type) [AddCommGroup Xm]
    [Module R Xm] [Module ℤ_[ℓ] Xm] [IsScalarTower ℤ_[ℓ] R Xm] (ϖ z z' : R) (r : ℕ)
    (V : Matrix (Fin r) (Fin r) R) (g0 : Xm →ₗ[R] Xm),
    z * z' = algebraMap ℤ_[ℓ] R (ℓ : ℤ_[ℓ]) →
    IsAdicComplete (Ideal.span {ϖ}) (Fin r → Xm) → (∀ x : Xm, z • x = 0 → x = 0) →
    (∀ x, g0 x = x → x = 0) → (∀ x, ∃ y, z • x = g0 y - y) →
    (∀ i j, z * ϖ ∣ (V - 1) i j) →
    (∀ v : Fin r → Xm, (fun k => ∑ t, V k t • g0 (v t)) = v → v = 0) ∧
    ∀ v : Fin r → Xm, ∃ y : Fin r → Xm,
      (ℓ : ℤ_[ℓ]) • v = (fun k => ∑ t, V k t • g0 (y t)) - y

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
