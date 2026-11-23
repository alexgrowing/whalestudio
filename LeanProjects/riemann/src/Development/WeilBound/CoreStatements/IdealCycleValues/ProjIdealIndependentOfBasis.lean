import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace BaseChangeColon

section

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω] {K : Type} {ι : K → Type}
  {N M : ℕ} {E : Type} [AddCommGroup E] [Module Ω E]

noncomputable def polyCoord (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) : (Σ o, bundleIdx ι M o) → MvPolynomial (Fin N) Ω
  | ⟨none, l⟩ => ∑ i, X i * C (φ l (w i))
  | ⟨some k, i⟩ => C (y ⟨k, i⟩)

noncomputable def polyCone (F : Type) [Field F] [Algebra F Ω] (y : (Σ k, ι k) → Ω)
    (w : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω E) :
    MRing (bundleIdx ι M) F →+* MvPolynomial (Option K) (MvPolynomial (Fin N) Ω) :=
  eval₂Hom (C.comp ((C : Ω →+* MvPolynomial (Fin N) Ω).comp (algebraMap F Ω)))
    (fun p => C (polyCoord y w φ p) * X p.1)

theorem aeval_polyCoord (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) {Φ : Type} [Field Φ] [Algebra Ω Φ] (s : Fin N → Φ)
    (p : Σ o, bundleIdx ι M o) : aeval s (polyCoord y w φ p) = projCoord y w φ s p := by
  obtain ⟨_ | k, i⟩ := p
  · simp only [polyCoord, projCoord, map_sum, map_mul, aeval_X, aeval_C]
  · simp only [polyCoord, projCoord, aeval_C]

theorem projIdeal_eq_ker (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) {Φ : Type} [Field Φ] [Algebra Ω Φ] (s : Fin N → Φ) :
    projIdeal F y w φ s = RingHom.ker ((MvPolynomial.map
      ((aeval s : MvPolynomial (Fin N) Ω →ₐ[Ω] Φ) : MvPolynomial (Fin N) Ω →+* Φ)).comp
        (polyCone F y w φ)) := by
  unfold projIdeal
  congr 1
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
  · simp [polyCone]
  · simp [polyCone, aeval_polyCoord]

theorem projCoord_change (y : (Σ k, ι k) → Ω) (w w' : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) {Φ : Type} [Field Φ] [Algebra Ω Φ] (t : Fin N → Φ) :
    projCoord y w φ (fun i => ∑ j, t j * algebraMap Ω Φ (w.repr (w' j) i)) = projCoord y w' φ t := by
  funext p
  obtain ⟨_ | k, l⟩ := p
  · simp only [projCoord, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_rhs => rw [← w.sum_repr (w' j)]
    simp only [map_sum, map_smul, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]
  · simp only [projCoord]

theorem projIdeal_le (y : (Σ k, ι k) → Ω) (w w' : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) {Φ : Type} [Field Φ] [Algebra Ω Φ] (t : Fin N → Φ)
    (ht : AlgebraicIndependent Ω t) : projIdeal F y w φ t ≤ projIdeal F y w' φ t := by
  have e : projIdeal F y w' φ t =
      projIdeal F y w φ (fun i => ∑ j, t j * algebraMap Ω Φ (w.repr (w' j) i)) := by
    unfold projIdeal
    rw [projCoord_change]
  rw [e, projIdeal_eq_ker, projIdeal_eq_ker]
  intro f hf
  rw [RingHom.mem_ker, RingHom.comp_apply] at hf ⊢
  have h0 : polyCone F y w φ f = 0 :=
    MvPolynomial.map_injective
      ((aeval t : MvPolynomial (Fin N) Ω →ₐ[Ω] Φ) : MvPolynomial (Fin N) Ω →+* Φ) ht
      (by rw [hf, map_zero])
  rw [h0, map_zero]

end

theorem projIdeal_independent_of_basis : ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (N M : ℕ) (E : Type) [AddCommGroup E] [Module Ω E] (w w' : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω E) (Φ : Type) [Field Φ] [Algebra Ω Φ] (t : Fin N → Φ), AlgebraicIndependent Ω t → projIdeal F y w φ t = projIdeal F y w' φ t := by
  intro F _ Ω _ _ K _ _ ι _ y N M E _ _ w w' φ Φ _ _ t ht
  exact le_antisymm (projIdeal_le y w w' φ t ht) (projIdeal_le y w' w φ t ht)

end BaseChangeColon
