import Formalism.LocalToGlobal.InertKernelTheory.DelPolOfTies

noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

namespace Formalism.L2.KerInert.QuadraticBaseChangeGL3

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.KerInert.K2 Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelSeries

section Dict

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (j : ℕ)

theorem coeff_trDY (D : D7) {N N' : ℕ} {ι : ℂ →+* Kc} (e : GL3Theta.Idx D N N' → X.ZA j) (he : Function.Injective e)
    (Φ₀ : MvPolynomial (GL3Theta.FrV D N') ℂ →ₛₗ[ι] XspC (X.Pj (j + 1)) Kc)
    (R : MvPolynomial (GL3Theta.Idx D N N') (MvPolynomial (GL3Theta.FrV D N') ℂ)) (α : GL3Theta.Idx D N N' →₀ ℕ) :
    MvPolynomial.coeff (α.mapDomain e) (trDY X Kc j D e Φ₀ R) = Φ₀ (MvPolynomial.coeff α R) := by
  classical
  unfold trDY
  rw [MvPolynomial.coeff_sum]
  by_cases hα : α ∈ R.support
  · rw [Finset.sum_eq_single α]
    · rw [MvPolynomial.coeff_monomial, if_pos rfl]
    · intro β _ hβ
      rw [MvPolynomial.coeff_monomial, if_neg]
      intro h
      exact hβ (Finsupp.mapDomain_injective he h)
    · intro h
      exact absurd hα h
  · rw [Finset.sum_eq_zero]
    · rw [MvPolynomial.notMem_support_iff.1 hα, map_zero]
    · intro β hβ
      rw [MvPolynomial.coeff_monomial, if_neg]
      intro h
      exact hα (by rwa [← Finsupp.mapDomain_injective he h])

theorem support_trDY (D : D7) {N N' : ℕ} {ι : ℂ →+* Kc} (e : GL3Theta.Idx D N N' → X.ZA j)
    (Φ₀ : MvPolynomial (GL3Theta.FrV D N') ℂ →ₛₗ[ι] XspC (X.Pj (j + 1)) Kc)
    (R : MvPolynomial (GL3Theta.Idx D N N') (MvPolynomial (GL3Theta.FrV D N') ℂ)) [DecidableEq (X.ZA j →₀ ℕ)] :
    (trDY X Kc j D e Φ₀ R).support ⊆ R.support.image (fun α => α.mapDomain e) := by
  intro n hn
  by_contra hni
  apply MvPolynomial.mem_support_iff.1 hn
  unfold trDY
  rw [MvPolynomial.coeff_sum]
  refine Finset.sum_eq_zero fun α hα => ?_
  rw [MvPolynomial.coeff_monomial, if_neg]
  intro h
  exact hni (Finset.mem_image.2 ⟨α, hα, h⟩)

end Dict

theorem prod_fact_mapDomain (Kc : Type) [CommSemiring Kc] {A B : Type} (e : A → B) (he : Function.Injective e)
    (α : A →₀ ℕ) :
    (∏ x ∈ (α.mapDomain e).support, (((α.mapDomain e) x).factorial : Kc)) = α.prod fun _ n => (n.factorial : Kc) := by
  show (α.mapDomain e).prod (fun _ n => (n.factorial : Kc)) = _
  exact Finsupp.prod_mapDomain_index_inj he

theorem pairing_dictionary : PairDict := by
  intro p _ X Kc _ _ j D N N' ι e he Φ₀ R Θ f w hdeg hser
  classical
  rw [Formalism.L2.G.Pend.pairD_eq X Kc j _ f _ (support_trDY X Kc j D e Φ₀ R),
    Finset.sum_image (fun a _ b _ h => Finsupp.mapDomain_injective he h)]
  unfold pairR
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [coeff_trDY X Kc j D e he Φ₀ R α]
  have hC : MvPolynomial.coeff α R * MvPolynomial.C ((α.prod fun _ n => (n.factorial : ℂ)) * TaylorLogMetric.taylor D Θ α) =
      ((α.prod fun _ n => (n.factorial : ℂ)) * TaylorLogMetric.taylor D Θ α) • MvPolynomial.coeff α R := by
    rw [MvPolynomial.smul_eq_C_mul]
    exact mul_comm _ _
  rw [hC, LinearMap.map_smulₛₗ, smul_smul]
  unfold Formalism.L2.G.Pend.derAt
  rw [if_pos (hdeg α hα), hser α hα, prod_fact_mapDomain Kc e he α]
  congr 1
  simp only [map_mul, Finsupp.prod, map_prod, map_natCast]
  ring

theorem eIdx_injective {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (j : ℕ) (hN : RankTie X D j) : Function.Injective (eIdx X D pos j hN) := by
  refine Function.LeftInverse.injective (g := fun z : X.ZA j =>
    ((pos ⟨z.1, z.2.1⟩, Fin.cast hN.2.symm z.2.2.2, Fin.cast hN.1.symm z.2.2.1) : GL3Theta.Idx D (D.R.N j) (D.R.N (j + 1)))) ?_
  rintro ⟨τ, b, a⟩
  simp [eIdx]

end Formalism.L2.KerInert.QuadraticBaseChangeGL3
