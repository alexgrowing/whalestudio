import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EvBasicNEvalSubCoeffMem
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubWeilOfInjective

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair.JetEv

theorem prod_pow_mem_span_pow {A κ : Type} [CommRing A] [Fintype κ] (a : κ → A) (e : κ → ℕ) :
    ∏ i, a i ^ e i ∈ Ideal.span (Set.range a) ^ (∑ i, e i) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) _

theorem jet_hom_spec : ∀ (V Ω A : Type) [CommRing V] [CommRing Ω] [CommRing A] [Algebra Ω A] (β : V →+* Ω) (κ : Type) [Fintype κ] [DecidableEq κ] (m : ℕ), (∀ a : κ → A, Ideal.span (Set.range a) ^ (m + 1) = ⊥ → ∃! ψ : Jet V κ m →+* A, (∀ v : V, ψ (algebraMap V _ v) = algebraMap Ω A (β v)) ∧ ∀ i, ψ (Ideal.Quotient.mk _ (MvPolynomial.X i)) = a i) ∧ ∀ ψ : Jet V κ m →+* A, (∀ v : V, ψ (algebraMap V _ v) = algebraMap Ω A (β v)) → Ideal.span (Set.range fun i => ψ (Ideal.Quotient.mk _ (MvPolynomial.X i))) ^ (m + 1) = ⊥ ∧ (∀ i, IsNilpotent (ψ (Ideal.Quotient.mk _ (MvPolynomial.X i)))) ∧ ∀ f : MvPowerSeries κ V, ψ (psJet m f) = nEval (MvPowerSeries.map β f) (fun i => ψ (Ideal.Quotient.mk _ (MvPolynomial.X i))) := by
  intro V Ω A _ _ _ _ β κ _ _ m
  refine ⟨fun a ha => ?_, fun ψ hψ => ?_⟩
  · letI : Algebra V A := ((algebraMap Ω A).comp β).toAlgebra
    let φ : Jet V κ m →ₐ[V] A := liftJet (MvPolynomial.aeval a) (by simpa using ha)
    have hφ : ∀ i, φ (Ideal.Quotient.mk _ (MvPolynomial.X i)) = a i := fun i =>
      MvPolynomial.aeval_X a i
    refine ⟨(φ : Jet V κ m →+* A), ⟨fun v => φ.commutes v, hφ⟩, ?_⟩
    rintro ψ ⟨h1, h2⟩
    refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun v => ?_) fun i => ?_)
    · exact (h1 v).trans (φ.commutes v).symm
    · exact (h2 i).trans (hφ i).symm
  · set a : κ → A := fun i => ψ (Ideal.Quotient.mk _ (MvPolynomial.X i)) with ha
    have h0 : Ideal.span (Set.range a) ^ (m + 1) = ⊥ := by
      have := map_orig_pow (ψ.comp (Ideal.Quotient.mk (orig V κ ^ (m + 1)))) (m + 1)
      rw [← Ideal.map_map, Ideal.map_quotient_self, Ideal.map_bot] at this
      exact this.symm
    have h1 : ∀ i, a i ^ (m + 1) = 0 := fun i => by
      have := Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i) : a i ∈ Ideal.span (Set.range a)) (m + 1)
      rwa [h0, Ideal.mem_bot] at this
    refine ⟨h0, fun i => ⟨m + 1, h1 i⟩, fun f => ?_⟩
    have hm : ∀ (e : κ →₀ ℕ) (c : V), ψ (Ideal.Quotient.mk _ (MvPolynomial.monomial e c)) =
        algebraMap Ω A (β c) * ∏ i, a i ^ e i := fun e c => by
      rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), ← hψ]
      simp only [map_mul, map_prod, map_pow]
      rfl
    rw [GlobalTheory.evBasic_nEval_eq_tEval _ a (m + 1) h1, psJet, psTrunc, map_sum, map_sum]
    simp only [hm]
    rw [degLE, Finset.sum_filter, Finset.sum_image, ReciprocityTheory.PGsh.Be2.tEval]
    · refine Finset.sum_congr rfl fun e _ => ?_
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl), MvPowerSeries.coeff_map]
      split_ifs with h
      · rfl
      · have h2 := prod_pow_mem_span_pow a fun i => (e i : ℕ)
        have h3 : m + 1 ≤ ∑ i, (e i : ℕ) := Nat.lt_of_not_le h
        have h4 := Ideal.pow_le_pow_right h3 h2
        rw [h0, Ideal.mem_bot] at h4
        rw [h4, mul_zero]
    · intro e _ e' _ h
      funext i
      exact Fin.ext (congrFun (Finsupp.equivFunOnFinite.symm.injective h) i)

end GlobalTheory.AlphaPair.JetEv
end
