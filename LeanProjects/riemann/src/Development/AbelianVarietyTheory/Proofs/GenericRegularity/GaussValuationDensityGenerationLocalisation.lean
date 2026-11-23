import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.LocRingPf
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLoc
import ReciprocityTheory.SemistableReduction.AlgAll
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ValuationLifting.RApprox
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj

namespace GlobalTheory.GaussVal

section
variable {O L U Γ : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L]
  [IsFractionRing O L] [Field U] [LinearOrderedCommGroupWithZero Γ] (v : Valuation U Γ)

omit [Field L] [Algebra O L] [IsFractionRing O L] in

theorem val_lt_one (g : O →+* U) (h1 : ∀ a, v (g a) ≤ 1) {ϖ : O} (hϖ : Irreducible ϖ) (h2 : v (g ϖ) < 1)
    {a : O} (ha : a ∈ IsLocalRing.maximalIdeal O) : v (g a) < 1 := by
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at ha
  obtain ⟨y, rfl⟩ := ha
  rw [map_mul, map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_right' (h1 y)) h2

theorem isInteger_of_val_le (φ : L →+* U) (h1 : ∀ a, v (φ (algebraMap O L a)) ≤ 1) {ϖ : O} (hϖ : Irreducible ϖ)
    (h2 : v (φ (algebraMap O L ϖ)) < 1) {c : L} (hc : v (φ c) ≤ 1) : ∃ a, algebraMap O L a = c := by
  rcases ValuationRing.isInteger_or_isInteger O c with h | ⟨b, hb⟩
  · exact h
  by_cases hc0 : c = 0
  · exact ⟨0, by simp [hc0]⟩
  by_cases hu : IsUnit b
  · obtain ⟨u, rfl⟩ := hu
    refine ⟨((u⁻¹ : Oˣ) : O), ?_⟩
    rw [map_units_inv, hb, inv_inv]
  · exfalso
    have := val_lt_one v (φ.comp (algebraMap O L)) h1 hϖ h2 (a := b) hu
    rw [RingHom.comp_apply, hb] at this
    have h3 : v (φ c) * v (φ c⁻¹) = 1 := by rw [← map_mul, ← map_mul, mul_inv_cancel₀ hc0, map_one, map_one]
    exact absurd h3 (lt_of_le_of_lt (mul_le_of_le_one_left' hc) this).ne
end

theorem val_unit {A U Γ : Type} [CommRing A] [Field U] [LinearOrderedCommGroupWithZero Γ] (v : Valuation U Γ)
    (g : A →+* U) (h1 : ∀ a, v (g a) ≤ 1) {a : A} (ha : IsUnit a) : v (g a) = 1 := by
  obtain ⟨b, hb⟩ := ha.exists_right_inv
  refine le_antisymm (h1 a) ?_
  have h3 : v (g a) * v (g b) = 1 := by rw [← map_mul, ← map_mul, hb, map_one, map_one]
  exact h3.symm.le.trans (mul_le_of_le_one_right' (h1 b))

theorem exists_approx {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))
    (c t : la.adicCompletion K) (ht : t ≠ 0) :
    ∃ (a : K) (y : la.adicCompletionIntegers K), c - algebraMap K _ a = t * (y : la.adicCompletion K) := by
  have ho : IsOpen {x : la.adicCompletion K | t⁻¹ * (c - x) ∈ la.adicCompletionIntegers K} :=
    (Valued.isOpen_valuationSubring (la.adicCompletion K)).preimage (f := fun x => t⁻¹ * (c - x)) (by fun_prop)
  obtain ⟨a, ha⟩ := (HeightOneSpectrum.denseRange_algebraMap K la).exists_mem_open ho ⟨c, by simp⟩
  exact ⟨a, ⟨_, ha⟩, by rw [mul_inv_cancel_left₀ ht]⟩

theorem gauss_dense_gen : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (U : Type) [Field U] (v : Valuation U (WithZero (Multiplicative ℤ))) (ψ : Kp X la N →+* U), (∀ a : Op X la N, v (ψ (algebraMap (Op X la N) (Kp X la N) a)) ≤ 1) → v (ψ (algebraMap (Op X la N) (Kp X la N) (unifO X la N))) < 1 → (∀ (f : B.KO →+* U), (∀ a, f a = ψ (algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a))) → ∀ p : MvPolynomial (Idx D j N) B.KO, (∀ α, v (f (p.coeff α)) ≤ 1) → (∃ α, v (f (p.coeff α)) = 1) → v (MvPolynomial.eval₂ f (fun q => ψ (algebraMap (Op X la N) (Kp X la N) (Tv X la N q))) p) = 1) ∧ (∀ (c : X.Ol la) (γ : WithZero (Multiplicative ℤ)), γ ≠ 0 → ∃ a : B.KO, v (ψ (algebraMap (X.Ol la) (Kp X la N) c) - ψ (algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a))) < γ) ∧ ∀ S : Subfield U, (∀ c : X.Ol la, ψ (algebraMap (X.Ol la) (Kp X la N) c) ∈ S) → (∀ q, ψ (algebraMap (Op X la N) (Kp X la N) (Tv X la N q)) ∈ S) → ∀ c : Kp X la N, ψ c ∈ S := by
  intro D B P j X la N U _ v ψ h1 h2
  have hϖ : Irreducible (unif X la) :=
    Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible (X.Ol la))
  have e1 : ∀ c : X.Ol la, algebraMap (X.Kl la) (Kp X la N) (algebraMap (X.Ol la) (X.Kl la) c) =
      algebraMap (Op X la N) (Kp X la N) (algebraMap (X.Ol la) (Op X la N) c) := fun c => by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have eC : ∀ c : X.Ol la, algebraMap (Pol X la N) (Op X la N) (MvPolynomial.C c) =
      algebraMap (X.Ol la) (Op X la N) c := fun c => by
    rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  set φ : X.Kl la →+* U := ψ.comp (algebraMap (X.Kl la) (Kp X la N)) with hφ
  have g1 : ∀ a, v (φ (algebraMap (X.Ol la) (X.Kl la) a)) ≤ 1 := fun a => by
    rw [hφ, RingHom.comp_apply, e1]; exact h1 _
  have g2 : v (φ (algebraMap (X.Ol la) (X.Kl la) (unif X la))) < 1 := by
    rw [hφ, RingHom.comp_apply, e1]; exact h2
  refine ⟨?_, ?_, ?_⟩
  · intro f hf p hp ⟨α₀, hα₀⟩
    have hf' : ∀ a, f a = φ (algebraMap B.KO (X.Kl la) a) := hf
    have hex : ∀ α, ∃ a : X.Ol la, algebraMap (X.Ol la) (X.Kl la) a = algebraMap B.KO (X.Kl la) (p.coeff α) :=
      fun α => isInteger_of_val_le v φ g1 hϖ g2 (by rw [← hf']; exact hp α)
    choose b hb using hex
    set p₀ : Pol X la N := ∑ α ∈ p.support, MvPolynomial.monomial α (b α) with hp₀
    have hs : α₀ ∈ p.support := by
      rw [MvPolynomial.mem_support_iff]
      intro h
      rw [h, map_zero, map_zero] at hα₀
      exact zero_ne_one hα₀
    have hc : p₀.coeff α₀ = b α₀ := by
      classical
      rw [hp₀, MvPolynomial.coeff_sum]
      simp only [MvPolynomial.coeff_monomial]
      rw [Finset.sum_ite_eq' , if_pos hs]
    have hn : p₀ ∉ gI X la N := by
      unfold gI Formalism.DV.gaussIdeal
      rw [MvPolynomial.mem_map_C_iff]
      intro h
      have := val_lt_one v (φ.comp (algebraMap (X.Ol la) (X.Kl la))) g1 hϖ g2 (h α₀)
      rw [hc, RingHom.comp_apply, hb, ← hf', hα₀] at this
      exact lt_irrefl _ this
    have hu : IsUnit (algebraMap (Pol X la N) (Op X la N) p₀) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff (Op X la N) (gI X la N) p₀).2 hn
    have := val_unit v (ψ.comp (algebraMap (Op X la N) (Kp X la N))) h1 hu
    rw [← this]
    congr 1
    rw [MvPolynomial.eval₂_eq, hp₀, map_sum, map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [MvPolynomial.monomial_eq, map_mul, map_mul, eC, hf', ← hb, hφ, RingHom.comp_apply, e1, Finsupp.prod,
      map_prod, map_prod]
    simp only [map_pow]
    rfl
  · intro c γ hγ
    obtain ⟨n, hn⟩ := exists_pow_lt₀ g2 (Units.mk0 γ hγ)
    have ht : algebraMap (X.Ol la) (X.Kl la) (unif X la) ^ n ≠ 0 := by
      refine pow_ne_zero _ ?_
      rw [Ne, IsFractionRing.to_map_eq_zero_iff]
      exact hϖ.ne_zero
    obtain ⟨a, y, hy⟩ := exists_approx la (algebraMap (X.Ol la) (X.Kl la) c) _ ht
    refine ⟨a, ?_⟩
    rw [IsScalarTower.algebraMap_apply (X.Ol la) (X.Kl la) (Kp X la N)]
    change v (φ _ - φ _) < γ
    rw [← map_sub, hy, map_mul, map_mul, map_pow, map_pow]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (g1 y)) hn
  · intro S hO hT
    have hP : ∀ q : Pol X la N,
        ψ (algebraMap (Op X la N) (Kp X la N) (algebraMap (Pol X la N) (Op X la N) q)) ∈ S := by
      intro q
      induction q using MvPolynomial.induction_on with
      | C a => rw [eC]; exact hO a
      | add p q hp hq => simp only [map_add]; exact S.add_mem hp hq
      | mul_X p i hp => simp only [map_mul]; exact S.mul_mem hp (hT i)
    have hA : ∀ x : Op X la N, ψ (algebraMap (Op X la N) (Kp X la N) x) ∈ S := by
      intro x
      obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj (gI X la N).primeCompl x
      have hs : ψ (algebraMap (Op X la N) (Kp X la N) (algebraMap (Pol X la N) (Op X la N) s)) ≠ 0 :=
        (((IsLocalization.map_units (Op X la N) s).map _).map _).ne_zero
      have h' := congrArg (fun z => ψ (algebraMap (Op X la N) (Kp X la N) z)) h
      simp only [map_mul] at h'
      rw [eq_div_of_mul_eq hs h']
      exact S.div_mem (hP _) (hP _)
    intro c
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := Op X la N) c
    rw [map_div₀]
    exact S.div_mem (hA _) (hA _)

end GlobalTheory.GaussVal
