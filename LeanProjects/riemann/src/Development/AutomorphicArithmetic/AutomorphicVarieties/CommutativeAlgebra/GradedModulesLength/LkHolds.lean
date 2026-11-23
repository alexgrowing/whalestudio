import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.NegWeightLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.Satfil
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.Latfil

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

theorem UpperTheory.V.Alg.M.lk_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    ∀ (τ : Type) [Fintype τ] (wt : τ → ℤ) (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)), IsChart0 𝒜 x wt φ →
    Q.F (Fin.last r) ∈ satSq x → ∃ 𝔮 : Ideal (mR Q), (𝔮 : Set (mR Q)) = leadKer Q wt φ ∧ (GMod.self (mGr Q)).IsHomSub 𝔮 ∧
      coefIdeal _ (RingHom.ker φ) ≤ 𝔮 ∧ (∀ b : 𝒜 0, x b = 0 → algebraMap (𝒜 0) (mR Q) b ∈ 𝔮) ∧
      (∀ c : O, c ≠ 0 → ∀ p, algebraMap (𝒜 0) (mR Q) (algebraMap O (𝒜 0) c) * p ∈ 𝔮 → p ∈ 𝔮) ∧
      ∀ (f g : A) (hf : f ∈ 𝒜 (-1)) (hg : g ∈ 𝒜 (-1)), f - g ∈ satSq x →
        sec (mN 𝒜 (Q.F (Fin.last r))) 0 (f ^ 2) (sq_mem_neg 𝒜 hf) - sec (mN 𝒜 (Q.F (Fin.last r))) 0 (g ^ 2) (sq_mem_neg 𝒜 hg) ∈ 𝔮 := by
  classical
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x hW r s r' s' m Q τ _ wt φ hφ hF
  have hsat := satfil_holds O A 𝒜 x hW τ wt φ hφ
  have hlat := latfil_holds O A 𝒜 x hW τ wt φ hφ _ (Q.hF (Fin.last r)) hF
  have hmul : ∀ (a b : ℕ) (g h : MvPowerSeries τ (FractionRing O)), g ∈ fil (FractionRing O) wt a →
      h ∈ fil (FractionRing O) wt b → g * h ∈ fil (FractionRing O) wt (a + b) :=
    fun a b g h hg hh => (fil_holds _ τ wt a b g h hg hh).1
  have h0 : ∀ g : MvPowerSeries τ (FractionRing O), g ∈ fil (FractionRing O) wt 0 :=
    fun g ν hν => absurd hν (Nat.not_lt_zero _)
  let 𝔮 : Ideal (mR Q) :=
    { carrier := leadKer Q wt φ
      add_mem' := fun {p q} hp hq μ => by
        show φ (MvPolynomial.coeff μ (p.1 + q.1)) ∈ _
        rw [MvPolynomial.coeff_add, map_add]
        exact add_mem (hp μ) (hq μ)
      zero_mem' := fun μ => by
        show φ 0 ∈ _
        rw [map_zero φ]; exact zero_mem _
      smul_mem' := fun c p hp μ => by
        show φ (MvPolynomial.coeff μ (c.1 * p.1)) ∈ _
        rw [MvPolynomial.coeff_mul, map_sum]
        refine Submodule.sum_mem _ fun d hd => ?_
        rw [map_mul]
        have h1 := hmul _ _ _ _ (hlat d.1 _ (c.2 d.1)).2 (hp d.2)
        have h2 : d.1 + d.2 = μ := Finset.HasAntidiagonal.mem_antidiagonal.1 hd
        have h3 : 2 * μ 0 + 4 * μ 2 + 1 = 2 * d.1 0 + 4 * d.1 2 + (2 * d.2 0 + 4 * d.2 2 + 1) := by
          rw [← h2, Finsupp.add_apply, Finsupp.add_apply]; ring
        rw [h3]; exact h1 }
  have hmono : ∀ (μ : Fin 3 →₀ ℕ) (p : mR Q) (f : A), p.1 = MvPolynomial.monomial μ f →
      φ f ∈ fil (FractionRing O) wt (2 * μ 0 + 4 * μ 2 + 1) → p ∈ 𝔮 := by
    intro μ p f hp h ν
    rw [hp, MvPolynomial.coeff_monomial]
    split_ifs with h1
    · rw [← h1]; exact h
    · rw [map_zero φ]; exact zero_mem _
  refine ⟨𝔮, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · refine le_antisymm (fun p hp => ?_) (Submodule.span_le.2 fun p hp => hp.1)
    rw [eq_sum_mono _ p]
    exact Submodule.sum_mem _ fun μ _ =>
      Submodule.subset_span ⟨hmono μ _ _ rfl (hp μ), toDeg μ, mono_mem _ μ _ _⟩
  · intro p hp μ
    have : φ (MvPolynomial.coeff μ p.1) = 0 := hp μ
    rw [this]; exact zero_mem _
  · intro b hb
    exact hmono 0 _ b.1 rfl (hsat.2 b.1 b.2 hb)
  · intro c hc p hp μ
    have h1 : φ (MvPolynomial.coeff μ (MvPolynomial.C (algebraMap O A c) * p.1)) ∈ _ := hp μ
    rw [MvPolynomial.coeff_C_mul, map_mul, AlgHom.commutes, ← Algebra.smul_def,
      ← algebraMap_smul (FractionRing O)] at h1
    have hc' : algebraMap O (FractionRing O) c ≠ 0 := by
      simpa using hc
    exact (Submodule.smul_mem_iff _ hc').1 h1
  · intro f g hf hg hfg
    refine hmono (Finsupp.single 0 1) _ (f ^ 2 - g ^ 2) ?_ ?_
    · rw [map_sub]; rfl
    · have h1 := hsat.1 _ (sub_mem hf hg) hfg
      have h2 := (fil_holds _ τ wt 0 0 _ _ (h0 (φ (f + g))) (h0 0)).2 _ (hφ.graded _ _ (add_mem hf hg))
      have h3 := hmul _ _ _ _ h1 h2
      rw [← map_mul] at h3
      have h4 : f ^ 2 - g ^ 2 = (f - g) * (f + g) := by ring
      rw [h4]
      simpa using h3
