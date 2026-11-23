import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.KjMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SmulPowLeOfStep
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FiniteModuleMaximalIdealAnnihilation
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem exists_pow_maximalIdeal_smul_finite_eq_zero (R Q : Type) [CommRing R] [IsLocalRing R] [AddCommGroup Q] [Module R Q] [Finite Q] :
    ∃ c : ℕ, ∀ a ∈ maximalIdeal R ^ c, ∀ z : Q, a • z = 0 :=
  _root_.UpperTheory.Reformulated.B.FiniteModuleMaximalIdealAnnihilation.exists_pow_maximalIdeal_smul_finite_eq_zero R Q

private theorem finite_quotient_of_power_maximal_ideal_le (Λ R X : Type) [CommRing Λ] [IsLocalRing Λ] [CommRing R] [IsNoetherianRing Λ]
    [Finite (ResidueField Λ)] [AddCommGroup X] [Module R X] [Module Λ X] [Module.Finite Λ X] (t : Λ →+* R)
    (ht : ∀ (a : Λ) (x : X), a • x = t a • x) (j : ℕ) (K : Ideal R) (hK : (maximalIdeal Λ).map t ^ j ≤ K) :
    Finite (X ⧸ (K • ⊤ : Submodule R X)) := by
  haveI h0 : Finite (Λ ⧸ maximalIdeal Λ) := ‹Finite (ResidueField Λ)›
  haveI h1 : Finite (Λ ⧸ maximalIdeal Λ ^ j) := Ideal.finite_quotient_pow (IsNoetherian.noetherian _) j
  haveI h2 : Finite (X ⧸ (maximalIdeal Λ ^ j • ⊤ : Submodule Λ X)) :=
    Submodule.finite_quotient_smul _ (Module.Finite.fg_top)
  have hle : ∀ x ∈ (maximalIdeal Λ ^ j • ⊤ : Submodule Λ X), x ∈ (K • ⊤ : Submodule R X) := by
    intro x hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro a ha y _
      rw [ht]
      refine Submodule.smul_mem_smul (hK ?_) Submodule.mem_top
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ ha
    · intro a b ha hb
      exact Submodule.add_mem _ ha hb
  let g : (X ⧸ (maximalIdeal Λ ^ j • ⊤ : Submodule Λ X)) → (X ⧸ (K • ⊤ : Submodule R X)) := fun q =>
    Quotient.liftOn' q (fun x => Submodule.Quotient.mk x)
      (fun a b h => (Submodule.Quotient.eq _).2 (hle _ ((Submodule.quotientRel_def _).1 h)))
  refine Finite.of_surjective g fun z => ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  exact ⟨Submodule.Quotient.mk x, rfl⟩

theorem UpperTheory.V.Pa.Core.finite_quotient_of_ultrafilter_limit_module :
    ∀ (Λ R σ : Type) [CommRing Λ] [IsLocalRing Λ] [CommRing R] [Fintype σ] (s : MvPowerSeries σ Λ →+* R) [IsNoetherianRing Λ] [Finite (ResidueField Λ)] [IsLocalRing R] (U : Ultrafilter ℕ) (f : R) (M : ℕ → Type) [∀ N, AddCommGroup (M N)] [∀ N, Module R (M N)] (X : Type) [AddCommGroup X] [Module R X] [Module Λ X] [Module.Finite Λ X], (∀ (a : Λ) (x : X), a • x = s (MvPowerSeries.C a) • x) → (∀ a (x : X), s (MvPowerSeries.X a) • x = 0) → (∀ j, ∀ᶠ N in (U : Filter ℕ), ∃ (φ : (X ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R X)) →ₗ[R] (M N ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R (M N)))) (ψ : (M N ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R (M N))) →ₗ[R] (X ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R X))), (∀ z, φ (ψ z) = f • z) ∧ ∀ z, ψ (φ z) = f • z) → ∀ k j : ℕ, ∃ c : ℕ, ∀ᶠ N in (U : Filter ℕ), ∀ a ∈ maximalIdeal R ^ c, ∀ x : M N, (f ^ k * a) • x ∈ ((Ideal.span (Set.range (fun a => s (MvPowerSeries.X a))) ^ k ⊔ ((maximalIdeal Λ).map (s.comp MvPowerSeries.C)) ^ j) • ⊤ : Submodule R (M N)) := by
  intro Λ R σ _ _ _ _ s _ _ _ U f M _ _ X _ _ _ _ hC _ h k j
  have hK := kjMap Λ R σ s 1 j
  haveI : Finite (X ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R X)) :=
    finite_quotient_of_power_maximal_ideal_le Λ R X (s.comp MvPowerSeries.C) hC j _ (hK ▸ le_sup_right)
  obtain ⟨c, hc⟩ := exists_pow_maximalIdeal_smul_finite_eq_zero R (X ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R X))
  refine ⟨c * k, (h j).mono ?_⟩
  rintro N ⟨φ, ψ, hφψ, -⟩ a ha x
  have h1 : ((Ideal.span {f} * maximalIdeal R ^ c) • ⊤ : Submodule R (M N)) ≤ (kjIdeal Λ σ 1 j).map s • ⊤ := by
    refine Submodule.smul_le.2 ?_
    intro r hr y _
    obtain ⟨b, hb, rfl⟩ := Ideal.mem_span_singleton_mul.1 hr
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul, mul_comm, mul_smul, ← hφψ, ← map_smul,
      hc b hb, map_zero]
  rw [hK, pow_one, sup_comm] at h1
  have h2 := (smul_pow_le_of_step R (maximalIdeal R ^ c) _ _ f).2 (M N) h1 k
  rw [sup_comm]
  refine h2 (Submodule.smul_mem_smul (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) ?_) Submodule.mem_top)
  rwa [← pow_mul]
