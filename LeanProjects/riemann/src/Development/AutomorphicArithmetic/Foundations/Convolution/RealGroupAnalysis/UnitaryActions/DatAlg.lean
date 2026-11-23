import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaLiftTrivialOrbitTermsVanish

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open scoped Classical
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.datAlg :
    ∀ (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E], Module.finrank F E = 2 →
      ∃ (δ : F) (θ : E) (σ : E ≃ₐ[F] E) (b : Module.Basis (Fin 2) F E), b 0 = 1 ∧ b 1 = θ ∧ θ ^ 2 = algebraMap F E δ ∧ σ θ = -θ := by
  intro F E _ _ _ _ h2
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  haveI : IsGalois F E := inferInstance
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  have hcard : Nat.card (E ≃ₐ[F] E) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, h2]
  obtain ⟨σ, hσ⟩ : ∃ σ : E ≃ₐ[F] E, σ ≠ 1 := by
    haveI : Finite (E ≃ₐ[F] E) := inferInstance
    haveI : Nontrivial (E ≃ₐ[F] E) := by
      apply Finite.one_lt_card_iff_nontrivial.mp
      omega
    exact exists_ne 1
  have hall : ∀ τ : E ≃ₐ[F] E, τ = 1 ∨ τ = σ := by
    intro τ
    by_contra hc
    push_neg at hc
    have h3 : 3 ≤ Nat.card (E ≃ₐ[F] E) := by
      haveI : Fintype (E ≃ₐ[F] E) := Fintype.ofFinite _
      rw [Nat.card_eq_fintype_card]
      have : ({1, σ, τ} : Finset (E ≃ₐ[F] E)).card = 3 := by
        rw [Finset.card_eq_three]
        exact ⟨1, σ, τ, hσ.symm, hc.1.symm, hc.2.symm, rfl⟩
      rw [← this]
      exact Finset.card_le_univ _
    omega
  have hσσ : σ * σ = 1 := by
    have : Monoid.exponent (E ≃ₐ[F] E) ∣ 2 := by
      rw [← hcard]; exact Group.exponent_dvd_nat_card
    have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp this σ
    rwa [pow_two] at h
  obtain ⟨α, hα⟩ : ∃ α : E, σ α ≠ α := by
    by_contra hc
    push_neg at hc
    exact hσ (AlgEquiv.ext hc)
  have hσσα : ∀ x : E, σ (σ x) = x := fun x => by
    have := congrArg (fun τ : E ≃ₐ[F] E => τ x) hσσ
    simpa using this
  set θ : E := α - σ α with hθ
  have hθ0 : θ ≠ 0 := fun h => hα (sub_eq_zero.mp h).symm
  have hσθ : σ θ = -θ := by
    simp [hθ, hσσα]
  have hfix : θ ^ 2 ∈ Set.range (algebraMap F E) := by
    have hb : θ ^ 2 ∈ (⊥ : IntermediateField F E) := by
      rw [IsGalois.mem_bot_iff_fixed]
      intro τ
      rcases hall τ with rfl | rfl
      · simp
      · rw [map_pow, hσθ]; ring
    exact IntermediateField.mem_bot.mp hb
  obtain ⟨δ, hδ⟩ := hfix
  have hli : LinearIndependent F ![(1 : E), θ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : algebraMap F E s + algebraMap F E t * θ = 0 := by
      simpa [Algebra.smul_def] using hst
    have h2' : algebraMap F E s - algebraMap F E t * θ = 0 := by
      have := congrArg σ h1
      simpa [hσθ, sub_eq_add_neg] using this
    have hs2 : (2 : E) * algebraMap F E s = 0 := by linear_combination h1 + h2'
    have ht2 : (2 : E) * (algebraMap F E t * θ) = 0 := by linear_combination h1 - h2'
    have hs : s = 0 := by
      have : algebraMap F E s = 0 := by
        rcases mul_eq_zero.mp hs2 with h | h
        · exact absurd h two_ne_zero
        · exact h
      simpa using this
    have ht : t = 0 := by
      have : algebraMap F E t = 0 := by
        rcases mul_eq_zero.mp ht2 with h | h
        · exact absurd h two_ne_zero
        · rcases mul_eq_zero.mp h with h | h
          · exact h
          · exact absurd h hθ0
      simpa using this
    exact ⟨hs, ht⟩
  refine ⟨δ, θ, σ, basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2]), ?_, ?_, hδ.symm, hσθ⟩
  · simp
  · simp
