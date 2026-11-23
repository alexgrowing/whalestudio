import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinOfPI
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StandardPolynomialVanishesOnBicommutant
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.BicommutantRestrictionPrime
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NoOrthogonalIdempotents
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsMinimalOfOrthogonalBound
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SchurOnMinimalSubspace
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StarProjectionCommute

noncomputable section

open CompanionTheory.D.gk.admitted (stdPoly)
open CompanionTheory.Rg.Fl GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RgFl

theorem proj_comm_of_star_closed {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {N : Set (H →L[ℂ] H)} (hN : ∀ T ∈ N, star T ∈ N) (S : Submodule ℂ H) [S.HasOrthogonalProjection]
    (hS : ∀ T ∈ N, ∀ v ∈ S, T v ∈ S) (T : H →L[ℂ] H) (hT : T ∈ N) :
    T * S.starProjection = S.starProjection * T := by
  ext v
  have hperp : ∀ u, u ∈ Sᗮ → T u ∈ Sᗮ := by
    intro u hu
    rw [Submodule.mem_orthogonal] at hu ⊢
    intro w hw
    have h1 : ⟪w, T u⟫_ℂ = ⟪star T w, u⟫_ℂ := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    rw [h1]
    exact hu _ (hS _ (hN T hT) _ hw)
  show T (S.starProjection v) = S.starProjection (T v)
  symm
  apply Submodule.eq_starProjection_of_mem_orthogonal (hS T hT _ (S.starProjection_apply_mem v))
  rw [← map_sub]
  exact hperp _ (S.sub_starProjection_mem_orthogonal v)

theorem stFactor_from (h1 : ∀ (G H : Type) [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G →* (H →L[ℂ] H)),
    (∀ g v, ‖σ g v‖ = ‖v‖) → ∀ (E : H →L[ℂ] H) (m : ℕ), (∀ g : Fin m → G, stdPoly E (fun i => σ (g i)) = 0) →
    ∀ a : Fin m → (H →L[ℂ] H), (∀ i, ∀ T : H →L[ℂ] H, (∀ g, T * σ g = σ g * T) → T * a i = a i * T) → stdPoly E a = 0) (h2 : ∀ (G G₁ H : Type) [Group G] [Group G₁] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : G →* (H →L[ℂ] H)), IsTopIrreducible π → ∀ (j : G₁ →* G) (p : G →* G₁),
    (∀ x, p (j x) = x) → (∀ x g, p g = 1 → Commute (j x) g) → ∀ x y : H →L[ℂ] H,
    (∀ T : H →L[ℂ] H, (∀ g, T * π (j g) = π (j g) * T) → T * y = y * T) → y ≠ 0 →
    (∀ g, x * π (j g) * y = 0) → x = 0) (h3 : ∀ (R : Type) [Ring R] (A S : Set R) (E : R) (m : ℕ) (q : Fin (m + 1) → R),
    (∀ a ∈ A, ∀ b ∈ A, a * b ∈ A) → S ⊆ A →
    (∀ x ∈ A, ∀ y ∈ A, y ≠ 0 → (∀ s ∈ S, x * s * y = 0) → x = 0) →
    (∀ a : Fin m → R, (∀ i, a i ∈ A) → stdPoly E a = 0) →
    (∀ i, q i ∈ A) → (∀ i, q i ≠ 0) → (∀ i, q i * q i = q i) → (∀ i k, i ≠ k → q i * q k = 0) →
    (∀ i, E * q i = q i) → False) (h4 : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (L : Set (Submodule ℂ H)) (m : ℕ)
    (S₀ : Submodule ℂ H), (∀ S ∈ L, IsClosed (S : Set H)) → (∀ S ∈ L, ∀ T ∈ L, S ⊓ Tᗮ ∈ L) → S₀ ∈ L → S₀ ≠ ⊥ →
    (∀ f : Fin (m + 1) → Submodule ℂ H, (∀ i, f i ∈ L) → (∀ i, f i ≠ ⊥) → ¬ Pairwise fun i k => f i ⟂ f k) →
    ∃ Q ∈ L, Q ≠ ⊥ ∧ ∀ T ∈ L, T ≤ Q → T = ⊥ ∨ T = Q) (h5 : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (N : Set (H →L[ℂ] H))
    (Q : Submodule ℂ H), (∀ T ∈ N, star T ∈ N) → IsClosed (Q : Set H) → (∀ T ∈ N, ∀ v ∈ Q, T v ∈ Q) →
    (∀ U : Submodule ℂ H, IsClosed (U : Set H) → U ≤ Q → (∀ T ∈ N, ∀ v ∈ U, T v ∈ U) → U = ⊥ ∨ U = Q) →
    ∀ A : H →L[ℂ] H, (∀ T ∈ N, T * A = A * T) → ∃ c : ℂ, ∀ v ∈ Q, A v - c • v ∈ Qᗮ) (h6 : ∀ (G H : Type) [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G →* (H →L[ℂ] H)),
    (∀ g v, ‖σ g v‖ = ‖v‖) → ∀ (Q : Submodule ℂ H) (ξ : H), IsClosed (Q : Set H) → ξ ∈ Q → ξ ≠ 0 →
    (∀ T : H →L[ℂ] H, (∀ g, T * σ g = σ g * T) → ∀ v ∈ Q, T v ∈ Q) →
    (∀ g, ∃ c : ℂ, σ g ξ - c • ξ ∈ Qᗮ) → ∃ W, IsIrredSubrep σ W) : StFactor := by
  intro G G₁ H _ _ _ _ _ π hπ hirr j p hpj hcomm E hE
  obtain ⟨hE0, hEE, hEadj, hEc, m, hm⟩ := hE
  set ρ : G₁ →* (H →L[ℂ] H) := π.comp j with hρdef
  have hρ : ∀ g v, ‖ρ g v‖ = ‖v‖ := fun g v => hπ _ v
  let N : Set (H →L[ℂ] H) := {T | ∀ g, T * ρ g = ρ g * T}
  let A : Set (H →L[ℂ] H) := {T | ∀ n ∈ N, n * T = T * n}
  have hN : ∀ T ∈ N, star T ∈ N := by
    intro T hT g
    have h := congrArg star (hT g⁻¹)
    simp only [star_mul, CompanionTheory.D.gk.admitted.FinOfPIAux.star_eq ρ hρ, inv_inv] at h
    exact h.symm
  have hAmul : ∀ a ∈ A, ∀ b ∈ A, a * b ∈ A := by
    intro a ha b hb n hn
    rw [← mul_assoc, ha n hn, mul_assoc, hb n hn, mul_assoc]
  have hSA : Set.range ρ ⊆ A := by
    rintro _ ⟨g, rfl⟩ n hn
    exact hn g
  have hprime : ∀ x ∈ A, ∀ y ∈ A, y ≠ 0 → (∀ s ∈ Set.range ρ, x * s * y = 0) → x = 0 := by
    intro x _ y hy hy0 h
    exact h2 G G₁ H π hirr j p hpj hcomm x y (fun T hT => hy T hT) hy0 (fun g => h _ ⟨g, rfl⟩)
  have hPI : ∀ a : Fin m → (H →L[ℂ] H), (∀ i, a i ∈ A) → stdPoly E a = 0 :=
    fun a ha => h1 G₁ H ρ hρ E m hm a fun i T hT => ha i T hT
  let R : Submodule ℂ H := LinearMap.range (E : H →ₗ[ℂ] H)
  have hRmem : ∀ v, v ∈ R ↔ E v = v := by
    intro v
    constructor
    · rintro ⟨w, rfl⟩
      exact DFunLike.congr_fun hEE w
    · intro h
      exact ⟨v, h⟩
  have hRcl : IsClosed (R : Set H) := by
    have : (R : Set H) = {v | E v = v} := Set.ext hRmem
    rw [this]
    exact isClosed_eq E.continuous continuous_id
  let L : Set (Submodule ℂ H) :=
    {S | IsClosed (S : Set H) ∧ (∀ T ∈ N, ∀ v ∈ S, T v ∈ S) ∧ S ≤ R}
  have hRL : R ∈ L := by
    refine ⟨hRcl, fun T hT v hv => ?_, le_rfl⟩
    rw [hRmem] at hv ⊢
    have := DFunLike.congr_fun (hEc T hT) v
    simp only [mul_apply_eq_comp] at this
    rw [← this, hv]
  have hR0 : R ≠ ⊥ := by
    intro h
    apply hE0
    ext v
    have : E v ∈ R := ⟨v, rfl⟩
    rw [h] at this
    simpa using this
  have hLinf : ∀ S ∈ L, ∀ T ∈ L, S ⊓ Tᗮ ∈ L := by
    rintro S ⟨hS1, hS2, hS3⟩ U ⟨hU1, hU2, hU3⟩
    refine ⟨hS1.inter U.isClosed_orthogonal, fun T hT v hv => ⟨hS2 T hT v hv.1, ?_⟩, inf_le_left.trans hS3⟩
    have hv2 : v ∈ Uᗮ := hv.2
    show T v ∈ Uᗮ
    rw [Submodule.mem_orthogonal] at hv2 ⊢
    intro w hw
    have h1 : ⟪w, T v⟫_ℂ = ⟪star T w, v⟫_ℂ := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    rw [h1]
    exact hv2 _ (hU2 _ (hN T hT) _ hw)
  have hbound : ∀ f : Fin (m + 1) → Submodule ℂ H, (∀ i, f i ∈ L) → (∀ i, f i ≠ ⊥) →
      ¬ Pairwise fun i k => f i ⟂ f k := by
    intro f hf hf0 hp
    have hc : ∀ i, CompleteSpace (f i) := fun i => (hf i).1.completeSpace_coe
    refine h3 (H →L[ℂ] H) A (Set.range ρ) E m (fun i => (f i).starProjection) hAmul hSA hprime hPI
      (fun i n hn => proj_comm_of_star_closed hN (f i) (hf i).2.1 n hn) (fun i h0 => hf0 i ?_) (fun i => ?_) (fun i k hik => ?_)
      (fun i => ?_)
    · rw [Submodule.eq_bot_iff]
      intro v hv
      have := Submodule.starProjection_eq_self_iff.mpr hv
      rw [← this, h0]
      rfl
    · ext v
      exact Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ v) |> fun h => h
    · ext v
      have hv : (f k).starProjection v ∈ (f i)ᗮ :=
        (hp hik).symm ((f k).starProjection_apply_mem v)
      exact Submodule.eq_starProjection_of_mem_orthogonal (zero_mem _) (by simpa using hv)
    · ext v
      exact (hRmem _).mp ((hf i).2.2 ((f i).starProjection_apply_mem v))
  obtain ⟨Q, hQL, hQ0, hQmin⟩ := h4 H L m R (fun S hS => hS.1) hLinf hRL hR0 hbound
  obtain ⟨ξ, hξ, hξ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ0
  refine h6 G₁ H ρ hρ Q ξ hQL.1 hξ hξ0 (fun T hT v hv => hQL.2.1 T hT v hv) (fun g => ?_)
  obtain ⟨c, hc⟩ := h5 H N Q hN hQL.1 hQL.2.1
    (fun U hU1 hU2 hU3 => hQmin U ⟨hU1, hU3, hU2.trans hQL.2.2⟩ hU2) (ρ g) (fun T hT => hT g)
  exact ⟨c, hc ξ hξ⟩

theorem stFactor : StFactor :=
  stFactor_from GlobalTheory.CompanionTheory.Factor.stdPoly_bicomm GlobalTheory.CompanionTheory.DirectFactor.bicommutant_restriction_prime GlobalTheory.CompanionTheory.PrimeRing.StdChain.no_orthogonal_idempotents GlobalTheory.CompanionTheory.OrthoFamily.exists_minimal_of_orthogonal_bound GlobalTheory.CompanionTheory.Factor.schur_on_minimal_subspace GlobalTheory.CompanionTheory.CyclicScalar.exists_isIrredSubrep

end GlobalTheory.CompanionTheory.RgFl

end
