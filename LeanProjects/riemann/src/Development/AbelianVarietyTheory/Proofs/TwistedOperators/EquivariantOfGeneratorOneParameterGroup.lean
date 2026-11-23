import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealIntertwinerOfCompactGroupIntertwiner

noncomputable section

namespace GlobalTheory.OneParamEquivariance

theorem hasDerivAt_apply {F : Type*} [AddCommGroup F] [Module ℂ F] [FiniteDimensional ℂ F]
    (A : ℝ → F →ₗ[ℂ] ℂ) (A' : F →ₗ[ℂ] ℂ) (c : ℝ → F) (c' : F)
    (hA : ∀ x, HasDerivAt (fun t => A t x) (A' x) 0)
    (hc : ∀ f : F →ₗ[ℂ] ℂ, HasDerivAt (fun t => f (c t)) (f c') 0) :
    HasDerivAt (fun t => A t (c t)) (A' (c 0) + A 0 c') 0 := by
  let b := Module.finBasis ℂ F
  have e : ∀ (a : F →ₗ[ℂ] ℂ) u, a u = ∑ i, a (b i) * b.coord i u := by
    intro a u
    conv_lhs => rw [← b.sum_repr u, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
    rfl
  have := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (hA (b i)).fun_mul (hc (b.coord i))
  have e1 : (fun t => A t (c t)) = fun t => ∑ i, A t (b i) * b.coord i (c t) := funext fun t => e _ _
  rw [e1, e A' (c 0), e (A 0) c', ← Finset.sum_add_distrib]
  exact this

theorem equivariant_of_generator : ∀ (σ Z H : Type) [Finite σ] [AddCommGroup H] [Module ℂ H] (pt : MvPolynomial σ ℂ →ₗ[ℂ] (Z → ℂ)) (R : ℝ → Module.End ℂ (Z → ℂ)) (L : Module.End ℂ (MvPolynomial σ ℂ)) (U : ℝ → Module.End ℂ H) (B : MvPolynomial σ ℂ →ₗ[ℂ] H) (Λ : Set (H →ₗ[ℂ] ℂ)), Function.Injective pt → R 0 = 1 → (∀ s t, R (s + t) = R s * R t) → (∀ t φ, ∃ ψ, ψ.totalDegree ≤ φ.totalDegree ∧ R t (pt φ) = pt ψ) → (∀ φ z, HasDerivAt (fun t : ℝ => R t (pt φ) z) (pt (L φ) z) 0) → U 0 = 1 → (∀ s t, U (s + t) = U s * U t) → (∀ x, (∀ l ∈ Λ, l x = 0) → x = 0) → (∀ l ∈ Λ, ∀ t, l ∘ₗ U t ∈ Λ) → (∀ l ∈ Λ, ∀ φ, HasDerivAt (fun t : ℝ => l (U t (B φ))) (l (B (L φ))) 0) → ∀ φ φ', pt φ' = R 1 (pt φ) → B φ' = U 1 (B φ) := by
  intro σ Z H _ _ _ pt R L U B Λ hpt hR0 hR hdeg hder hU0 hU hsep hΛ hB φ φ' hφ
  choose ρ hρd hρ using hdeg
  have hρ0 : ∀ ψ, ρ 0 ψ = ψ := fun ψ => hpt (by rw [← hρ, hR0]; rfl)
  have hρadd : ∀ s t ψ, ρ (s + t) ψ = ρ s (ρ t ψ) := fun s t ψ => hpt (by
    rw [← hρ, ← hρ, ← hρ, hR]; rfl)
  have key : ∀ l ∈ Λ, ∀ ψ, HasDerivAt (fun s : ℝ => l (U (-s) (B (ρ s ψ)))) 0 0 := by
    intro l hl ψ
    let F := MvPolynomial.restrictTotalDegree σ ℂ (max ψ.totalDegree (L ψ).totalDegree)
    have hc : ∀ s, ρ s ψ ∈ F := fun s =>
      (MvPolynomial.mem_restrictTotalDegree _ _ _).2 ((hρd s ψ).trans (le_max_left _ _))
    have hy : L ψ ∈ F := (MvPolynomial.mem_restrictTotalDegree _ _ _).2 (le_max_right _ _)
    have h1 := GlobalTheory.CompactIntertwiner.hasDerivAt_dual_of_sep (F := F)
      (fun z => (LinearMap.proj z ∘ₗ pt) ∘ₗ F.subtype)
      (fun x hx => Subtype.ext (hpt (by rw [Submodule.coe_zero, map_zero]; exact funext hx)))
      (fun s => ⟨ρ s ψ, hc s⟩) ⟨L ψ, hy⟩ (fun z => by
        have := hder ψ z
        simp only [hρ] at this
        exact this)
    have h2 : ∀ x : F, HasDerivAt (fun s : ℝ => (l ∘ₗ U (-s) ∘ₗ B ∘ₗ F.subtype) x)
        ((-(l ∘ₗ B ∘ₗ L ∘ₗ F.subtype)) x) 0 := by
      intro x
      have h3 : HasDerivAt (fun t : ℝ => l (U t (B x))) (l (B (L x))) (-0) := by
        rw [neg_zero]; exact hB l hl x
      have h4 := h3.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
      rw [neg_one_smul] at h4
      exact h4
    have h5 := hasDerivAt_apply _ _ _ _ h2 h1
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.neg_apply, hρ0, neg_zero, hU0,
      Module.End.one_apply, neg_add_cancel] at h5
    exact h5
  have hconst : ∀ l ∈ Λ, l (U (-1) (B (ρ 1 φ))) = l (B φ) := by
    intro l hl
    have hd : ∀ t₀ : ℝ, HasDerivAt (fun t : ℝ => l (U (-t) (B (ρ t φ)))) 0 t₀ := by
      intro t₀
      have h1 : HasDerivAt (fun s : ℝ => (l ∘ₗ U (-t₀)) (U (-s) (B (ρ s (ρ t₀ φ))))) 0 (t₀ - t₀) := by
        rw [sub_self]; exact key _ (hΛ l hl _) _
      have h2 := h1.comp_sub_const t₀ t₀
      refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      have e : -t₀ + -(t - t₀) = -t := by ring
      beta_reduce
      rw [← hρadd, sub_add_cancel, LinearMap.comp_apply, ← Module.End.mul_apply, ← hU, e]
    have := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) 1 0
    simpa [hρ0, hU0] using this
  have h1 : U (-1) (B (ρ 1 φ)) = B φ :=
    sub_eq_zero.1 (hsep _ fun l hl => by rw [map_sub, hconst l hl, sub_self])
  have h2 : φ' = ρ 1 φ := hpt (by rw [hφ, hρ])
  rw [← h1, ← Module.End.mul_apply, ← hU, add_neg_cancel, hU0, h2]
  rfl

end GlobalTheory.OneParamEquivariance

end
