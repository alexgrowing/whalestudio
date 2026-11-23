import Mathlib
open MeasureTheory
open scoped NNReal ENNReal

namespace GlobalTheory.CompanionTheory.TopGroup

theorem homeomorph_prod_of_closed_complements :
    ∀ (Q : Type) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q]
      [T2Space Q] [SecondCountableTopology Q] (N M : Subgroup Q),
      IsClosed (N : Set Q) → IsClosed (M : Set Q) → (∀ q, ∃ n ∈ N, ∃ m ∈ M, q = n * m) →
      (∀ x, x ∈ N → x ∈ M → x = 1) →
      ∃ Φ : (N × M) ≃ₜ Q, ∀ p, Φ p = (p.1 : Q) * (p.2 : Q) := by
  intro Q _ _ _ _ _ _ N M hN hM hprod hint
  haveI : LocallyCompactSpace N := hN.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace M := hM.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology N :=
    TopologicalSpace.Subtype.secondCountableTopology (N : Set Q)
  haveI : SecondCountableTopology M :=
    TopologicalSpace.Subtype.secondCountableTopology (M : Set Q)
  haveI : SigmaCompactSpace (N × M) := sigmaCompactSpace_of_locallyCompact_secondCountable
  letI act : MulAction (N × M) Q :=
    { smul := fun p q => (p.1 : Q) * q * (p.2 : Q)⁻¹
      one_smul := fun q => by
        change ((1 : N) : Q) * q * ((1 : M) : Q)⁻¹ = q
        simp
      mul_smul := fun p r q => by
        change ((p.1 * r.1 : N) : Q) * q * ((p.2 * r.2 : M) : Q)⁻¹ =
          (p.1 : Q) * ((r.1 : Q) * q * (r.2 : Q)⁻¹) * (p.2 : Q)⁻¹
        simp [mul_assoc] }
  have hsmul : ∀ (p : N × M) (q : Q), p • q = (p.1 : Q) * q * (p.2 : Q)⁻¹ := fun _ _ => rfl
  haveI : ContinuousSMul (N × M) Q := ⟨by
    have : (fun x : (N × M) × Q => x.1 • x.2) =
        fun x : (N × M) × Q => ((x.1.1 : Q)) * x.2 * ((x.1.2 : Q))⁻¹ := rfl
    rw [this]
    fun_prop⟩
  haveI : MulAction.IsPretransitive (N × M) Q := ⟨fun x y => by
    obtain ⟨n₁, hn₁, m₁, hm₁, rfl⟩ := hprod x
    obtain ⟨n₂, hn₂, m₂, hm₂, rfl⟩ := hprod y
    refine ⟨(⟨n₂ * n₁⁻¹, N.mul_mem hn₂ (N.inv_mem hn₁)⟩,
      ⟨m₂⁻¹ * m₁, M.mul_mem (M.inv_mem hm₂) hm₁⟩), ?_⟩
    rw [hsmul]
    simp [mul_assoc]⟩
  have hopen₀ : IsOpenMap (fun g : N × M => g • (1 : Q)) := isOpenMap_smul_of_sigmaCompact (1 : Q)
  let e : (N × M) ≃ₜ (N × M) := (Homeomorph.refl N).prodCongr (Homeomorph.inv M)
  let f : N × M → Q := fun p => (p.1 : Q) * (p.2 : Q)
  have hf : f = (fun g : N × M => g • (1 : Q)) ∘ e := by
    funext p
    change (p.1 : Q) * (p.2 : Q) = ((e p).1 : Q) * 1 * (((e p).2 : M) : Q)⁻¹
    simp [e]
  have hopen : IsOpenMap f := by
    rw [hf]
    exact hopen₀.comp e.isOpenMap
  have hcont : Continuous f := by fun_prop
  have hinj : Function.Injective f := by
    rintro ⟨⟨n₁, hn₁⟩, ⟨m₁, hm₁⟩⟩ ⟨⟨n₂, hn₂⟩, ⟨m₂, hm₂⟩⟩ h
    have h' : n₁ * m₁ = n₂ * m₂ := h
    have h1 : n₂⁻¹ * n₁ = m₂ * m₁⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq, h']
    have h2 : n₂⁻¹ * n₁ = 1 :=
      hint _ (N.mul_mem (N.inv_mem hn₂) hn₁) (h1 ▸ M.mul_mem hm₂ (M.inv_mem hm₁))
    have h3 : n₁ = n₂ := by
      rw [inv_mul_eq_one] at h2
      exact h2.symm
    have h4 : m₁ = m₂ := by
      subst h3
      exact mul_left_cancel h'
    subst h3
    subst h4
    rfl
  have hsurj : Function.Surjective f := fun q => by
    obtain ⟨n, hn, m, hm, rfl⟩ := hprod q
    exact ⟨(⟨n, hn⟩, ⟨m, hm⟩), rfl⟩
  exact ⟨(Equiv.ofBijective f ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen hcont hopen,
    fun _ => rfl⟩

end GlobalTheory.CompanionTheory.TopGroup
