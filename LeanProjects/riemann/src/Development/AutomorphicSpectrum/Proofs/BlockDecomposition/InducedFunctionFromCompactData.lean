import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EGPgTrueEqLastIff
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes.TwoOrbit

theorem exists_equivariant_extension :
    ∀ {G : Type} [Group G] {W₁ : Type} [AddCommGroup W₁] [Module ℂ W₁] {Q P : Subgroup G} {x : G} (σ : Representation ℂ Q W₁) (φ : P → W₁) (C : Set P) (K : Subgroup G), (∀ c ∈ C, ∀ κ ∈ K, ∀ (q : Q) (p' : P), (q : G) * x * (c : G) * κ = x * (p' : G) → φ p' = σ q (φ c)) → (∀ p : P, φ p ≠ 0 → ∃ c ∈ C, ∃ q : Q, x * (p : G) = (q : G) * x * (c : G)) → ∃ f : G → W₁, (∀ (q : Q) (g : G), f ((q : G) * g) = σ q (f g)) ∧ (∀ (g : G), ∀ κ ∈ K, f (g * κ) = f g) ∧ (∀ p : P, f (x * (p : G)) = φ p) ∧ ∀ g : G, f g ≠ 0 → ∃ q : Q, ∃ c ∈ C, ∃ κ ∈ K, g = (q : G) * x * (c : G) * κ := by
  intro G _ W₁ _ _ Q P x σ φ C K h1 h2
  classical
  let Ω : G → Prop := fun g =>
    ∃ (q : Q) (c : P), c ∈ C ∧ ∃ κ ∈ K, g = (q : G) * x * (c : G) * κ
  have wd : ∀ (q q' : Q) (c c' : P), c ∈ C → c' ∈ C → ∀ κ ∈ K, ∀ κ' ∈ K,
      (q : G) * x * (c : G) * κ = (q' : G) * x * (c' : G) * κ' →
        σ q (φ c) = σ q' (φ c') := by
    intro q q' c c' hc hc' κ hκ κ' hκ' e
    have e' : ((q'⁻¹ * q : Q) : G) * x * (c : G) * (κ * κ'⁻¹) = x * (c' : G) := by
      have e2 : (q : G) * x * (c : G) * κ * κ'⁻¹ = (q' : G) * x * (c' : G) := by
        rw [e]; group
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc ((q' : G)⁻¹ * q) * x * c * (κ * κ'⁻¹)
          = (q' : G)⁻¹ * ((q : G) * x * (c : G) * κ * κ'⁻¹) := by group
        _ = x * (c' : G) := by rw [e2]; group
    have e3 := h1 c hc (κ * κ'⁻¹) (K.mul_mem hκ (K.inv_mem hκ')) (q'⁻¹ * q) c' e'
    rw [e3, ← Module.End.mul_apply, ← map_mul]
    simp
  let f : G → W₁ := fun g =>
    if h : Ω g then σ h.choose (φ h.choose_spec.choose) else 0
  have hf : ∀ (q : Q) (c : P), c ∈ C → ∀ κ ∈ K,
      f ((q : G) * x * (c : G) * κ) = σ q (φ c) := by
    intro q c hc κ hκ
    have h : Ω ((q : G) * x * (c : G) * κ) := ⟨q, c, hc, κ, hκ, rfl⟩
    simp only [f]
    rw [dif_pos h]
    obtain ⟨hc', κ', hκ', e⟩ := h.choose_spec.choose_spec
    exact wd _ _ _ _ hc' hc κ' hκ' κ hκ e.symm
  have h0 : ∀ g, ¬ Ω g → f g = 0 := fun g h => dif_neg h
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · intro q g
    by_cases h : Ω g
    · obtain ⟨q₁, c, hc, κ, hκ, rfl⟩ := h
      have e : (q : G) * ((q₁ : G) * x * (c : G) * κ)
          = ((q * q₁ : Q) : G) * x * (c : G) * κ := by
        simp only [Subgroup.coe_mul]; group
      rw [e, hf _ _ hc _ hκ, hf _ _ hc _ hκ, map_mul, Module.End.mul_apply]
    · have h' : ¬ Ω ((q : G) * g) := by
        rintro ⟨q₁, c, hc, κ, hκ, e⟩
        refine h ⟨q⁻¹ * q₁, c, hc, κ, hκ, ?_⟩
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        calc g = (q : G)⁻¹ * ((q : G) * g) := by group
          _ = _ := by rw [e]; group
      rw [h0 _ h, h0 _ h', map_zero]
  · intro g κ hκ
    by_cases h : Ω g
    · obtain ⟨q₁, c, hc, κ₁, hκ₁, rfl⟩ := h
      have e : (q₁ : G) * x * (c : G) * κ₁ * κ = (q₁ : G) * x * (c : G) * (κ₁ * κ) := by group
      rw [e, hf _ _ hc _ (K.mul_mem hκ₁ hκ), hf _ _ hc _ hκ₁]
    · have h' : ¬ Ω (g * κ) := by
        rintro ⟨q₁, c, hc, κ₁, hκ₁, e⟩
        refine h ⟨q₁, c, hc, κ₁ * κ⁻¹, K.mul_mem hκ₁ (K.inv_mem hκ), ?_⟩
        calc g = (g * κ) * κ⁻¹ := by group
          _ = _ := by rw [e]; group
      rw [h0 _ h, h0 _ h']
  · intro p
    by_cases h : Ω (x * (p : G))
    · obtain ⟨q, c, hc, κ, hκ, e⟩ := h
      rw [e, hf _ _ hc _ hκ]
      exact (h1 c hc κ hκ q p e.symm).symm
    · rw [h0 _ h]
      by_contra hne
      obtain ⟨c, hc, q, e⟩ := h2 p (fun hz => hne hz.symm)
      exact h ⟨q, c, hc, 1, K.one_mem, by rw [e, mul_one]⟩
  · intro g hg
    by_contra hcon
    refine hg (h0 g ?_)
    rintro ⟨q, c, hc, κ, hκ, e⟩
    exact hcon ⟨q, c, hc, κ, hκ, e⟩

end GlobalTheory.CompanionTheory.BZRes.TwoOrbit
