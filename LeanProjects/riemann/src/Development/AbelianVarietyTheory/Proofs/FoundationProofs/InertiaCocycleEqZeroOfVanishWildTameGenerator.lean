import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaTorsionQuotientConjInvariantDecomposition
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemCoc
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA GlobalTheory.InertCoh
open scoped Matrix

namespace GlobalTheory.CocWildTame

theorem eq_zero_on_Ine : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (B : ValuationSubring Ω) (γ : G ℚ Ω), Formalism.BasicNotions.TameGenAt B γ → ∀ z : G ℚ Ω → Fin 2 → Qbar l, (∀ i, Continuous fun s => z s i) → (∀ s ∈ Ine (F := ℚ) B, ∀ t ∈ Ine (F := ℚ) B, z (s * t) = z s + mat W s *ᵥ z t) → (∀ σ : G ℚ Ω, (∀ y : Ω, y ≠ 0 → B.valuation (σ y / y - 1) < 1) → z σ = 0) → z γ = 0 → ∀ s ∈ Ine (F := ℚ) B, z s = 0 := by
  intro l _ Ω _ _ W B γ hγ z hz hcoc hw hγ0 s hs
  have hwild : ∀ σ : G ℚ Ω, (∀ y : Ω, y ≠ 0 → B.valuation (σ y / y - 1) < 1) → σ ∈ Ine (F := ℚ) B :=
    fun σ hσ => GlobalTheory.TameConjInv.wild_mem_Ine B hσ
  have h1 : z 1 = 0 := hw 1 (fun y hy => by simp [div_self hy])
  have key : ∀ h ∈ Subgroup.closure (insert γ {σ : G ℚ Ω | ∀ y : Ω, y ≠ 0 → B.valuation (σ y / y - 1) < 1}),
      h ∈ Ine (F := ℚ) B ∧ z h = 0 := by
    intro h hh
    induction hh using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact ⟨hγ.1, hγ0⟩
      · exact ⟨hwild x hx, hw x hx⟩
    | one => exact ⟨one_mem _, h1⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨hx, hzx⟩ := ihx
      obtain ⟨hy, hzy⟩ := ihy
      exact ⟨mul_mem hx hy, by rw [hcoc x hx y hy, hzx, hzy, Matrix.mulVec_zero, add_zero]⟩
    | inv x _ ihx =>
      obtain ⟨hx, hzx⟩ := ihx
      refine ⟨inv_mem hx, ?_⟩
      have := hcoc x⁻¹ (inv_mem hx) x hx
      rw [inv_mul_cancel, h1, hzx, Matrix.mulVec_zero, add_zero] at this
      exact this.symm
  have hclosed : IsClosed {t : G ℚ Ω | z t = 0} := by
    have : {t : G ℚ Ω | z t = 0} = ⋂ i, (fun t => z t i) ⁻¹' {0} := by
      ext t; simp [funext_iff]
    rw [this]
    exact isClosed_iInter fun i => (isClosed_singleton).preimage (hz i)
  have hsub : ((Subgroup.closure (insert γ {σ : G ℚ Ω | ∀ y : Ω, y ≠ 0 → B.valuation (σ y / y - 1) < 1}) :
      Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) ⊆ {t : G ℚ Ω | z t = 0} := fun h hh => (key h hh).2
  exact (closure_minimal hsub hclosed) (hγ.2 hs)

end GlobalTheory.CocWildTame
