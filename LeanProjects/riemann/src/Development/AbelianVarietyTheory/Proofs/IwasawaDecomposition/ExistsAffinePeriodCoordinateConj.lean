import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Formalism.LocalToGlobal.ProjectiveLattices.FibreUniformisationLevelTwo
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem frame_col_top_letter : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (τ₁ : E →+* ℂ), τ₁ ∉ X.Ψ → ∀ (i : ℕ), X.p0 = i + 1 → ∃ κ : Frame X.Ψ r → Fin r → ℂ, ContinuousOn κ X.dom ∧
      (∀ O : Set (Frame X.Ψ r), IsOpen O → O ⊆ X.dom → ∀ x ∈ O, ∀ ξ : Fin r → ℂ,
        ∀ᶠ t in nhdsWithin (0 : ℂ) {0}ᶜ, ∃ x' ∈ O, κ x' = κ x + t • ξ) ∧
      ∀ x ∈ X.dom, ∀ v, Formalism.L2.PjFree.perFr X x v τ₁ i = κ x ⬝ᵥ Data.emb τ₁ v := by
  intro E _ _ _ r X τ₁ h1 i hp
  classical
  have hc : conjEmb τ₁ = ComplexEmbedding.conjugate τ₁ := by
    ext z; simp [conjEmb, ComplexEmbedding.conjugate_coe_eq]
  have hτ : conjEmb τ₁ ∈ X.Ψ := by
    rw [hc, X.cmType]
    have hcc : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ₁) = τ₁ := by
      ext z; simp [ComplexEmbedding.conjugate_coe_eq]
    rw [hcc]; exact h1
  have hr : 0 < r := by have := X.p0_le; omega
  let τ' : X.Ψ := ⟨conjEmb τ₁, hτ⟩
  let c₀ : Fin r := ⟨0, hr⟩
  let κ : Frame X.Ψ r → Fin r → ℂ := fun x b => ∑ a, x τ' a c₀ * conjEmb τ₁ (X.Gm a b)
  have hcont : Continuous κ := by
    refine continuous_pi fun b => continuous_finset_sum _ fun a _ => ?_
    have h3 : Continuous fun x : Frame X.Ψ r => x τ' a c₀ := by fun_prop
    exact h3.mul continuous_const
  refine ⟨κ, hcont.continuousOn, ?_, ?_⟩
  · intro O hO hOd x hx ξ
    let Gτ : Matrix (Fin r) (Fin r) ℂ := X.Gm.map (conjEmb τ₁)
    have hdet : IsUnit Gτ.det := by
      rw [isUnit_iff_ne_zero]
      show (X.Gm.map (conjEmb τ₁)).det ≠ 0
      rw [show X.Gm.map (conjEmb τ₁) = (conjEmb τ₁).mapMatrix X.Gm from rfl, ← RingHom.map_det]
      exact (map_ne_zero _).2 X.Gm_det
    let η : Fin r → ℂ := ξ ᵥ* Gτ⁻¹
    have hη : ∀ b, ∑ a, η a * conjEmb τ₁ (X.Gm a b) = ξ b := by
      intro b
      have h2 : η ᵥ* Gτ = ξ := by
        simp only [η, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, Matrix.vecMul_one]
      rw [← h2]; rfl
    let d : Frame X.Ψ r := fun σ a c => if σ = τ' ∧ c = c₀ then η a else 0
    have hκ : ∀ t : ℂ, κ (x + t • d) = κ x + t • ξ := by
      intro t; funext b
      simp only [κ, d, Pi.add_apply, Pi.smul_apply, smul_eq_mul, and_self, if_true, add_mul,
        Finset.sum_add_distrib]
      rw [← hη b, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    have hcl : Continuous fun t : ℂ => x + t • d := continuous_const.add (continuous_id.smul continuous_const)
    have hev : ∀ᶠ t in nhds (0 : ℂ), x + t • d ∈ O :=
      hcl.continuousAt.preimage_mem_nhds (by simpa using hO.mem_nhds hx)
    exact (hev.filter_mono nhdsWithin_le_nhds).mono fun t ht => ⟨_, ht, hκ t⟩
  · intro x _ v
    unfold Formalism.L2.PjFree.perFr
    rw [dif_neg h1, dif_pos hτ, dif_pos (by omega : X.p0 - 1 - i < r)]
    have hcol : (⟨X.p0 - 1 - i, by omega⟩ : Fin r) = c₀ := Fin.ext (by simp [c₀]; omega)
    have hcj : ∀ z : E, (starRingEnd ℂ) (conjEmb τ₁ z) = τ₁ z := by
      intro z; simp [conjEmb]
    simp only [hermC, dotProduct, Data.emb, ReciprocityTheory.ChartRestriction.G.FD.col, mat, Matrix.of_apply, κ, hcol, hcj, Finset.sum_mul]
    rw [Finset.sum_comm]

end GlobalTheory
