import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

noncomputable section

namespace GlobalTheory.OddFrame

def frameMap (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] {r : ℕ} (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ) (k : ℤ)
    (hF : ∀ j, IsMF Γ (w j) (F j)) :
    (Π j : Fin r, ModularForm 𝒮ℒ (k - w j)) →ₗ[ℂ] ModularForm Γ k where
  toFun g := (IsMF.sum (f := fun j => ⇑(g j) * F j) Finset.univ
    (fun j _ => ((isMF_coe_top (g j)).mono le_top).mul (hF j) (by ring))).toMF
  map_add' g h := by
    ext τ
    simp [add_mul, Finset.sum_add_distrib, Finset.sum_apply]
  map_smul' c g := by
    ext τ
    simp [Finset.mul_sum, mul_assoc, Finset.sum_apply]

theorem frameMap_apply (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] {r : ℕ} (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ)
    (k : ℤ) (hF : ∀ j, IsMF Γ (w j) (F j)) (g : Π j : Fin r, ModularForm 𝒮ℒ (k - w j)) :
    ⇑(frameMap Γ w F k hF g) = ∑ j, ⇑(g j) * F j := rfl

theorem mul_slash_levelOne {r : ℕ} (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ) (k : ℤ)
    (g : Π j : Fin r, ModularForm 𝒮ℒ (k - w j)) (j : Fin r) (x : SL(2, ℤ)) :
    (⇑(g j) * F j) ∣[k] x = ⇑(g j) * (F j ∣[w j] x) := by
  have h := ModularForm.mul_slash_SL2 (k - w j) (w j) x (⇑(g j)) (F j)
  rw [sub_add_cancel] at h
  rw [h, IsMF.slash_top (isMF_coe_top (g j)) x]

theorem frameMap_injective (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] {r : ℕ} (s : Fin r → SL(2, ℤ))
    (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ) (k : ℤ) (hF : ∀ j, IsMF Γ (w j) (F j))
    (hdet : ∀ τ, (evM s w F τ).det ≠ 0) : Function.Injective (frameMap Γ w F k hF) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro g hg
  have hsum : ∑ j, ⇑(g j) * F j = 0 := by
    rw [← frameMap_apply Γ w F k hF g, hg]
    rfl
  have hrow : ∀ i τ, ∑ j, (g j) τ * (F j ∣[w j] s i) τ = 0 := by
    intro i τ
    have h1 : (∑ j, ⇑(g j) * F j) ∣[k] s i = 0 := by
      rw [hsum]
      exact SlashAction.zero_slash _ _
    rw [SlashAction.sum_slash] at h1
    simp only [mul_slash_levelOne w F k g _ (s i)] at h1
    have h2 := congrFun h1 τ
    simpa [Finset.sum_apply] using h2
  have hv : ∀ τ, (fun j => (g j) τ) = 0 := by
    intro τ
    apply Matrix.eq_zero_of_mulVec_eq_zero (hdet τ)
    funext i
    simp only [Matrix.mulVec, dotProduct, evM, Matrix.of_apply, Pi.zero_apply]
    rw [← hrow i τ]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  funext j
  ext τ
  exact congrFun (hv τ) j

theorem finrank_sum_le_of_frame : ∀ (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ)
    (F : Fin r → ℍ → ℂ) (k : ℤ), Γ.FiniteIndex → FiniteDimensional ℂ (ModularForm Γ k) →
    (∀ j, IsMF Γ (w j) (F j)) → (∀ τ, (evM s w F τ).det ≠ 0) →
    ∑ j, Module.finrank ℂ (ModularForm 𝒮ℒ (k - w j)) ≤ Module.finrank ℂ (ModularForm Γ k) := by
  intro Γ r s w F k hΓ hfin hF hdet
  have hinj := frameMap_injective Γ s w F k hF hdet
  have : Module.Finite ℂ (Π j : Fin r, ModularForm 𝒮ℒ (k - w j)) :=
    Module.Finite.of_injective (frameMap Γ w F k hF) hinj
  have : ∀ j, Module.Finite ℂ (ModularForm 𝒮ℒ (k - w j)) := fun j =>
    Module.Finite.of_surjective (LinearMap.proj (R := ℂ)
      (φ := fun j : Fin r => ModularForm 𝒮ℒ (k - w j)) j)
      (fun y => ⟨Pi.single j y, by simp⟩)
  rw [← Module.finrank_pi_fintype]
  exact LinearMap.finrank_le_finrank_of_injective hinj

end GlobalTheory.OddFrame
