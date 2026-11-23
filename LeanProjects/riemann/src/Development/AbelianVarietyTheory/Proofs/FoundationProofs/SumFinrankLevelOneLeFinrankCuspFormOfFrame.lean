import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

noncomputable section
namespace GlobalTheory.OddFrame

theorem levelOne_mul_slash {k w : ℤ} (g : ModularForm 𝒮ℒ (k - w)) (F : ℍ → ℂ) (x : SL(2, ℤ)) :
    ((⇑g) * F) ∣[k] x = (⇑g) * (F ∣[w] x) := by
  have h := ModularForm.mul_slash_SL2 (k - w) w x (⇑g) F
  rw [sub_add_cancel] at h
  rw [h, (isMF_coe_top g).slash_top x]

theorem sum_finrank_le_finrank_cuspForm (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ)
    (F : Fin r → ℍ → ℂ) (k : ℤ) (hΓ : Γ.FiniteIndex) (hfin : FiniteDimensional ℂ (CuspForm Γ k))
    (hF : ∀ j, IsCF Γ (w j) (F j)) (hdet : ∀ τ, (evM s w F τ).det ≠ 0) :
    ∑ j, Module.finrank ℂ (ModularForm 𝒮ℒ (k - w j)) ≤ Module.finrank ℂ (CuspForm Γ k) := by
  have hcf : ∀ (j : Fin r) (g : ModularForm 𝒮ℒ (k - w j)), IsCF Γ k ((⇑g) * F j) := fun j g =>
    ((isMF_coe_top g).mono le_top).mul_isCF (hF j) (by ring)
  have happ : ∀ (c : Fin r → CuspForm Γ k) (τ : ℍ), (∑ j, c j) τ = ∑ j, c j τ := by
    intro c τ
    induction (Finset.univ : Finset (Fin r)) using Finset.induction_on with
    | empty => simp
    | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, CuspForm.add_apply, ih]
  let L : (Π j, ModularForm 𝒮ℒ (k - w j)) →ₗ[ℂ] CuspForm Γ k :=
    { toFun := fun g => ∑ j, (hcf j (g j)).toCF
      map_add' := by
        intro a b; ext τ
        simp only [CuspForm.add_apply, happ, IsCF.coe_toCF, Pi.mul_apply, Pi.add_apply, ModularForm.add_apply,
          add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c a; ext τ
        simp only [CuspForm.smul_apply, happ, IsCF.coe_toCF, Pi.mul_apply, Pi.smul_apply, ModularForm.smul_apply,
          RingHom.id_apply, smul_eq_mul, Finset.mul_sum, mul_assoc] }
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro g hg
    have h0 : ∀ τ, ∑ j, g j τ * F j τ = 0 := by
      intro τ
      have := congrArg (fun f : CuspForm Γ k => f τ) hg
      simpa [L, happ] using this
    have hfun : (∑ j, (⇑(g j)) * F j) = 0 := by
      ext τ; simpa [Finset.sum_apply] using h0 τ
    have hvec : ∀ τ, Matrix.mulVec (evM s w F τ) (fun j => g j τ) = 0 := by
      intro τ; ext i
      have h1 := congrArg (fun f => (f ∣[k] s i) τ) hfun
      simp only [SlashAction.zero_slash, Pi.zero_apply] at h1
      rw [SlashAction.sum_slash] at h1
      simp only [levelOne_mul_slash, Finset.sum_apply, Pi.mul_apply] at h1
      simp only [Matrix.mulVec, dotProduct, evM, Matrix.of_apply, Pi.zero_apply]
      rw [← h1]; exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    funext j; ext τ
    have := Matrix.eq_zero_of_mulVec_eq_zero (hdet τ) (hvec τ)
    exact congrFun this j
  haveI : FiniteDimensional ℂ (Π j, ModularForm 𝒮ℒ (k - w j)) := inferInstance
  calc ∑ j, Module.finrank ℂ (ModularForm 𝒮ℒ (k - w j))
      = Module.finrank ℂ (Π j, ModularForm 𝒮ℒ (k - w j)) := (Module.finrank_pi_fintype ℂ).symm
    _ ≤ Module.finrank ℂ (CuspForm Γ k) := LinearMap.finrank_le_finrank_of_injective hinj

end GlobalTheory.OddFrame
