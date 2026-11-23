import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

namespace GlobalTheory

section RedGL

variable {E : Type} [Field E] [NumberField E]

theorem redGL_sum {ι : Type} (P : HeightOneSpectrum (𝓞 E)) (s : Finset ι) (f : ι → E)
    (hf : ∀ i ∈ s, IntAt P (f i)) :
    IntAt P (∑ i ∈ s, f i) ∧ redP P (∑ i ∈ s, f i) = ∑ i ∈ s, redP P (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 := IntAt.coe P 0
    have h1 := reduction_coe P 0
    simp only [map_zero] at h0 h1
    simpa using ⟨h0, h1⟩
  | insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have h3 := hf a (Finset.mem_insert_self a s)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ⟨h3.add h1, by rw [reduction_add h3 h1, h2]⟩

variable [StarRing E] {n : ℕ}

theorem redGL_single_mem (P : HeightOneSpectrum (𝓞 E)) (j : Fin n) :
    (Pi.single j 1 : Sp E n) ∈ stdAt E n P := by
  apply le_locP P
  simpa using single_mem_stdLat (E := E) j 1

theorem redGL_redV_single (P : HeightOneSpectrum (𝓞 E)) (j : Fin n) :
    redV P (Pi.single j 1 : Sp E n) = Pi.single j 1 := by
  funext i
  have h0 := reduction_coe P 0
  have h1 := reduction_coe P 1
  simp only [map_zero, map_one] at h0 h1
  by_cases h : i = j
  · subst h
    simp [redV, h1]
  · simp [redV, h, h0]

noncomputable def redGLMat (P : HeightOneSpectrum (𝓞 E)) (κ : Sp E n ≃ₗ[E] Sp E n) :
    Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal) :=
  Matrix.of fun i j => redP P (κ (Pi.single j 1) i)

theorem redGLMat_mulVec (P : HeightOneSpectrum (𝓞 E)) (κ : Sp E n ≃ₗ[E] Sp E n)
    (hκ : κ ∈ GLint E n P) (x : Sp E n) (hx : x ∈ stdAt E n P) :
    redV P (κ x) = (redGLMat P κ).mulVec (redV P x) := by
  have hxi : ∀ i, IntAt P (x i) := (mem_localization_standardLattice P x).1 hx
  have hc : ∀ j i, IntAt P (κ (Pi.single j 1) i) := fun j =>
    (mem_localization_standardLattice P _).1 ((hκ _).2 (redGL_single_mem P j))
  funext i
  have e : κ x i = ∑ j, κ (Pi.single j 1) i * x j := by
    have e1 : x = ∑ j, x j • (Pi.single j 1 : Sp E n) := by
      funext k
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [e1]
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
  change redP P (κ x i) = ∑ j, redP P (κ (Pi.single j 1) i) * redP P (x j)
  rw [e, (redGL_sum P _ _ fun j _ => (hc j i).mul (hxi j)).2]
  exact Finset.sum_congr rfl fun j _ => reduction_mul (hc j i) (hxi j)

theorem redGLMat_mul_inv (P : HeightOneSpectrum (𝓞 E)) (κ κ' : Sp E n ≃ₗ[E] Sp E n)
    (hκ : κ ∈ GLint E n P) (hκ' : κ' ∈ GLint E n P) (h : ∀ x, κ (κ' x) = x) :
    redGLMat P κ * redGLMat P κ' = 1 := by
  ext i j
  have h1 := redGLMat_mulVec P κ hκ (κ' (Pi.single j 1)) ((hκ' _).2 (redGL_single_mem P j))
  rw [h, redGL_redV_single] at h1
  have h2 := congrFun h1 i
  rw [Matrix.one_apply, ← Pi.single_apply j (1 : 𝓞 E ⧸ P.asIdeal) i, h2]
  rfl

end RedGL

theorem exists_GL_redV_of_mem_GLint (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ)
    (P : HeightOneSpectrum (𝓞 E)) (κ : Sp E n ≃ₗ[E] Sp E n) (hκ : κ ∈ GLint E n P) :
    ∃ h : GL (Fin n) (𝓞 E ⧸ P.asIdeal), ∀ x ∈ stdAt E n P, redV P (κ x) = h.1.mulVec (redV P x) := by
  have hκ' : κ⁻¹ ∈ GLint E n P := inv_mem hκ
  exact ⟨⟨redGLMat P κ, redGLMat P κ⁻¹,
    redGLMat_mul_inv P κ κ⁻¹ hκ hκ' fun x => LinearEquiv.apply_symm_apply κ x,
    redGLMat_mul_inv P κ⁻¹ κ hκ' hκ fun x => LinearEquiv.symm_apply_apply κ x⟩,
    fun x hx => redGLMat_mulVec P κ hκ x hx⟩

end GlobalTheory
