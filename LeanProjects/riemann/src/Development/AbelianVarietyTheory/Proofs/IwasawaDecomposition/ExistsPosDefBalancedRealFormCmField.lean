import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegelZeroFront

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.DefForm

variable {E : Type} [Field E] [NumberField E]

def coordForm (m : ℕ) : (Fin m → 𝓞 E) →ₗ[ℤ] (Fin m → 𝓞 E) →ₗ[ℤ] ℝ :=
  LinearMap.mk₂ ℤ (fun y z => ∑ k, ∑ τ : E →+* ℂ, (τ (y k : E) * conj (τ (z k : E))).re)
    (by intros; simp [add_mul, Finset.sum_add_distrib])
    (by intros; simp [Finset.mul_sum, mul_assoc])
    (by intros; simp [mul_add, Finset.sum_add_distrib])
    (by intro n y z; simp only [Finset.smul_sum, Pi.smul_apply]; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; rw [zsmul_eq_mul, zsmul_eq_mul]; simp [mul_left_comm])

theorem sum_sum_mul_re {ι : Type} [Fintype ι] (c : ι → ℝ) (u : ι → ℂ) :
    ∑ a, ∑ b, c a * c b * (u a * conj (u b)).re = Complex.normSq (∑ a, (c a : ℂ) * u a) := by
  rw [← Complex.ofReal_re (Complex.normSq _), ← Complex.mul_conj, map_sum, Finset.sum_mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_mul, Complex.conj_ofReal,
    show (c a : ℂ) * u a * ((c b : ℂ) * conj (u b)) = ((c a * c b : ℝ) : ℂ) * (u a * conj (u b)) by push_cast; ring,
    Complex.re_ofReal_mul]

theorem coordForm_mem [IsCMField E] (H : Host E) (m : ℕ) : coordForm (E := E) m ∈ realForms H.bar (Fin m → 𝓞 E) := by
  refine ⟨fun y z => ?_, fun a y z => ?_⟩
  · simp only [coordForm, LinearMap.mk₂_apply]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun τ _ => ?_
    rw [← Complex.conj_re, map_mul, Complex.conj_conj, mul_comm]
  · simp only [coordForm, LinearMap.mk₂_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun τ _ => ?_
    push_cast
    simp only [H.bar_eq, IsCMField.complexEmbedding_complexConj, map_mul, Complex.conj_conj]
    ring_nf

theorem coordForm_posDef (m : ℕ) : IsPosDef (coordForm (E := E) m) := by
  classical
  rw [isPosDef_iff_basis (Pi.basis fun _ : Fin m => RingOfIntegers.basis E)]
  intro c hc
  have hw : ∀ k (τ : E →+* ℂ), ∑ a, (c a : ℂ) * τ (((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a k : 𝓞 E) : E) =
      ∑ j, (c ⟨k, j⟩ : ℂ) * τ (RingOfIntegers.basis E j : E) := by
    intro k τ
    rw [Fintype.sum_sigma, Finset.sum_eq_single k]
    · exact Finset.sum_congr rfl fun j _ => by simp [Pi.basis_apply]
    · intro k' _ hk'
      exact Finset.sum_eq_zero fun j _ => by simp [Pi.basis_apply, Pi.single_apply, Ne.symm hk']
    · simp
  have hsum : ∑ a, ∑ a', c a * c a' * coordForm m ((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a)
      ((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a') =
      ∑ k, ∑ τ : E →+* ℂ, Complex.normSq (∑ j, (c ⟨k, j⟩ : ℂ) * τ (RingOfIntegers.basis E j : E)) := by
    simp_rw [← hw, ← sum_sum_mul_re]
    simp only [coordForm, LinearMap.mk₂_apply, Finset.mul_sum]
    calc _ = ∑ a, ∑ k, ∑ a', ∑ τ : E →+* ℂ, c a * c a' * (τ (((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a k : 𝓞 E) : E) *
            conj (τ (((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a' k : 𝓞 E) : E))).re :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ k, ∑ a, ∑ a', ∑ τ : E →+* ℂ, c a * c a' * (τ (((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a k : 𝓞 E) : E) *
            conj (τ (((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a' k : 𝓞 E) : E))).re := Finset.sum_comm
      _ = ∑ k, ∑ a, ∑ τ : E →+* ℂ, ∑ a', c a * c a' * (τ (((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a k : 𝓞 E) : E) *
            conj (τ (((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a' k : 𝓞 E) : E))).re :=
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun k _ => Finset.sum_comm
  rw [hsum]
  have hnn : ∀ k ∈ Finset.univ, 0 ≤ ∑ τ : E →+* ℂ, Complex.normSq (∑ j, (c ⟨k, j⟩ : ℂ) * τ (RingOfIntegers.basis E j : E)) :=
    fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  refine lt_of_le_of_ne (Finset.sum_nonneg hnn) fun h0 => hc ?_
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0.symm
  ext ⟨k, j⟩
  have h2 : ∀ τ : E →+* ℂ, ∑ j, (c ⟨k, j⟩ : ℂ) * τ (RingOfIntegers.basis E j : E) = 0 := fun τ =>
    Complex.normSq_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg fun _ _ => Complex.normSq_nonneg _).1
      (h1 k (Finset.mem_univ _)) τ (Finset.mem_univ _))
  have h3 : ∑ j, (c ⟨k, j⟩ : ℂ) • canonicalEmbedding.latticeBasis E j = 0 := by
    ext τ
    simpa [canonicalEmbedding.latticeBasis_apply, integralBasis_apply, canonicalEmbedding.apply_at] using h2 τ
  have := Fintype.linearIndependent_iff.1 (canonicalEmbedding.latticeBasis E).linearIndependent _ h3 j
  simpa using this

theorem exists_posDef_realForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X]
    [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
    ∃ B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ, B ∈ realForms H.bar X ∧ IsPosDef B := by
  intro E _ _ _ H X _ _ _ _
  obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' (𝓞 E) X
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  have hinj : Function.Injective s := Function.LeftInverse.injective (g := f) fun x => LinearMap.congr_fun hs x
  refine ⟨pullR s (coordForm m), ⟨fun y z => (coordForm_mem H m).1 _ _, fun a y z => ?_⟩, ?_⟩
  · simp only [pullR_apply, map_smul]
    exact (coordForm_mem H m).2 a _ _
  · intro n x hx c hc
    exact coordForm_posDef m n (s ∘ x) (hx.map' s.toAddMonoidHom.toIntLinearMap (LinearMap.ker_eq_bot.2 hinj)) c hc

end GlobalTheory.DefForm
