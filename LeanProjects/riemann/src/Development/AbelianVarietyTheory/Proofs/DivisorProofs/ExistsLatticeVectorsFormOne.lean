import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncMatTranspose
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.FormOne

theorem form_smul_left {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (c : E) (x y : Fin n → E) :
    form σ J (c • x) y = c * form σ J x y := by
  simp [form, smul_dotProduct]

theorem exists_sum_form_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ), X.IsHerm σ B r s → 0 < n →
    ∃ (m : ℕ) (x y : Fin m → Fin n → E), (∀ i, x i ∈ X.L ∧ y i ∈ X.L) ∧ ∑ i, form σ X.J (x i) (y i) = 1 := by
  intro F E _ _ _ _ _ σ B n X r s hX hn
  have key : (1 : E) ∈ Submodule.span (𝓞 E) {z : E | ∃ x ∈ X.L, ∃ y ∈ X.L, form σ X.J x y = z} := by
    by_contra h1
    have hI : (Submodule.span (𝓞 E) {z : E | ∃ x ∈ X.L, ∃ y ∈ X.L, form σ X.J x y = z}).comap
        (Algebra.linearMap (𝓞 E) E) ≠ ⊤ := by
      intro h; apply h1
      have : (1 : 𝓞 E) ∈ (Submodule.span (𝓞 E) {z : E | ∃ x ∈ X.L, ∃ y ∈ X.L, form σ X.J x y = z}).comap
          (Algebra.linearMap (𝓞 E) E) := h ▸ Submodule.mem_top
      simpa using this
    obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal _ hI
    have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)
    obtain ⟨γ, hγ, hγ1⟩ := FractionalIdeal.exists_notMem_one_of_ne_bot (K := E) hP0 hP.ne_top
    have hγL : ∀ y ∈ X.L, γ • y ∈ X.L := by
      intro y hy
      rw [hX.dual]
      intro x hx
      rw [form_smul_left]
      obtain ⟨a, ha⟩ : ∃ a : 𝓞 E, algebraMap (𝓞 E) E a = form σ X.J y x :=
        ⟨⟨_, (hX.dual y).1 hy x hx⟩, rfl⟩
      have haP : a ∈ P := hIP (Submodule.mem_comap.2 (Submodule.subset_span ⟨y, hy, x, hx, ha.symm⟩))
      have hm := FractionalIdeal.mul_mem_mul hγ ((FractionalIdeal.mem_coeIdeal _).2 ⟨a, haP, rfl⟩)
      rw [inv_mul_cancel₀ (FractionalIdeal.coeIdeal_ne_zero.2 hP0)] at hm
      obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).1 hm
      rw [← ha, ← hb]
      exact RingOfIntegers.isIntegral_coe b
    have hL0 : X.L ≠ ⊥ := by
      intro h
      have h1 := hX.lat.span_eq_top
      rw [h] at h1
      have h2 : (Pi.single (⟨0, hn⟩ : Fin n) (1 : E) : Fin n → E) ∈
          Submodule.span E ((⊥ : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
        rw [h1]; trivial
      simp at h2
    have hint := isIntegral_of_smul_mem_submodule X.L hL0 hX.lat.fg γ hγL
    exact hγ1 ((FractionalIdeal.mem_one_iff _).2 (IsIntegrallyClosed.isIntegral_iff.1 hint))
  obtain ⟨m, f, g, hfg⟩ := Submodule.mem_span_set'.1 key
  have hg := fun i => (g i).2
  simp only [Set.mem_setOf_eq] at hg
  choose x hx y hy hxy using hg
  refine ⟨m, fun i => (algebraMap (𝓞 E) E (f i)) • x i, y,
    fun i => ⟨by show (algebraMap (𝓞 E) E (f i)) • x i ∈ X.L; rw [algebraMap_smul]; exact X.L.smul_mem _ (hx i), hy i⟩, ?_⟩
  rw [← hfg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [form_smul_left, hxy i, Algebra.smul_def]

end GlobalTheory.FormOne
