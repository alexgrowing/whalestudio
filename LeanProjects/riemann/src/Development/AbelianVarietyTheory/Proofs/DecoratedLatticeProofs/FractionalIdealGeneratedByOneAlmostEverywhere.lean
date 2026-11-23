import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
open Formalism.BasicNotions IsDedekindDomain NumberField

namespace GlobalTheory.IdeleGen

theorem exists_nat_mem_mul_integral {E : Type} [Field E] [NumberField E]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hI : I ≠ 0) :
    ∃ N : ℕ, N ≠ 0 ∧ (N : E) ∈ I ∧ ∀ b ∈ I, ∃ o : 𝓞 E, (N : E) * b = (o : E) := by
  obtain ⟨a, ha, hint⟩ := I.isFractional
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hbot : (I : Submodule (𝓞 E) E) ≠ ⊥ := by
    intro h
    apply hI
    exact FractionalIdeal.coeToSubmodule_injective (h.trans FractionalIdeal.coe_zero.symm)
  obtain ⟨x, hxI, hx0⟩ := (Submodule.ne_bot_iff _).1 hbot
  obtain ⟨j, hj⟩ := hint x hxI
  have hj' : (j : E) = (a : E) * x := by
    simpa [Algebra.smul_def] using hj
  have haE : (a : E) ≠ 0 := by exact_mod_cast ha0
  have hj0 : j ≠ 0 := by
    intro h; rw [h] at hj'; simp at hj'
    rcases hj' with h1 | h1
    · first | exact ha0 h1 | exact ha0 h1.symm | exact haE h1 | exact haE h1.symm
    · first | exact hx0 h1 | exact hx0 h1.symm
  set Nd := Ideal.absNorm (Ideal.span {a}) with hNd
  set Nj := Ideal.absNorm (Ideal.span {j}) with hNj
  have hNd0 : Nd ≠ 0 := by
    rw [hNd, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact ha0
  have hNj0 : Nj ≠ 0 := by
    rw [hNj, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hj0
  obtain ⟨o₁, ho₁⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))
  obtain ⟨o₂, ho₂⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {j}))
  have ho₁E : ((Nd : 𝓞 E) : E) = (o₁ : E) * (a : E) := by rw [← ho₁]; push_cast; ring
  have ho₂E : ((Nj : 𝓞 E) : E) = (o₂ : E) * (j : E) := by rw [← ho₂]; push_cast; ring
  refine ⟨Nd * Nj, mul_ne_zero hNd0 hNj0, ?_, ?_⟩
  · have : ((Nd * Nj : ℕ) : E) = ((Nd : 𝓞 E) * o₂ * a : 𝓞 E) • x := by
      rw [Algebra.smul_def]
      have e1 : ((Nd * Nj : ℕ) : E) = ((Nd : 𝓞 E) : E) * ((Nj : 𝓞 E) : E) := by push_cast; ring
      rw [e1, ho₂E]
      have hal : ∀ z : 𝓞 E, algebraMap (𝓞 E) E z = (z : E) := fun _ => rfl
      rw [hal]
      push_cast
      linear_combination ((Nd : E) * (o₂ : E)) * hj'
    rw [this]
    exact Submodule.smul_mem _ _ hxI
  · intro b hb
    obtain ⟨y, hy⟩ := hint b hb
    have hy' : (y : E) = (a : E) * b := by simpa [Algebra.smul_def] using hy
    refine ⟨(Nj : 𝓞 E) * o₁ * y, ?_⟩
    have e1 : ((Nd * Nj : ℕ) : E) = ((Nd : 𝓞 E) : E) * ((Nj : 𝓞 E) : E) := by push_cast; ring
    rw [e1, ho₁E]
    push_cast
    linear_combination (-((Nj : E) * (o₁ : E))) * hy'

theorem aeGen : ∀ (D : D7) (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E), I ≠ 0 →
    ∃ S : Finset (HeightOneSpectrum (𝓞 D.host.F)), ∀ v ∉ S, ∃ c : 𝓞 D.host.F, c ∉ v.asIdeal ∧
      ((c : D.host.F) : D.host.E) ∈ I ∧ ∀ b ∈ I, ∃ o : 𝓞 D.host.E, ((c : D.host.F) : D.host.E) * b = (o : D.host.E) := by
  intro D I hI
  obtain ⟨N, hN0, hNI, hNb⟩ := exists_nat_mem_mul_integral I hI
  have hc0 : Ideal.span {(N : 𝓞 D.host.F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN0
  have hfin := Ideal.finite_factors hc0
  refine ⟨hfin.toFinset, fun v hv => ⟨(N : 𝓞 D.host.F), ?_, ?_, ?_⟩⟩
  · intro hmem
    apply hv
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hmem
  · have : (((N : 𝓞 D.host.F) : D.host.F) : D.host.E) = (N : D.host.E) := by push_cast; rfl
    rw [this]; exact hNI
  · have : (((N : 𝓞 D.host.F) : D.host.F) : D.host.E) = (N : D.host.E) := by push_cast; rfl
    rw [this]; exact hNb

end GlobalTheory.IdeleGen
