import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.LiftApplyOfMemAdmissibleSubalgebra
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TrivialEigenvalueCongruenceVanishesStatement

noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.H3.LamInj

theorem algebraMap_injective (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra ℤ_[l] E] [CharZero E] :
    Function.Injective (algebraMap ℤ_[l] E) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  have e := PadicInt.unitCoeff_spec h0
  rw [e, map_mul, map_pow, map_natCast] at hx
  have hl : (l : E) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  rcases mul_eq_zero.1 hx with h | h
  · exact ((PadicInt.unitCoeff h0).isUnit.map (algebraMap ℤ_[l] E)).ne_zero h
  · exact pow_ne_zero _ hl h

theorem gamma_le_of_dvd {N M : ℕ} (h : N ∣ M) : CongruenceSubgroup.Gamma M ≤ CongruenceSubgroup.Gamma N := by
  intro δ hδ
  rw [CongruenceSubgroup.Gamma_mem] at hδ ⊢
  obtain ⟨a, b, c, d⟩ := hδ
  have e : ∀ x : ℤ, ((x : ZMod M).cast : ZMod N) = (x : ZMod N) := fun x => ZMod.cast_intCast h x
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← e, a]; simp [ZMod.cast_one h]
  · rw [← e, b]; simp
  · rw [← e, c]; simp
  · rw [← e, d]; simp [ZMod.cast_one h]

theorem gamma_le_gam (N l : ℕ) : CongruenceSubgroup.Gamma (N * l) ≤ Gam N l := by
  intro δ hδ
  have h1 := CongruenceSubgroup.Gamma_mem.1 (gamma_le_of_dvd (Dvd.intro l rfl : N ∣ N * l) hδ)
  have h2 := CongruenceSubgroup.Gamma_mem.1 (gamma_le_of_dvd (Dvd.intro_left N rfl : l ∣ N * l) hδ)
  exact ⟨(CongruenceSubgroup.Gamma1_mem N δ).2 ⟨h1.1, h1.2.2.2, h1.2.2.1⟩, CongruenceSubgroup.Gamma0_mem.2 h2.2.2.1⟩

theorem fst_eq_zero_of_triv : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
    ∀ (N l w : ℕ) [Fact l.Prime], 1 ≤ N → ∀ {E : Type} [Field E] [Algebra ℤ_[l] E], CharZero E →
    ∀ (y : E ⊗[ℤ_[l]] X.Fn l) (G : ℂ → MvPolynomial (Fin 2) E), (y, G) ∈ H3.abelian₂ X l E → G ∈ Triv E w (Gam N l) →
    y = 0 := by
  intro Ω _ _ _ ε X _ _ N l w _ hN E _ _ hE y G hp hG
  exact GlobalTheory.T.trivial_eigenvalue_congruence_vanishes Ω ε X l E (algebraMap_injective l E) w (Gam N l) (N * l)
    (Nat.mul_pos hN (Fact.out : l.Prime).pos) (gamma_le_gam N l) (y, G) hp hG

end GlobalTheory.KZ.H3.LamInj
