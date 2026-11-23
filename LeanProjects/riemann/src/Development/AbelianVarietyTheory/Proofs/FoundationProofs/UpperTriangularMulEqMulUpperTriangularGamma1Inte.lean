import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm
open GlobalTheory.HeckeFamilyMatrices

namespace GlobalTheory.Hk

theorem tinv_fin_fin : ∀ (N l q j : ℕ) (γ : SL(2, ℤ)), q.Prime → ¬ q ∣ N * l → j < q → γ ∈ GlobalTheory.Hk.lev N l →
    ¬ (q : ℤ) ∣ mat γ 0 0 + j * mat γ 1 0 → ∃ j' < q, ∃ γ' ∈ GlobalTheory.Hk.lev N l,
      !![(1 : ℤ), (j : ℤ); 0, (q : ℤ)] * mat γ = mat γ' * !![(1 : ℤ), (j' : ℤ); 0, (q : ℤ)] := by
  intro N l q j γ hq _ _ hγ hA
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨h1, h0⟩ := Subgroup.mem_inf.mp hγ
  rw [Gamma1_mem] at h1
  rw [Gamma0_mem] at h0
  obtain ⟨ha1, hd1, hc0⟩ := h1
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe
    rw [Matrix.det_fin_two] at this
    exact this
  set a := γ 0 0 with ha
  set b := γ 0 1 with hb
  set c := γ 1 0 with hc
  set d := γ 1 1 with hd
  have hmat : mat γ = !![a, b; c, d] := by
    ext i k; fin_cases i <;> fin_cases k <;> rfl
  rw [hmat] at hA ⊢
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const] at hA
  set A : ℤ := a + j * c with hAdef
  set B : ℤ := b + j * d with hBdef
  have hAq : ((A : ℤ) : ZMod q) ≠ 0 := by
    intro h
    exact hA ((ZMod.intCast_zmod_eq_zero_iff_dvd A q).mp h)
  set j' : ℕ := ((B : ZMod q) * (A : ZMod q)⁻¹).val with hj'
  have hj'lt : j' < q := ZMod.val_lt _
  have hdiv : (q : ℤ) ∣ B - j' * A := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hj', ZMod.natCast_zmod_val]
    field_simp
    ring
  obtain ⟨e, he⟩ := hdiv
  have hdet' : !![A, e; (q : ℤ) * c, d - c * j'].det = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination hdet + c * he
  let g : SL(2, ℤ) := ⟨!![A, e; (q : ℤ) * c, d - c * j'], hdet'⟩
  refine ⟨j', hj'lt, g, Subgroup.mem_inf.mpr ⟨(Gamma1_mem N g).mpr ⟨?_, ?_, ?_⟩, Gamma0_mem.mpr ?_⟩, ?_⟩
  · show ((a + j * c : ℤ) : ZMod N) = 1
    push_cast; rw [ha1, hc0]; ring
  · show ((d - c * j' : ℤ) : ZMod N) = 1
    push_cast; rw [hd1, hc0]; ring
  · show (((q : ℤ) * c : ℤ) : ZMod N) = 0
    push_cast; rw [hc0]; ring
  · show (((q : ℤ) * c : ℤ) : ZMod l) = 0
    push_cast; rw [h0]; ring
  · show _ = !![A, e; (q : ℤ) * c, d - c * j'] * _
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
    have e00 : 1 * a + (j : ℤ) * c = A * 1 + e * 0 := by rw [hAdef]; ring
    have e01 : 1 * b + (j : ℤ) * d = A * j' + e * q := by linear_combination he - hBdef
    have e10 : 0 * a + (q : ℤ) * c = (q : ℤ) * c * 1 + (d - c * j') * 0 := by ring
    have e11 : 0 * b + (q : ℤ) * d = (q : ℤ) * c * j' + (d - c * j') * q := by ring
    rw [e00, e01, e10, e11]

end GlobalTheory.Hk
