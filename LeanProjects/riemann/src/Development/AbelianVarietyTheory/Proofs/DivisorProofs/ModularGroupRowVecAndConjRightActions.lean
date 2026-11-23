import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.Act

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
theorem _root_.GlobalTheory.WpFam.Act.redGL_mul (N : ℕ) (γ δ : SL(2, ℤ)) :
    _root_.GlobalTheory.WpFam.redGL N (γ * δ) = _root_.GlobalTheory.WpFam.redGL N γ * _root_.GlobalTheory.WpFam.redGL N δ := by
  unfold _root_.GlobalTheory.WpFam.redGL
  simp [map_mul]

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
theorem _root_.GlobalTheory.WpFam.Act.redGL_one (N : ℕ) : _root_.GlobalTheory.WpFam.redGL N 1 = 1 := by
  unfold _root_.GlobalTheory.WpFam.redGL
  simp

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
theorem _root_.GlobalTheory.WpFam.Act.vmul_vmul {N : ℕ} (x : Fin 2 → ZMod N) (α β : GL (Fin 2) (ZMod N)) :
    _root_.GlobalTheory.WpFam.vmul (_root_.GlobalTheory.WpFam.vmul x α) β = _root_.GlobalTheory.WpFam.vmul x (α * β) := by
  unfold _root_.GlobalTheory.WpFam.vmul
  simp [Matrix.vecMul_vecMul]

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
theorem _root_.GlobalTheory.WpFam.Act.vmul_one {N : ℕ} (x : Fin 2 → ZMod N) : _root_.GlobalTheory.WpFam.vmul x 1 = x := by
  unfold _root_.GlobalTheory.WpFam.vmul
  simp

theorem zero_vmul {N : ℕ} (α : GL (Fin 2) (ZMod N)) : vmul (0 : Fin 2 → ZMod N) α = 0 := by
  simp only [vmul, Matrix.zero_vecMul]

theorem isRAct_gact (N : ℕ) (D : GL (Fin 2) (ZMod N)) : IsRAct (gact N D) := by
  constructor
  · intro x; simp [gact, redGL_one]
  · intro x γ δ; simp only [gact, redGL_mul]; group

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in

theorem _root_.GlobalTheory.WpFam.Act.rightActions : ∀ (N : ℕ), _root_.GlobalTheory.QFam.IsRAct (_root_.GlobalTheory.WpFam.vact N) ∧ (∀ D, _root_.GlobalTheory.QFam.IsRAct (_root_.GlobalTheory.WpFam.gact N D)) ∧ (∀ (x : Fin 2 → ZMod N) α β, _root_.GlobalTheory.WpFam.vmul (_root_.GlobalTheory.WpFam.vmul x α) β = _root_.GlobalTheory.WpFam.vmul x (α * β)) ∧ (∀ x : Fin 2 → ZMod N, _root_.GlobalTheory.WpFam.vmul x 1 = x) ∧ (∀ (x : Fin 2 → ZMod N) α, _root_.GlobalTheory.WpFam.vmul x α = 0 ↔ x = 0) ∧ (∀ (M : ℕ) (x : Fin 2 → ZMod N) α, _root_.GlobalTheory.WpFam.vmul (M • x) α = M • _root_.GlobalTheory.WpFam.vmul x α) ∧ (∀ (x : Fin 2 → ZMod N) (a : (ZMod N)ˣ), _root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a) = ![x 0, (a : ZMod N) * x 1]) ∧ (∀ γ δ, _root_.GlobalTheory.WpFam.redGL N (γ * δ) = _root_.GlobalTheory.WpFam.redGL N γ * _root_.GlobalTheory.WpFam.redGL N δ) ∧ _root_.GlobalTheory.WpFam.redGL N 1 = 1 := by
  intro N
  refine ⟨?_, ?_, _root_.GlobalTheory.WpFam.Act.vmul_vmul, _root_.GlobalTheory.WpFam.Act.vmul_one, ?_, ?_, ?_,
    _root_.GlobalTheory.WpFam.Act.redGL_mul N, _root_.GlobalTheory.WpFam.Act.redGL_one N⟩
  · refine ⟨fun x => ?_, fun x γ δ => ?_⟩
    · unfold _root_.GlobalTheory.WpFam.vact
      rw [_root_.GlobalTheory.WpFam.Act.redGL_one, _root_.GlobalTheory.WpFam.Act.vmul_one]
    · unfold _root_.GlobalTheory.WpFam.vact
      rw [_root_.GlobalTheory.WpFam.Act.vmul_vmul, _root_.GlobalTheory.WpFam.Act.redGL_mul]
  · intro D
    refine ⟨fun α => ?_, fun α γ δ => ?_⟩
    · unfold _root_.GlobalTheory.WpFam.gact
      rw [_root_.GlobalTheory.WpFam.Act.redGL_one]
      group
    · unfold _root_.GlobalTheory.WpFam.gact
      rw [_root_.GlobalTheory.WpFam.Act.redGL_mul]
      group
  · intro x α
    constructor
    · intro h
      have key := congrArg (fun y => _root_.GlobalTheory.WpFam.vmul y α⁻¹) h
      simp only [_root_.GlobalTheory.WpFam.Act.vmul_vmul, mul_inv_cancel, _root_.GlobalTheory.WpFam.Act.vmul_one] at key
      rw [key]
      unfold _root_.GlobalTheory.WpFam.vmul
      simp
    · rintro rfl
      unfold _root_.GlobalTheory.WpFam.vmul
      simp
  · intro M x α
    unfold _root_.GlobalTheory.WpFam.vmul
    rw [Matrix.smul_vecMul]
  · intro x a
    unfold _root_.GlobalTheory.WpFam.vmul _root_.GlobalTheory.WpFam.dg
    ext i
    fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_comm]

end GlobalTheory.WpFam.Act
