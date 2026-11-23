import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Chapter
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory

theorem zs_iter_Uo {R : Type*} [CommRing R] (l r : ℕ) (a : ℕ → R) (n : ℕ) :
    (GlobalTheory.EisM.Uo l)^[r] a n = a (l ^ r * n) := by
  induction r generalizing n with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', GlobalTheory.EisM.Uo, ih]
    congr 1; ring

theorem zs_norm_char_le_one {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) {N : ℕ} (hN : 0 < N)
    (θ : DirichletCharacter ℂ N) (z : ZMod N) : ‖ι.symm (θ z)‖ ≤ 1 := by
  haveI : NeZero N := ⟨hN.ne'⟩
  by_cases hz : IsUnit z
  · obtain ⟨u, rfl⟩ := hz
    have h1 : (θ (u : ZMod N)) ^ Fintype.card (ZMod N)ˣ = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
    have h2 : ‖ι.symm (θ (u : ZMod N))‖ ^ Fintype.card (ZMod N)ˣ = 1 := by
      rw [← norm_pow, ← map_pow, h1, map_one, norm_one]
    exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) Fintype.card_ne_zero).1 h2).le
  · rw [MulChar.map_nonunit θ hz, map_zero, norm_zero]; exact zero_le_one

theorem zs_norm_exp {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) {N : ℕ} (hN : 0 < N) (y : ℕ) (d : ℤ) :
    ‖ι.symm (cexp (2 * π * Complex.I * (y * d) / N))‖ = 1 := by
  have h1 : (cexp (2 * π * Complex.I * (y * d) / N)) ^ N = 1 := by
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨(y : ℤ) * d, ?_⟩
    have : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    push_cast
    field_simp
  have h2 : ‖ι.symm (cexp (2 * π * Complex.I * (y * d) / N))‖ ^ N = 1 := by
    rw [← norm_pow, ← map_pow, h1, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN.ne').1 h2

theorem zs_norm_hat_le_one {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) {N : ℕ} (hN : 0 < N)
    (θ : DirichletCharacter ℂ N) (d : ℤ) : ‖ι.symm (GlobalTheory.EisM.hat (fun z => θ z) d)‖ ≤ 1 := by
  unfold GlobalTheory.EisM.hat
  rw [map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun y _ => ?_
  rw [map_mul, norm_mul, zs_norm_exp ι hN, mul_one]
  exact zs_norm_char_le_one ι hN θ _

end GlobalTheory

namespace GlobalTheory

end GlobalTheory

end
