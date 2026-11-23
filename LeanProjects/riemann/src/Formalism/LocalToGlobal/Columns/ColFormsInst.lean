import Mathlib
import Formalism.LocalToGlobal.Columns.ColFormsLemmas
import Formalism.LocalToGlobal.Columns.BaseInst

open NumberField IsDedekindDomain IntermediateField Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.Host Formalism.L2.DIV

section Gauss

variable (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : KQ 1 ≤ LL)

def gaussianPrimesSmall : Primes (gaussFields ι LL hE) where
  cond := 4
  g := ![29, 5]
  piG := ![gz ι LL hE 5 2, gz ι LL hE 2 1]
  Word := Unit
  T := fun _ => 14145788201
  piT := fun _ => gz ι LL hE 84101 84100

set_option maxRecDepth 1000000 in
theorem prime_fourteen_billion_example : Nat.Prime 14145788201 := by norm_num

theorem gaussianPrimesSmall_ok : (gaussianPrimesSmall ι LL hE).Ok := by
  have n0 := gz_norm ι LL hE 5 2 29 (by norm_num)
  have n1 := gz_norm ι LL hE 2 1 5 (by norm_num)
  have nT := gz_norm ι LL hE 84101 84100 14145788201 (by norm_num)
  have p0 : Nat.Prime 29 := by norm_num
  have p1 : Nat.Prime 5 := by norm_num
  have hr := gauss_rank ι LL hE
  have hf := gauss_f ι LL hE
  exact
    { g_prime := Fin.forall_fin_two.2 ⟨p0, p1⟩
      piG_Kq := fun _ => gauss_Kq ι LL hE _
      piG_norm := Fin.forall_fin_two.2 ⟨n0, n1⟩
      piG_cop := Fin.forall_fin_two.2 ⟨gz_cop ι LL hE 5 2 3 (-1) (by norm_num), gz_cop ι LL hE 2 1 (-1) 1 (by norm_num)⟩
      vG_card := Fin.forall_fin_two.2
        ⟨(card_divs_of_norm _ hr p0 (conj_norm _ n0)).trans hf.symm, (card_divs_of_norm _ hr p1 (conj_norm _ n1)).trans hf.symm⟩
      vG_norm := Fin.forall_fin_two.2
        ⟨norm_divs_of_norm _ hr p0 (conj_norm _ n0), norm_divs_of_norm _ hr p1 (conj_norm _ n1)⟩
      g_cong := Fin.forall_fin_two.2 ⟨(by decide : 29 ≡ 1 [MOD 4]), (by decide : 5 ≡ 1 [MOD 4])⟩
      g_ne := (by decide : (29 : ℕ) ≠ 5)
      T_prime := fun _ => prime_fourteen_billion_example
      piT_Kq := fun _ => gauss_Kq ι LL hE _
      piT_norm := fun _ => nT
      piT_cop := fun _ => gz_cop ι LL hE 84101 84100 (-84100) 1 (by norm_num)
      vT_card := fun _ => (card_divs_of_norm _ hr prime_fourteen_billion_example nT).trans hf.symm
      vT_norm := fun _ => norm_divs_of_norm _ hr prime_fourteen_billion_example nT
      piT_cong := fun _ => by
        have e : (gaussianPrimesSmall ι LL hE).cond * ((gaussianPrimesSmall ι LL hE).g 0 * (gaussianPrimesSmall ι LL hE).g 1) ^ 2 = 84100 := by
          show 4 * (29 * 5) ^ 2 = 84100
          norm_num
        rw [e]
        refine ⟨gz ι LL hE 1 1, ?_⟩
        show gz ι LL hE 84101 84100 - 1 = _
        unfold gz
        push_cast
        ring
      T_ne_g := fun _ => Fin.forall_fin_two.2 ⟨(by norm_num : (14145788201 : ℕ) ≠ 29), (by norm_num : (14145788201 : ℕ) ≠ 5)⟩ }

theorem gaussianSmallPrime_gt_twice_rank : 2 * (gaussFields ι LL hE).f * Examples₂.R0.k < (gaussianPrimesSmall ι LL hE).g 0 - 1 := by
  rw [gauss_f]
  show 2 * 1 * 8 < 29 - 1
  norm_num

end Gauss

end Formalism.L2.Col
