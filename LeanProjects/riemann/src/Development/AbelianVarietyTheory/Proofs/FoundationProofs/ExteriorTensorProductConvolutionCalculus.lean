import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial

open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem conv_tens {ι G : Type} [Fintype ι] [Group G] [Fintype G] (a b : ι → G → ℂ) :
    conv (tens a) (tens b) = tens fun v => conv (a v) (b v) := by
  funext x
  simp only [conv, tens]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.prod_mul_distrib]
  rfl

theorem conv_tens2 {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] (a a' : G → ℂ) (b b' : G' → ℂ) :
    conv (tens2 a b) (tens2 a' b') = tens2 (conv a a') (conv b b') := by
  funext x
  simp only [conv, tens2]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
  simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv]
  ring

theorem tens_calculus : ∀ (ι G G' : Type) [Fintype ι] [Group G] [Fintype G] [Group G'] [Fintype G'], (∀ a b : ι → G → ℂ, conv (tens a) (tens b) = tens fun v => conv (a v) (b v)) ∧ (∀ a : ι → G → ℂ, (∀ v, IsProj (a v)) → IsProj (tens a)) ∧ (∀ (a a' : G → ℂ) (b b' : G' → ℂ), conv (tens2 a b) (tens2 a' b') = tens2 (conv a a') (conv b b')) ∧ (∀ (a : G → ℂ) (b : G' → ℂ), IsProj a → IsProj b → IsProj (tens2 a b)) ∧ tens2 (dirac : G → ℂ) (dirac : G' → ℂ) = dirac ∧ ∀ (a a' : G → ℂ) (b b' : G' → ℂ), tens2 (a - a') b = tens2 a b - tens2 a' b ∧ tens2 a (b - b') = tens2 a b - tens2 a b' := by
  intro ι G G' _ _ _ _ _
  refine ⟨conv_tens, fun a h => ⟨?_, fun x => ?_⟩, conv_tens2, fun a b ha hb => ⟨?_, fun x => ?_⟩, ?_,
    fun a a' b b' => ⟨?_, ?_⟩⟩
  · rw [conv_tens]
    congr 1
    funext v
    exact (h v).1
  · simp only [tens, map_prod]
    exact Finset.prod_congr rfl fun v _ => (h v).2 (x v)
  · rw [conv_tens2, ha.1, hb.1]
  · simp only [tens2, map_mul, Prod.fst_inv, Prod.snd_inv, ha.2, hb.2]
  · funext ⟨x, y⟩
    simp only [tens2, dirac, Prod.mk_eq_one]
    by_cases hx : x = 1 <;> by_cases hy : y = 1 <;> simp [hx, hy]
  · funext x
    simp only [tens2, Pi.sub_apply, sub_mul]
  · funext x
    simp only [tens2, Pi.sub_apply, mul_sub]

end GlobalTheory.BadShare
