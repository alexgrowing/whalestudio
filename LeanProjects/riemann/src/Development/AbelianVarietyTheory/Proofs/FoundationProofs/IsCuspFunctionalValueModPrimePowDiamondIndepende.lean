import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlMulToRingEquiv
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

noncomputable section

namespace GlobalTheory.KZ

theorem mul_inv_mem_Gam_of_isDiam {N l d : ℕ} {s t : SL(2, ℤ)} (hs : IsDiam N l d s) (ht : IsDiam N l d t) :
    s * t⁻¹ ∈ Gam N l := by
  obtain ⟨hs0, hsd⟩ := hs
  obtain ⟨ht0, htd⟩ := ht
  rw [Subgroup.mem_inf] at hs0 ht0
  refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mul_mem _ hs0.2 (Subgroup.inv_mem _ ht0.2)⟩
  have hsN := CongruenceSubgroup.Gamma0_mem.1 hs0.1
  have htN := CongruenceSubgroup.Gamma0_mem.1 ht0.1
  have ds := s.det_coe
  have dt := t.det_coe
  rw [Matrix.det_fin_two] at ds dt
  have ds' : ((s 0 0 * s 1 1 - s 0 1 * s 1 0 : ℤ) : ZMod N) = 1 := by rw [ds]; simp
  have dt' : ((t 0 0 * t 1 1 - t 0 1 * t 1 0 : ℤ) : ZMod N) = 1 := by rw [dt]; simp
  push_cast at ds' dt'
  simp only [en] at hsd htd
  rw [CongruenceSubgroup.Gamma1_mem]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
  push_cast
  refine ⟨?_, ?_, ?_⟩
  · linear_combination ds' + (s 0 0 : ZMod N) * (htd - hsd) + (s 0 1 : ZMod N) * hsN - (s 0 1 : ZMod N) * htN
  · linear_combination dt' + (t 0 0 : ZMod N) * (hsd - htd) + (t 0 1 : ZMod N) * htN - (t 0 1 : ZMod N) * hsN
  · linear_combination (t 1 1 : ZMod N) * hsN - (s 1 1 : ZMod N) * htN

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem Tower.act_eq_of_mem_B (X : Tower Ω ε) {N l w : ℕ} [Fact l.Prime] {b : X.Fn l} (hb : b ∈ X.B N l w)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gam N l) : X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = b := by
  induction hb using Submodule.span_induction with
  | mem x hx => exact hx.2 γ hγ
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul c x _ hx => rw [map_smul, hx]

theorem Tower.act_isDiam_eq (X : Tower Ω ε) {N l w d : ℕ} [Fact l.Prime] {b : X.Fn l} (hb : b ∈ X.B N l w)
    {s : SL(2, ℤ)} (hs : IsDiam N l d s) :
    X.act l (s : Matrix (Fin 2) (Fin 2) ℤ) b = X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b := by
  have ht : IsDiam N l d (sgD N l d) := Classical.epsilon_spec ⟨s, hs⟩
  have hγ := mul_inv_mem_Gam_of_isDiam hs ht
  have e : s = (s * (sgD N l d)⁻¹) * sgD N l d := by group
  have hpos : ∀ g : SL(2, ℤ), 0 < (g : Matrix (Fin 2) (Fin 2) ℤ).det := fun g => by rw [g.det_coe]; exact one_pos
  rw [e, Matrix.SpecialLinearGroup.coe_mul, ← Tower.act_act Ω ε X l _ _ (hpos _) (hpos _) b,
    X.act_eq_of_mem_B hb hγ]

theorem isThB_act_isDiam_iff : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n w d : ℕ) (b : X.Fn l), b ∈ X.B N l w →
    ∀ s : SL(2, ℤ), IsDiam N l d s → ∀ φ : HahnSeries ℚ Ω,
  IsThB X A N l n (X.act l (s : Matrix (Fin 2) (Fin 2) ℤ) b) φ ↔
    IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) φ := by
  intro Ω _ _ _ ε X A N l _ n w d b hb s hs φ
  rw [X.act_isDiam_eq hb hs]

end GlobalTheory.KZ
