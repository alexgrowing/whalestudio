import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import Development.AbelianVarietyTheory.Definitions.Foundations.OpLDOneSubMemTriv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlMulToRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFunctionalValueModPrimePowDiamondIndependeStatement
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

noncomputable section

namespace GlobalTheory.KZ

theorem isDiam_sgD_of_coprime {N l d : ℕ} (hl : l ≠ 0) (hd : Nat.Coprime d N) : IsDiam N l d (sgD N l d) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h1 : d = 1 := Nat.coprime_zero_right d |>.1 hd
    subst h1
    refine Classical.epsilon_spec (p := IsDiam 0 l 1) ⟨1, ⟨?_, ?_⟩, ?_⟩
    · exact Subgroup.one_mem _
    · exact Subgroup.one_mem _
    · simp [en]
  · exact Betti.isDiam_sgD hN.ne' hl hd

theorem isDiam_mul {N l a d : ℕ} {s t : SL(2, ℤ)} (hs : IsDiam N l a s) (ht : IsDiam N l d t) :
    IsDiam N l (d * a) (s * t) := by
  obtain ⟨hs0, hsd⟩ := hs
  obtain ⟨ht0, htd⟩ := ht
  refine ⟨Subgroup.mul_mem _ hs0 ht0, ?_⟩
  have hsN := CongruenceSubgroup.Gamma0_mem.1 (Subgroup.mem_inf.1 hs0).1
  simp only [en] at hsd htd ⊢
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  rw [hsN, hsd, htd]
  ring

end GlobalTheory.KZ

theorem GlobalTheory.KZ.isThB_act_sgD_diam_iff : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ)
    (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n w a d : ℕ), a.Coprime N → d.Coprime N →
    ∀ b : X.Fn l, b ∈ X.B N l w → ∀ φ : HahnSeries ℚ Ω,
  IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.diam N l a b)) φ ↔
    IsThB X A N l n (X.act l (sgD N l (d * a) : Matrix (Fin 2) (Fin 2) ℤ) b) φ := by
  intro Ω _ _ _ ε X A N l hl n w a d ha hd b hb φ
  have hl0 : l ≠ 0 := hl.out.ne_zero
  have hsa := GlobalTheory.KZ.isDiam_sgD_of_coprime (l := l) hl0 ha
  have hsd := GlobalTheory.KZ.isDiam_sgD_of_coprime (l := l) hl0 hd
  have hpos : ∀ g : SL(2, ℤ), 0 < (g : Matrix (Fin 2) (Fin 2) ℤ).det := fun g => by rw [g.det_coe]; exact one_pos
  have e : X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.diam N l a b) =
      X.act l ((sgD N l a * sgD N l d : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) b := by
    rw [Matrix.SpecialLinearGroup.coe_mul, GlobalTheory.KZ.Tower.diam,
      GlobalTheory.KZ.Tower.act_act Ω ε X l _ _ (hpos _) (hpos _) b]
  rw [e]
  exact GlobalTheory.T.isCuspFunctionalValueModPrimePow_diamond_independent Ω ε X A N l n w (d * a) b hb _ (GlobalTheory.KZ.isDiam_mul hsa hsd) φ
