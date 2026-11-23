import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsQuasiFiniteSheets
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsPrimeQuasiFiniteSheets
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsPrimePairMeetImage
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

namespace QuasiFiniteSheets

variable {n d : ℕ}

def HasSheetsOff (S : Set (Fin n → ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (c : MvPolynomial (Fin d) ℂ) : Prop :=
  ∀ y : Fin d → ℂ, eval y c ≠ 0 →
    ∃ (U : Set (Fin d → ℂ)) (N : ℕ) (s : Fin N → (Fin d → ℂ) → Fin n → ℂ),
      IsOpen U ∧ y ∈ U ∧ (∀ j, DifferentiableOn ℂ (s j) U) ∧
      ∀ y' ∈ U, (∀ j, s j y' ∈ {x | x ∈ S ∧ A.mulVec x = y'}) ∧
        Function.Injective (fun j => s j y') ∧
        {x | x ∈ S ∧ A.mulVec x = y'} ⊆ Set.range (fun j => s j y')

theorem hasSheetsOff_empty (A : Matrix (Fin d) (Fin n) ℂ) : HasSheetsOff ∅ A 1 := by
  intro y _
  refine ⟨Set.univ, 0, Fin.elim0, isOpen_univ, Set.mem_univ _, fun j => j.elim0, fun y' _ => ?_⟩
  refine ⟨fun j => j.elim0, fun i => i.elim0, ?_⟩
  rintro x ⟨hx, -⟩
  exact hx.elim

theorem hasSheetsOff_union {S T : Set (Fin n → ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {c c' e : MvPolynomial (Fin d) ℂ} (h₁ : HasSheetsOff S A c) (h₂ : HasSheetsOff T A c')
    (he : ∀ x ∈ S ∩ T, eval (A.mulVec x) e = 0) : HasSheetsOff (S ∪ T) A (c * c' * e) := by
  intro y hy
  simp only [map_mul, ne_eq, mul_eq_zero, not_or] at hy
  obtain ⟨⟨hc, hc'⟩, hey⟩ := hy
  obtain ⟨U₁, N₁, s₁, hU₁, hyU₁, hd₁, hs₁⟩ := h₁ y hc
  obtain ⟨U₂, N₂, s₂, hU₂, hyU₂, hd₂, hs₂⟩ := h₂ y hc'
  refine ⟨U₁ ∩ U₂ ∩ {w | eval w e ≠ 0}, N₁ + N₂, Fin.append s₁ s₂,
    (hU₁.inter hU₂).inter (isOpen_ne_fun (MvPolynomial.continuous_eval e) continuous_const),
    ⟨⟨hyU₁, hyU₂⟩, hey⟩, fun j => ?_, ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · rw [Fin.append_left]; exact (hd₁ j).mono fun w hw => hw.1.1
    · rw [Fin.append_right]; exact (hd₂ j).mono fun w hw => hw.1.2
  rintro w ⟨⟨hw₁, hw₂⟩, hwe⟩
  obtain ⟨hm₁, hi₁, hr₁⟩ := hs₁ w hw₁
  obtain ⟨hm₂, hi₂, hr₂⟩ := hs₂ w hw₂
  have hcross : ∀ i j, s₁ i w ≠ s₂ j w := by
    intro i j hij
    apply hwe
    rw [← (hm₁ i).2]
    exact he _ ⟨(hm₁ i).1, hij ▸ (hm₂ j).1⟩
  refine ⟨fun j => ?_, fun i j hij => ?_, ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · rw [Fin.append_left]; exact ⟨Or.inl (hm₁ j).1, (hm₁ j).2⟩
    · rw [Fin.append_right]; exact ⟨Or.inr (hm₂ j).1, (hm₂ j).2⟩
  · induction i using Fin.addCases with
    | left i =>
      induction j using Fin.addCases with
      | left j => simp only [Fin.append_left] at hij; rw [hi₁ hij]
      | right j => simp only [Fin.append_left, Fin.append_right] at hij; exact (hcross i j hij).elim
    | right i =>
      induction j using Fin.addCases with
      | left j => simp only [Fin.append_left, Fin.append_right] at hij; exact (hcross j i hij.symm).elim
      | right j => simp only [Fin.append_right] at hij; rw [hi₂ hij]
  · rintro x ⟨hx | hx, hAx⟩
    · obtain ⟨j, rfl⟩ := hr₁ ⟨hx, hAx⟩
      exact ⟨Fin.castAdd N₂ j, by simp only [Fin.append_left]⟩
    · obtain ⟨j, rfl⟩ := hr₂ ⟨hx, hAx⟩
      exact ⟨Fin.natAdd N₁ j, by simp only [Fin.append_right]⟩

theorem hasSheetsOff_biUnion (F : Finset (Ideal (MvPolynomial (Fin n) ℂ))) (A : Matrix (Fin d) (Fin n) ℂ)
    (hsh : ∀ Q ∈ F, ∃ c : MvPolynomial (Fin d) ℂ, c ≠ 0 ∧ HasSheetsOff (ComplexSets.zeroSet Q) A c)
    (hpair : ∀ Q ∈ F, ∀ Q' ∈ F, Q ≠ Q' → ∃ e : MvPolynomial (Fin d) ℂ, e ≠ 0 ∧
      ∀ x ∈ ComplexSets.zeroSet Q ∩ ComplexSets.zeroSet Q', eval (A.mulVec x) e = 0) :
    ∃ c : MvPolynomial (Fin d) ℂ, c ≠ 0 ∧ HasSheetsOff (⋃ Q ∈ F, ComplexSets.zeroSet Q) A c := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simpa using hasSheetsOff_empty A⟩
  | insert Q F hQ ih =>
    obtain ⟨c₀, hc₀, h₀⟩ := ih (fun Q' h => hsh Q' (Finset.mem_insert_of_mem h))
      (fun Q' h Q'' h' hne => hpair Q' (Finset.mem_insert_of_mem h) Q'' (Finset.mem_insert_of_mem h') hne)
    obtain ⟨c, hc, h⟩ := hsh Q (Finset.mem_insert_self _ _)
    have hp : ∀ Q' ∈ F, ∃ e : MvPolynomial (Fin d) ℂ, e ≠ 0 ∧
        ∀ x ∈ ComplexSets.zeroSet Q ∩ ComplexSets.zeroSet Q', eval (A.mulVec x) e = 0 :=
      fun Q' hQ' => hpair Q (Finset.mem_insert_self _ _) Q' (Finset.mem_insert_of_mem hQ')
        (by rintro rfl; exact hQ hQ')
    choose! e he0 he using hp
    refine ⟨c * c₀ * ∏ Q' ∈ F, e Q', mul_ne_zero (mul_ne_zero hc hc₀) (Finset.prod_ne_zero_iff.mpr he0), ?_⟩
    rw [Finset.set_biUnion_insert]
    refine hasSheetsOff_union h h₀ ?_
    rintro x ⟨hxQ, hxF⟩
    obtain ⟨Q', hQ', hx'⟩ := Set.mem_iUnion₂.mp hxF
    rw [map_prod]
    exact Finset.prod_eq_zero hQ' (he Q' hQ' x ⟨hxQ, hx'⟩)

end QuasiFiniteSheets

open QuasiFiniteSheets in

theorem QuasiFiniteSheets.proof (h₁ : PrimeQuasiFiniteSheets.Statement)
    (h₂ : PrimePairMeetImage.Statement) : QuasiFiniteSheets.Statement := by
  intro n d I A hfin
  classical
  have hmin := I.finite_minimalPrimes_of_isNoetherianRing
  have hfinQ : ∀ Q ∈ I.minimalPrimes, ∀ y, (ComplexSets.fibre Q A y).Finite := fun Q hQ y =>
    (hfin y).subset fun x hx => ⟨fun q hq => hx.1 q (hQ.1.2 hq), hx.2⟩
  have hZ : ComplexSets.zeroSet I = ⋃ Q ∈ hmin.toFinset, ComplexSets.zeroSet Q := by
    ext x
    constructor
    · intro hx
      have hker : I ≤ RingHom.ker (eval x) := fun q hq => hx q hq
      have : (RingHom.ker (eval x : MvPolynomial (Fin n) ℂ →+* ℂ)).IsPrime := RingHom.ker_isPrime _
      obtain ⟨Q, hQ, hQle⟩ := Ideal.exists_minimalPrimes_le hker
      exact Set.mem_iUnion₂.mpr ⟨Q, hmin.mem_toFinset.mpr hQ, fun q hq => hQle hq⟩
    · intro hx
      obtain ⟨Q, hQ, hxQ⟩ := Set.mem_iUnion₂.mp hx
      exact fun q hq => hxQ q ((hmin.mem_toFinset.mp hQ).1.2 hq)
  obtain ⟨c, hc, hsh⟩ := hasSheetsOff_biUnion hmin.toFinset A
    (fun Q hQ => h₁ n d Q A (hmin.mem_toFinset.mp hQ).1.1 (hfinQ Q (hmin.mem_toFinset.mp hQ)))
    (fun Q hQ Q' hQ' hne => h₂ n d Q Q' A (hmin.mem_toFinset.mp hQ).1.1 (hmin.mem_toFinset.mp hQ').1.1 hne
      (hfinQ Q (hmin.mem_toFinset.mp hQ)) (hfinQ Q' (hmin.mem_toFinset.mp hQ')))
  rw [← hZ] at hsh
  exact ⟨c, hc, hsh⟩

end GroundTheory.Heights₂.Heights
