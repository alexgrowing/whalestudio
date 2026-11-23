import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTamagawa
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulVecMemGenLatSmul

noncomputable section

open Matrix Classical

namespace GlobalTheory.SUCong

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

def piIdeal (S : Subring A) (ϖ : A) : Ideal S := Ideal.span {x : S | (x : A) = ϖ}

abbrev Res (S : Subring A) (ϖ : A) : Type := S ⧸ piIdeal S ϖ

def red (S : Subring A) (ϖ : A) (a : A) : Res S ϖ :=
  if h : a ∈ S then Ideal.Quotient.mk _ ⟨a, h⟩ else 0

def InPow (S : Subring A) (ϖ : A) (k : ℕ) (a : A) : Prop := ∃ s ∈ S, a = ϖ ^ k * s

def congSU (S : Subring A) (σ : A →+* A) (H : Matrix n n A) (ϖ : A) (k : ℕ) : Subgroup (GL n A) where
  carrier := {g | g ∈ Formalism.UG.UJ σ H ∧ (g : Matrix n n A).det = 1 ∧
    (∀ i j, (g : Matrix n n A) i j ∈ S) ∧ (∀ i j, ((g⁻¹ : GL n A) : Matrix n n A) i j ∈ S) ∧
    ∀ i j, InPow S ϖ k (((g : Matrix n n A) - 1) i j)}
  one_mem' := by
    refine ⟨one_mem _, by simp, fun i j => ?_, fun i j => ?_, fun i j => ⟨0, zero_mem _, by simp⟩⟩
    · simp only [Units.val_one, one_apply]; split_ifs <;> simp [one_mem, zero_mem]
    · simp only [inv_one, Units.val_one, one_apply]; split_ifs <;> simp [one_mem, zero_mem]
  mul_mem' {a b} ha hb := by
    refine ⟨mul_mem ha.1 hb.1, by rw [Units.val_mul, det_mul, ha.2.1, hb.2.1, one_mul], fun i j => ?_,
      fun i j => ?_, fun i j => ?_⟩
    · rw [Units.val_mul, mul_apply]
      exact Subring.sum_mem _ fun l _ => mul_mem (ha.2.2.1 i l) (hb.2.2.1 l j)
    · rw [_root_.mul_inv_rev, Units.val_mul, mul_apply]
      exact Subring.sum_mem _ fun l _ => mul_mem (hb.2.2.2.1 i l) (ha.2.2.2.1 l j)
    · have e : ((a * b : GL n A) : Matrix n n A) - 1 =
          (a : Matrix n n A) * ((b : Matrix n n A) - 1) + ((a : Matrix n n A) - 1) := by
        rw [Units.val_mul, Matrix.mul_sub, Matrix.mul_one, sub_add_sub_cancel]
      rw [e, Matrix.add_apply, mul_apply]
      choose s hs he using hb.2.2.2.2
      choose t ht hte using ha.2.2.2.2
      refine ⟨(∑ l, (a : Matrix n n A) i l * s l j) + t i j,
        add_mem (Subring.sum_mem _ fun l _ => mul_mem (ha.2.2.1 i l) (hs l j)) (ht i j), ?_⟩
      rw [hte, mul_add, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [he]; ring
  inv_mem' {a} ha := by
    refine ⟨inv_mem ha.1, ?_, ha.2.2.2.1, by simpa using ha.2.2.1, fun i j => ?_⟩
    · have h := congrArg Matrix.det (Units.inv_mul a)
      rwa [Matrix.det_mul, ha.2.1, mul_one, Matrix.det_one] at h
    · have e : ((a⁻¹ : GL n A) : Matrix n n A) - 1 =
          -(((a⁻¹ : GL n A) : Matrix n n A) * ((a : Matrix n n A) - 1)) := by
        rw [Matrix.mul_sub, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one, neg_sub]
      rw [e, Matrix.neg_apply, mul_apply]
      choose t ht hte using ha.2.2.2.2
      refine ⟨-(∑ l, ((a⁻¹ : GL n A) : Matrix n n A) i l * t l j),
        neg_mem (Subring.sum_mem _ fun l _ => mul_mem (ha.2.2.2.1 i l) (ht l j)), ?_⟩
      rw [mul_neg, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hte]; ring

def levMap (S : Subring A) (ϖ : A) (k : ℕ) (g : Matrix n n A) : Matrix n n (Res S ϖ) :=
  fun i j => if h : InPow S ϖ k ((g - 1) i j) then red S ϖ (Classical.choose h) else 0

def skewTr (S : Subring A) (σ : A →+* A) (H : Matrix n n A) (ϖ : A) : Set (Matrix n n (Res S ϖ)) :=
  {Y | ∃ X : Matrix n n A, (∀ i j, X i j ∈ S) ∧ (∀ i j, Y i j = red S ϖ (X i j)) ∧
    (∀ i j, InPow S ϖ 1 ((Formalism.UG.cT σ X * H + H * X) i j)) ∧ InPow S ϖ 1 X.trace}

def GoodRing (S : Subring A) (σ : A →+* A) (ϖ : A) (q : ℕ) : Prop :=
  (∀ a, σ (σ a) = a) ∧ (∀ s ∈ S, σ s ∈ S) ∧ ϖ ∈ S ∧ σ ϖ = ϖ ∧ (∀ a : A, ϖ * a = 0 → a = 0) ∧
  (∃ w ∈ S, w + σ w = 1 ∧ (∃ u ∈ S, (w - σ w) * u = 1) ∧
    ∀ s ∈ S, ∃ a ∈ S, ∃ b ∈ S, σ a = a ∧ σ b = b ∧ s = a + b * w) ∧
  (∀ a ∈ S, σ a = a → (¬ InPow S ϖ 1 a) → ∃ b ∈ S, a * b = 1) ∧
  Nat.card {x : Res S ϖ // ∃ a ∈ S, σ a = a ∧ x = red S ϖ a} = q

def GoodForm (S : Subring A) (σ : A →+* A) (H : Matrix n n A) : Prop :=
  (∀ i j, H i j ∈ S) ∧ Formalism.UG.cT σ H = H ∧ ∃ H' : Matrix n n A, (∀ i j, H' i j ∈ S) ∧ H * H' = 1

end GlobalTheory.SUCong

namespace GlobalTheory.SUCong

section Concrete

open IsDedekindDomain NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def intA (v : HeightOneSpectrum (𝓞 F)) : Subring (Fv F v ⊗[F] E) :=
  Subring.closure {y | ∃ a ∈ v.adicCompletionIntegers F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}

end Concrete

end GlobalTheory.SUCong
