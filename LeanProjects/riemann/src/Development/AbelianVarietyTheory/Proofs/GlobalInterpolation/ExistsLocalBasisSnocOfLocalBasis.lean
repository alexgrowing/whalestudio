import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Formalism.LocalToGlobal.Columns.TiedValLatG
import Formalism.LocalToGlobal.Columns.CoefModB
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

noncomputable section

namespace GlobalTheory.LocBasisSnoc

variable {E : Type} [Field E] {n : ℕ}

def blk (A : Matrix (Fin n) (Fin n) E) (c : E) : Matrix (Fin (n + 1)) (Fin (n + 1)) E :=
  Matrix.of fun i j => Fin.lastCases (Fin.lastCases c (fun _ => 0) j)
    (fun i' => Fin.lastCases 0 (fun j' => A i' j') j) i

theorem blk_mulVec_castSucc (A : Matrix (Fin n) (Fin n) E) (c : E) (x : Fin (n + 1) → E) (i : Fin n) :
    (blk A c *ᵥ x) i.castSucc = (A *ᵥ Fin.init x) i := by
  simp [blk, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, Fin.init]

theorem blk_mulVec_last (A : Matrix (Fin n) (Fin n) E) (c : E) (x : Fin (n + 1) → E) :
    (blk A c *ᵥ x) (Fin.last n) = c * x (Fin.last n) := by
  simp [blk, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]

theorem blk_mulVec_ext {P Q : Matrix (Fin (n + 1)) (Fin (n + 1)) E} (h : ∀ x, P *ᵥ x = Q *ᵥ x) : P = Q :=
  Matrix.ext_of_mulVec_single fun j => h _

theorem blk_mul (A A' : Matrix (Fin n) (Fin n) E) (c c' : E) :
    blk A c * blk A' c' = blk (A * A') (c * c') := by
  refine blk_mulVec_ext fun x => ?_
  rw [← Matrix.mulVec_mulVec]
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [blk_mulVec_last, blk_mulVec_last, blk_mulVec_last, mul_assoc]
  · rw [blk_mulVec_castSucc, blk_mulVec_castSucc, ← Matrix.mulVec_mulVec]
    congr 2
    funext k
    exact blk_mulVec_castSucc _ _ _ _

theorem blk_one : blk (1 : Matrix (Fin n) (Fin n) E) 1 = 1 := by
  refine blk_mulVec_ext fun x => ?_
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [blk_mulVec_last, one_mul, Matrix.one_mulVec]
  · rw [blk_mulVec_castSucc, Matrix.one_mulVec, Matrix.one_mulVec]
    rfl

end GlobalTheory.LocBasisSnoc

open GlobalTheory.LocBasisSnoc in

theorem GlobalTheory.isLocBasis_snoc : ∀ {E : Type} [Field E] [NumberField E] {N n : ℕ} (hN : N = n + 1) (t : E), t ≠ 0 → ∀ (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin n → E)), (∀ x, x ∈ L ↔ iniH hN x ∈ L' ∧ t * x (Br.iL hN) ∈ (1 : Submodule (𝓞 E) E)) → ∀ (p : ℕ) (B' : GL (Fin n) E), p.Prime → IsLocBasis p (L' : Set (Fin n → E)) B' → ∃ B : GL (Fin N) E, (∀ x, iniH hN ((B : Matrix (Fin N) (Fin N) E) *ᵥ x) = (B' : Matrix (Fin n) (Fin n) E) *ᵥ iniH hN x) ∧ (∀ x, t * ((B : Matrix (Fin N) (Fin N) E) *ᵥ x) (Br.iL hN) = x (Br.iL hN)) ∧ IsLocBasis p (L : Set (Fin N → E)) B := by
  intro E _ _ N n hN t ht L L' hL p B' hp hB'
  subst hN
  let B : GL (Fin (n + 1)) E :=
    ⟨blk (B' : Matrix (Fin n) (Fin n) E) t⁻¹, blk ((B'⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) t,
      by rw [blk_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, inv_mul_cancel₀ ht, blk_one],
      by rw [blk_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_inv_cancel₀ ht, blk_one]⟩
  have hini : ∀ y : Fin (n + 1) → E, iniH rfl y = Fin.init y := fun y => rfl
  have hlast : (Br.iL (rfl : n + 1 = n + 1)) = Fin.last n := rfl
  refine ⟨B, fun x => ?_, fun x => ?_, ?_⟩
  · rw [hini, hini]
    funext i
    exact blk_mulVec_castSucc _ _ _ _
  · rw [hlast]
    show t * (blk _ t⁻¹ *ᵥ x) (Fin.last n) = _
    rw [blk_mulVec_last, ← mul_assoc, mul_inv_cancel₀ ht, one_mul]
  · intro x
    have hinv : ((B⁻¹ : GL (Fin (n + 1)) E) : Matrix _ _ E) = blk ((B'⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) t := rfl
    rw [hinv]
    set R := (algebraMap (𝓞 E) E).range
    have hR : ∀ (s : ℕ) {y : E}, y ∈ R → (s : E) * y ∈ R := fun s y hy => R.mul_mem (natCast_mem R s) hy
    have key : ∀ s : ℕ, (∀ a, (s : E) * (blk ((B'⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) t *ᵥ x) a ∈ R) ↔
        (∀ a, (s : E) * (((B'⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ Fin.init x) a ∈ R) ∧
          (s : E) * (t * x (Fin.last n)) ∈ R := by
      intro s
      constructor
      · intro h
        refine ⟨fun a => ?_, ?_⟩
        · have := h a.castSucc
          rwa [blk_mulVec_castSucc] at this
        · have := h (Fin.last n)
          rwa [blk_mulVec_last] at this
      · rintro ⟨h1, h2⟩ a
        refine Fin.lastCases ?_ (fun i => ?_) a
        · rw [blk_mulVec_last]; exact h2
        · rw [blk_mulVec_castSucc]; exact h1 i
    have memL : ∀ s : ℕ, (s : E) • x ∈ L ↔ (s : E) • Fin.init x ∈ L' ∧ (s : E) * (t * x (Fin.last n)) ∈ R := by
      intro s
      rw [hL, hini, hlast, Submodule.mem_one]
      have e : t * ((s : E) • x) (Fin.last n) = (s : E) * (t * x (Fin.last n)) := by
        rw [Pi.smul_apply, smul_eq_mul, mul_left_comm]
      rw [e]
      rfl
    have hnd : ∀ a b : ℕ, ¬ p ∣ a → ¬ p ∣ b → ¬ p ∣ a * b := fun a b ha hb h =>
      (hp.dvd_mul.mp h).elim ha hb
    have hB := hB' (Fin.init x)
    constructor
    · rintro ⟨s, hs, hx⟩
      obtain ⟨h1, h2⟩ := (memL s).mp hx
      obtain ⟨s', hs', h3⟩ := hB.mp ⟨s, hs, h1⟩
      refine ⟨s * s', hnd _ _ hs hs', (key _).mpr ⟨fun a => ?_, ?_⟩⟩
      · rw [Nat.cast_mul, mul_assoc]; exact hR s (h3 a)
      · rw [Nat.cast_mul, mul_comm (s : E), mul_assoc]; exact hR s' h2
    · rintro ⟨s, hs, h⟩
      obtain ⟨h1, h2⟩ := (key s).mp h
      obtain ⟨s', hs', h3⟩ := hB.mpr ⟨s, hs, h1⟩
      refine ⟨s * s', hnd _ _ hs hs', (memL _).mpr ⟨?_, ?_⟩⟩
      · rw [Nat.cast_mul, mul_smul, Nat.cast_smul_eq_nsmul]
        exact nsmul_mem h3 s
      · rw [Nat.cast_mul, mul_comm (s : E), mul_assoc]; exact hR s' h2
