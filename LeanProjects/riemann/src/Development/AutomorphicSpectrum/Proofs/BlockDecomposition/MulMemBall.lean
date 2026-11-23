import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

noncomputable section

open Matrix GlobalTheory.BZMir GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.BZPhiPG.Onto

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def ballSub (s : kˣ) : AddSubgroup k where
  carrier := cball s
  zero_mem' := by simp [cball]
  add_mem' := add_mem_cball
  neg_mem' := neg_mem_cball

theorem mul_mem_ball {s : kˣ} (hs : valuation k (s : k) ≤ 1) {x y : k} (hx : x ∈ cball s)
    (hy : y ∈ cball s) : x * y ∈ cball s := by
  show valuation k (x * y) ≤ valuation k (s : k)
  rw [map_mul]
  calc valuation k x * valuation k y ≤ valuation k (s : k) * 1 :=
        mul_le_mul' hx (le_trans hy hs)
    _ = valuation k (s : k) := mul_one _

def NearOne (s : kˣ) {m : ℕ} (A : Matrix (Fin m) (Fin m) k) : Prop :=
  ∀ a b, A a b - (1 : Matrix (Fin m) (Fin m) k) a b ∈ cball s

theorem NearOne.mul {s : kˣ} (hs : valuation k (s : k) ≤ 1) {m : ℕ}
    {A B : Matrix (Fin m) (Fin m) k} (hA : NearOne s A) (hB : NearOne s B) : NearOne s (A * B) := by
  intro a b
  have e : (A * B) a b - (1 : Matrix (Fin m) (Fin m) k) a b =
      ((A - 1) * (B - 1)) a b + (A a b - (1 : Matrix (Fin m) (Fin m) k) a b) +
        (B a b - (1 : Matrix (Fin m) (Fin m) k) a b) := by
    have : A * B - 1 = (A - 1) * (B - 1) + (A - 1) + (B - 1) := by noncomm_ring
    exact congrFun (congrFun this a) b
  rw [e]
  refine add_mem_cball (add_mem_cball ?_ (hA a b)) (hB a b)
  rw [Matrix.mul_apply]
  exact (ballSub s).sum_mem fun l _ => mul_mem_ball hs (hA a l) (hB l b)

variable (k) in

def congGL (s : kˣ) (hs : valuation k (s : k) ≤ 1) (m : ℕ) : Subgroup (GL (Fin m) k) where
  carrier := {g | NearOne s (g : Matrix (Fin m) (Fin m) k) ∧
    NearOne s ((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k)}
  one_mem' := by
    constructor <;> intro a b <;> simp [cball]
  mul_mem' := by
    rintro g h ⟨g1, g2⟩ ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]
      exact g1.mul hs h1
    · rw [_root_.mul_inv_rev, Units.val_mul]
      exact h2.mul hs g2
  inv_mem' := by
    rintro g ⟨g1, g2⟩
    exact ⟨g2, by simpa using g1⟩

variable (k) in

def congM (s : kˣ) (hs : valuation k (s : k) ≤ 1) (n : ℕ) : Subgroup (Mir k n) :=
  (congGL k s hs (n + 1)).comap (Mir k n).subtype

end GlobalTheory.CompanionTheory.BZPhiPG.Onto

end
