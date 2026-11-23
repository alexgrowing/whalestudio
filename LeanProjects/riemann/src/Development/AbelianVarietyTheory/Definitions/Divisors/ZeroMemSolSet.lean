import Mathlib
import Formalism.UnipotentAdelicQuotients.EllReg

noncomputable section

open ZetaZeros.D.EllReg
open scoped BoundedContinuousFunction

namespace GlobalTheory.HCA

variable {d : ℕ}

def apOp (m : ℕ) (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (u : E d → ℂ) (x : E d) : ℂ :=
  ∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d, a n w x * dw (List.ofFn w) u x

def symb (m : ℕ) (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (x ξ : E d) : ℂ :=
  ∑ w : Fin m → Fin d, a m w x * ∏ l, ((ξ (w l) : ℝ) : ℂ)

def oneSys (m : ℕ) (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) : Sys d Unit := ⟨fun _ => m, fun _ => a⟩

open Classical in

def ext0 (U : Set (E d)) (u : U → ℂ) (x : E d) : ℂ := if hx : x ∈ U then u ⟨x, hx⟩ else 0

def solSet {ι : Type} (P : Sys d ι) (U : Set (E d)) : Set (U →ᵇ ℂ) := {u | WeakSol P U (ext0 U u)}

open scoped BoundedContinuousFunction in
variable {d : ℕ} in

theorem _root_.GlobalTheory.HCA.apOp_zero_one (u : _root_.ZetaZeros.D.EllReg.E d → ℂ) (x : _root_.ZetaZeros.D.EllReg.E d) :
    _root_.GlobalTheory.HCA.apOp 0 (fun _ _ _ => 1) u x = u x := by
  simp only [_root_.GlobalTheory.HCA.apOp, zero_add, Finset.range_one, Finset.sum_singleton,
    one_mul, Fintype.sum_unique, List.ofFn_zero]
  unfold _root_.ZetaZeros.D.EllReg.dw
  rfl

open scoped BoundedContinuousFunction in
variable {d : ℕ} in

theorem _root_.GlobalTheory.HCA.zero_mem_solSet {ι : Type} (P : _root_.ZetaZeros.D.EllReg.Sys d ι) (U : Set (_root_.ZetaZeros.D.EllReg.E d)) :
    (0 : U →ᵇ ℂ) ∈ _root_.GlobalTheory.HCA.solSet P U := by
  have h : _root_.GlobalTheory.HCA.ext0 U (0 : U →ᵇ ℂ) = fun _ => 0 := by
    funext x
    unfold _root_.GlobalTheory.HCA.ext0
    split_ifs <;> rfl
  show _root_.ZetaZeros.D.EllReg.WeakSol P U (_root_.GlobalTheory.HCA.ext0 U (0 : U →ᵇ ℂ))
  rw [h]
  unfold _root_.ZetaZeros.D.EllReg.WeakSol
  intro i φ _ _ _
  simp

end GlobalTheory.HCA

end
