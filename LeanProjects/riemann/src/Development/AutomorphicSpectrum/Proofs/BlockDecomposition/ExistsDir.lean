import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.ComplexMatrixMajorantIntegrable

noncomputable section

open MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.InnQ

open Ad3.K Ad3.K.LC Ad3.K.LC.C

abbrev V : Type := Fin 2 → ℂ
abbrev E5 : Type := M23 × V

def Pm (h : M22) (x : V) : M23 := Matrix.of.symm (Matrix.of h * blk x)

def Lh (h : M22) : V →ₗ[ℝ] M23 where
  toFun x := fun i j => if j = 2 then (Matrix.of h *ᵥ x) i else 0
  map_add' x y := by
    ext i j; by_cases hj : j = 2 <;> simp [hj, Matrix.mulVec_add]
  map_smul' c x := by
    ext i j; by_cases hj : j = 2 <;> simp [hj, Matrix.mulVec_smul]

def I0 : ℝ := ∫ y : V, (1 + ‖y‖) ^ (-(5 : ℝ))

def Bd (G : Sw) (K n : ℕ) (B : ℝ) : Prop :=
  ∀ m ≤ n, ∀ Y : E5, (1 + ‖Y‖) ^ K * ‖iteratedFDeriv ℝ m G Y‖ ≤ B

theorem Bd.mono {G : Sw} {K n n' : ℕ} {B : ℝ} (h : Bd G K n B) (hn : n' ≤ n) : Bd G K n' B :=
  fun m hm => h m (hm.trans hn)

def II (G : Sw) (h : M22) (β : ℂ) (q : V) : ℂ := ∫ x : V, G (Pm h x, q) * psiC (-(β * x 1))

def chi (β : ℂ) (x : V) : ℂ := psiC (-(β * x 1))

def Fd (G : Sw) (h : M22) (β : ℂ) (q x : V) : V →L[ℝ] ℂ :=
  chi β x • (fderiv ℝ G (Pm h x, q)).comp (ContinuousLinearMap.inr ℝ M23 V)

abbrev dd (e : E5) (G : Sw) : Sw := LineDeriv.lineDerivOp e G

def Tph (β : ℂ) : V →L[ℝ] ℂ :=
  (4 * Real.pi * Complex.I : ℂ) • (Complex.ofRealCLM.comp (Complex.reCLM.comp
    (β • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℂ) 1)))

end GlobalTheory.CompanionTheory.InnQ
