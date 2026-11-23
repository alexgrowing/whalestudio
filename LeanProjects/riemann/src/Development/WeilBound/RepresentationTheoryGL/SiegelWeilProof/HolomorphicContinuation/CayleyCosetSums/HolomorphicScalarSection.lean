import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.ConjImaginaryPartFixed
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.CayleyG
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SecondCayleyBlockMulInverseCayley

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.HSt.CR

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def holomorphicScalarSection (m : ℕ) (e : ℤ) (x : M2 n) : ℂ := x.det ^ e * (u1 x).det ^ (-(m : ℤ))

def WM (x : M2 n) : Matrix (Fin n) (Fin n) ℂ :=
  (-(Complex.I • x.toBlocks₁₁) + x.toBlocks₁₂) - zOfE x * u2 x

def CauchyRiemannFacts : Prop :=
  (∀ (n m : ℕ) (e : ℤ) (y : GR n), F0 m 0 e y = holomorphicScalarSection m e (mR y)) ∧
  ∀ (n : ℕ) (x : M2 n), x.det ≠ 0 → (u1 x).det ≠ 0 →
    DifferentiableAt ℂ zOfE x ∧ (∀ (m : ℕ) (e : ℤ), DifferentiableAt ℂ (holomorphicScalarSection m e) x) ∧
    (∀ Q, fderiv ℂ zOfE x (x * lowQ Q) = 0 ∧ ∀ (m : ℕ) (e : ℤ), fderiv ℂ (holomorphicScalarSection m e) x (x * lowQ Q) = 0) ∧
    (∀ R, fderiv ℂ zOfE x (x * sig (lowQ R)) = WM x * Rᴴ * (u1 x)⁻¹) ∧
    (InG x → (WM x).det ≠ 0)

end PositivityTheory.Rg.Sw.HSt.CR
