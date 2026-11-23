import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusElementActsOnFrameColumns
import GroundTheory.GlobalFields.Adele.IntegersLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdaptedBasisWittFrame

noncomputable section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.LeviRed

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def rE (s : ℝ) : AF F ⊗[F] E := algebraMap (AF F) (AF F ⊗[F] E) (GlobalTheory.TorusTheta.infScale F s)

def dM {n : ℕ} (a : Fin n → ℝ) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := diagonal fun i => rE F E (a i)

def nxt {r : ℕ} (t : Fin r → ℝ) (i : Fin r) : ℝ := if h : i.val + 1 < r then t ⟨i.val + 1, h⟩ else 1

omit [NumberField E] in
theorem rE_mul (a b : ℝ) : rE F E (a * b) = rE F E a * rE F E b := by
  rw [rE, rE, rE, ← map_mul]
  congr 1
  refine Prod.ext ?_ (mul_one _).symm
  show _ = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _ * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _
  rw [← map_mul, ← map_mul]
  rfl

omit [NumberField E] in
theorem rE_one : rE F E 1 = 1 := by
  rw [rE, ← map_one (algebraMap (AF F) (AF F ⊗[F] E))]
  congr 1
  simp only [GlobalTheory.TorusTheta.infScale, map_one]
  rfl

def extT (n : ℕ) {r : ℕ} (t : Fin r → ℝ) (i : Fin n) : ℝ :=
  if h : i.val < r then t ⟨i.val, h⟩ else if h' : i.rev.val < r then (t ⟨i.rev.val, h'⟩)⁻¹ else 1

def lev (n : ℕ) {r : ℕ} (S : Finset (Fin r)) : Fin n → ℝ :=
  extT n fun i => Real.exp (GlobalTheory.StdPar.stepSum S (fun _ => 1) i)

open GlobalTheory.AdelicU GlobalTheory.SiegelSet

variable {F E} (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def crd (B : GL (Fin n) E) (g : GAd σ J) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) :=
  adMat F (B⁻¹).1 * (matHom _ σ J g).1 * adMat F B.1

end GlobalTheory.LeviRed
