import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksFgB
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMapB
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs GlobalTheory.SmGL

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration

set_option linter.unusedSectionVars false

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r s : ℕ}

def lowL (X : Lie E (r + s)) : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E) :=
  Matrix.of fun i j => if r ≤ (i : ℕ) ∧ (j : ℕ) < r then X i j else 0

def skw (X : Lie E (r + s)) : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E) := lowL X - (lowL X)ᴴ

theorem skw_skew (X : Lie E (r + s)) : (skw X)ᴴ = -skw X := by
  rw [skw, conjTranspose_sub, conjTranspose_conjTranspose, neg_sub]

theorem par_low (X : Lie E (r + s)) (i : Fin s) (j : Fin r) :
    (X - toL (skw X)) (Fin.natAdd r i) (Fin.castAdd s j) = 0 := by
  have h1 : lowL X (Fin.natAdd r i) (Fin.castAdd s j) = X (Fin.natAdd r i) (Fin.castAdd s j) := by
    simp [lowL]
  have h2 : lowL X (Fin.castAdd s j) (Fin.natAdd r i) = 0 := by
    simp [lowL]
  change X (Fin.natAdd r i) (Fin.castAdd s j) - (lowL X (Fin.natAdd r i) (Fin.castAdd s j) -
    star (lowL X (Fin.castAdd s j) (Fin.natAdd r i))) = 0
  rw [h1, h2, star_zero, sub_zero, sub_self]

theorem lie_split (X : Lie E (r + s)) (F : Sm E (r + s)) :
    lie E (r + s) X F = lie E (r + s) (X - toL (skw X)) F + lie E (r + s) (toL (skw X)) F := by
  rw [← LinearMap.add_apply, ← map_add, sub_add_cancel]

theorem yp_mul {a : ℕ} (k k' : Kinf E a) (g g' : GL (Fin a) (Af E)) :
    BlockDerivatives.yp k g * BlockDerivatives.yp k' g' = BlockDerivatives.yp (k * k') (g * g') :=
  InducedTensorMap.cf_mul a k k' g g'

theorem rt_yp_rt {a : ℕ} (k k' : Kinf E a) (g g' : GL (Fin a) (Af E)) (φ : Sm E a) :
    rt E a (BlockDerivatives.yp k g) (rt E a (BlockDerivatives.yp k' g') φ) = rt E a (BlockDerivatives.yp (k * k') (g * g')) φ := by
  rw [← yp_mul, map_mul, Module.End.mul_apply]

theorem act_fin_eq {a : ℕ} (h : GL (Fin a) (Af E)) (φ : Sm E a) : act (.fin h) φ = rt E a (BlockDerivatives.yp 1 h) φ := by
  refine Subtype.ext (funext fun x => ?_)
  simp [BlockDerivatives.yp]
  rfl

theorem act_cpt_eq {a : ℕ} (κ : Kinf E a) (φ : Sm E a) : act (.cpt κ) φ = rt E a (BlockDerivatives.yp κ 1) φ := by
  refine Subtype.ext (funext fun x => ?_)
  simp [BlockDerivatives.yp]
  rfl

theorem rt_lie_yp {a : ℕ} (k : Kinf E a) (g : GL (Fin a) (Af E)) (X : Lie E a) :
    ∃ X' : Lie E a, rt E a (BlockDerivatives.yp k g) * lie E a X = lie E a X' * rt E a (BlockDerivatives.yp k g) := by
  refine ⟨toL ((Unitary.toUnits k).val * Matrix.of X * ((Unitary.toUnits k)⁻¹).val), ?_⟩
  rw [BlockDerivatives.yp, map_mul, mul_assoc, ← lie_rt_fin, ← mul_assoc, ← mul_assoc]
  exact congrArg (· * _) (GlobalTheory.CapAdInv.rt_lie (Unitary.toUnits k) (Matrix.of X))

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration
