import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsIntZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadMod
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsAdmissibleLinearFunctional

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.CtS

theorem blk_val_det {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b : ℕ} (h : a + b = n) (w : Pl E)
    (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (blk h w m X).val.det = m.1.val.det * m.2.val.det := by
  have hdet : (Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val)).det = m.1.val.det * m.2.val.det := by
    rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
  have h1 : IsUnit m.1.val.det := (Matrix.isUnit_iff_isUnit_det _).1 m.1.isUnit
  have h2 : IsUnit m.2.val.det := (Matrix.isUnit_iff_isUnit_det _).1 m.2.isUnit
  have hu : IsUnit (Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val)) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (hdet ▸ h1.mul h2)
  simp only [blk]
  rw [dif_pos hu, IsUnit.unit_spec]
  exact hdet

theorem ordL_blk_det : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E)
    (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)),
    ordL (blk h w m X).val.det = ordL m.1.val.det + ordL m.2.val.det := by
  intro E _ _ _ n a b h w m X
  have h1 : IsUnit m.1.val.det := (Matrix.isUnit_iff_isUnit_det _).1 m.1.isUnit
  have h2 : IsUnit m.2.val.det := (Matrix.isUnit_iff_isUnit_det _).1 m.2.isUnit
  rw [blk_val_det, GlobalTheory.CompanionTheory.SwapInt.ordL_mul_of_ne h1.ne_zero h2.ne_zero]

end GlobalTheory.CompanionTheory.CtS
