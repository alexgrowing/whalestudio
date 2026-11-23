import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatGLOfInvT
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsNormalisedOfDualIsConj

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS
open GlobalTheory.LFun.ConjPlace (invT dGL apply_heckeVec_shift Tj_invT Tj_shift_self map_mem_Ov_iff mem_iff_invT satEig_inv_mul satEig_zero)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.ThetaSatPair

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

variable {u w : Pl E}

def pairInv (c : u.adicCompletion E ≃+* w.adicCompletion E) (a b : ℕ) : GLw a u × GLw b u ≃* GLw a w × GLw b w :=
  MulEquiv.prodCongr (invT c a) (invT c b)

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def pairConj (c : u.adicCompletion E ≃+* w.adicCompletion E) (k : GLw a u × GLw b u) :
    GLw a u × GLw b u ≃* GLw a w × GLw b w :=
  MulEquiv.trans (MulAut.conj k⁻¹) (pairInv c a b)

theorem embT_cw (a : ℕ) (u : Pl E) (g : GLw a (GlobalTheory.ThetaSatake.cw u)) :
    embT a (GlobalTheory.ThetaSatake.cw u) g =
      embW a u (PhiU a _ * invT (GlobalTheory.ThetaSatake.cloc u) a g * (PhiU a _)⁻¹) := by
  change GlobalTheory.ThetaPull.thetaA E a (finGL E a (locGL E a (GlobalTheory.ThetaSatake.cw u) g)) = finGL E a (locGL E a u _)
  rw [GlobalTheory.ThetaPull.thetaA_finGL, GlobalTheory.ThetaSatake.theta_locGL, GlobalTheory.ThetaSatake.thetaGL_conj]

theorem invT_symm {K K' : Type} [Field K] [Field K'] (c : K ≃+* K') (n : ℕ) (g : GL (Fin n) K') :
    (invT c n).symm g = invT c.symm n g := rfl

end GlobalTheory.CompanionTheory.ThetaSatPair
