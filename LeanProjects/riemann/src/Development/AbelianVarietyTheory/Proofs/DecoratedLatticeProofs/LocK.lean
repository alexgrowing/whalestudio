import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.QuotientFiniteLevel

variable {D : D7} {c : Comm D} {v : VCom c} {t : Tup c}

def locK (F : QFam v t) (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m) (i : Fin F.r) : Subgroup (GA D (c.V (j + 1))) :=
  ((F.Q i).T.lev (j + 1) ((F.Q i).s - j) (by have := (F.Q i).hs; omega)).J.map
    ((F.Q i).gl (j + 1) ((F.Q i).s - j) (by have := (F.Q i).hs; omega))

def qK (F : QFam v t) (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m) : Subgroup (GA D (c.V (j + 1))) :=
  ⨆ i, locK F j σ h i

end GlobalTheory.QuotientFiniteLevel
end
