import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevOpParabEqLevOpCt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockLevelsTwistedConstantTermSplitPlace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumSatEqOfIsCT

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.RS

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev tJ {w : Pl E} {ϖ : w.adicCompletion E} (h0 : ϖ ≠ 0) (m i : ℕ) : GLw m w :=
  GlobalTheory.WeylGL.tor h0 fun r : Fin m => if (r : ℕ) < i then 1 else 0

def dCt (q : ℕ) (c : ℂˣ) (a b i j : ℕ) : ℂ :=
  ((c ^ (i * b + j * a) : ℂˣ) : ℂ) * ((q : ℂ) ^ ((((j * a : ℕ) : ℂ) - ((i * b : ℕ) : ℂ)) / 2) * (q : ℂ) ^ (i * (b - j)))

abbrev pairsK (a b k : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (a + 1) ×ˢ Finset.range (b + 1)).filter fun p => p.1 + p.2 = k

end PositivityTheory.Rg.BcB.F.RS
