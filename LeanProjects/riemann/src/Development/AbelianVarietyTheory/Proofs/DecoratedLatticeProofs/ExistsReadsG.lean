import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopLevExists
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsMemMultT
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OnFrameOfSignature
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultValueLeftContLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepMemSm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.Onto

open GlobalTheory.Mem.ColAd GlobalTheory.Core.Rk.Top GlobalTheory.Core.Rk.TopLift

section Fock

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {Pm : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  {K : ClassesAtPrimes M bad} {okW : D.what₂.places.Pl → Prop}

def bf (V : ValuationAtPrimes K okW) (c : M.clsP) : (FrP D → ℂ) →ₗ⋆[ℂ] (FrP D → ℂ) →ₗ[ℂ] ℂ :=
  ((Nat.card (M.stabilizer₂ c) : ℂ)) •
    ((M.ipP.comp (V.eW.symm.toLinearMap ∘ₗ LinearMap.single ℂ (fun _ => FrP D → ℂ) c)).compl₂
      (V.eW.symm.toLinearMap ∘ₗ LinearMap.single ℂ (fun _ => FrP D → ℂ) c))

end Fock

section Points

variable {D : D7} (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n)

variable {V} {S : D.what₂.Tau → SPar} {MX : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ}

end Points

section Move

variable {D : D7} {u : D.what₂.Word} {θ : InfFam D} {S : D.what₂.Tau → SPar} {MX : DSModel D.sp.X' S}
  {j : SmT MX →ₗ[ℂ] (FrP D → ℂ)} {J : Set (GA D D.sp.X')} {χ : GA D D.sp.X' → ℂ} {f : SmT MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)}

end Move

end GlobalTheory.Fam.Onto

end
