import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.FinMatchDefs
import Development.AutomorphicArithmetic.LocalEmbeddings.ComplEquivEvW
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Geo piW chrW unifAt latAtV At SInf)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime IsSplitBasis)
open GlobalTheory.BotMatch (evW)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.StageGeo

variable {D : D7}

def AUnit {v : HeightOneSpectrum (𝓞 D.host.F)} (t : D.host.E →ₐ[D.host.F] Fv D.host.F v) : Prop :=
  (∃ a ∈ D.host.AA, Valued.v (t a) = 1) ∧ ∃ z ∈ D.host.AA⁻¹, Valued.v (t z) = 1

structure IsStageGeo (ψ : AddChar (AF D.host.F) ℂ) {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) (FA : Fr A) (FA' : Fr A')
    (FW : Fr WW) (hr : A.rank + A'.rank = WW.rank) (Bs : Base D.host.F D.host.E) (Γ : Geo D.sp.cm.sig A.rank A'.rank) : Prop where

  pairA : IsPair ψ true A WW (finCongr hr) Bs Γ.V Γ.W Γ.M

  pairB : IsPair ψ false A' WW (finCongr hr) Bs Γ.V' Γ.W Γ.M'

  latA : IsLat (finCongr hr) Γ.V Γ.W X.rA.Λ X.rW.Λ

  latB : IsLat (finCongr hr) Γ.V' Γ.W X.rA'.Λ X.rW.Λ

  cartA : IsCart true FA FW (finCongr hr) Bs Γ.V Γ.W

  cartB : IsCart false FA' FW (finCongr hr) Bs Γ.V' Γ.W

  JA : Γ.V.J = (1 : D.host.E) • A.gram

  JB : Γ.V'.J = (-1 : D.host.E) • A'.gram

  measA : Γ.M.μ = X.m.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU A 1 JA)

  domA : Γ.M.dom = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU A 1 JA '' X.fd

  measB : Γ.M'.μ = X.m'.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU A' (-1) JB)

  domB : Γ.M'.dom = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU A' (-1) JB '' X.fd'

  basA : ∀ v : Bs.P, ((Γ.V.bas v)⁻¹).1 = -(A.gram.map (Bs.τ v) * X.rA.β.1.map (evW (Bs.τ v)))ᵀ

  basB : ∀ v : Bs.P, ((Γ.V'.bas v)⁻¹).1 = (A'.gram.map (Bs.τ v) * X.rA'.β.1.map (evW (Bs.τ v)))ᵀ

  basW : ∀ v : Bs.P, AUnit (Bs.τ v) →
    (Γ.W.bas v).1 = (X.rW.β.1.map (evW (Bs.τ v))).submatrix (finCongr hr) (finCongr hr)

end GlobalTheory.StageGeo

end
