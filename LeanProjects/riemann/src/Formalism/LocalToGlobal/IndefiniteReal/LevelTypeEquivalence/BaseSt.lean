import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory NumberField Matrix
open scoped TensorProduct

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def InfFamExists : Prop :=
  ∃ θ : Datum.InfFam D, IsInfFam θ

def InfFamUnique : Prop :=
  ∀ θ θ' : Datum.InfFam D, IsInfFam θ → IsInfFam θ' → θ = θ'

def InfSplit : Prop :=
  ∀ θ : Datum.InfFam D, IsInfFam θ →
    ∃ e : (Ainf D.host.F ⊗[D.host.F] D.host.E) ≃+* (D.what₂.Tau → ℂ),
      Continuous e ∧ Continuous e.symm ∧ ∀ x τ, e x τ = θ τ x

def AtTauExUnique : Prop :=
  ∀ θ : Datum.InfFam D, IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ),
    gᴴ * gramAt D V τ * g = gramAt D V τ → ∃! h : GA D V, IsAtTau θ V τ g h

def AtTauUnitary : Prop :=
  ∀ θ : Datum.InfFam D, IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (h : GA D V),
    IsAtTau θ V τ g h → gᴴ * gramAt D V τ * g = gramAt D V τ

def AtTauHom : Prop :=
  ∀ θ : Datum.InfFam D, IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau),
    atTau θ V τ 1 = 1 ∧
    (∀ g g' : Matrix (Fin V.rank) (Fin V.rank) ℂ, gᴴ * gramAt D V τ * g = gramAt D V τ →
      g'ᴴ * gramAt D V τ * g' = gramAt D V τ → atTau θ V τ (g * g') = atTau θ V τ g * atTau θ V τ g') ∧
    ContinuousOn (atTau θ V τ) {g | gᴴ * gramAt D V τ * g = gramAt D V τ}

def GATop : Prop :=
  ∀ V : HSp D, IsTopologicalGroup (GA D V) ∧ LocallyCompactSpace (GA D V) ∧ T2Space (GA D V) ∧
    SecondCountableTopology (GA D V) ∧ BorelSpace (GA D V)

def GQDiscrete : Prop :=
  ∀ V : HSp D, DiscreteTopology (GQ V)

def FundDomExists : Prop :=
  ∀ V : HSp D, ∃ 𝓕 : Set (GA D V), MeasurableSet 𝓕 ∧ ∀ μ : Measure (GA D V), IsFundamentalDomain (GQ V) 𝓕 μ

def MinfExUnique : Prop :=
  ∀ p q : ℕ, ∃! m : Measure (UpqT p q), Lev.IsMinf m

variable {D}

def IsLevelA (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) : Prop :=
  IsCompact (Lev.levA V K : Set (GA D V)) ∧ IsOpen (((Lev.levA V K).subgroupOf (GfC V)) : Set (GfC V))

variable (D)

def MeasLevExists : Prop :=
  ∀ V : HSp D, V.SigOK → ∀ K : Subgroup (GL (Fin V.rank) (Lev.EAf D)), IsLevelA V K → ∃ μ, Lev.IsMeasLev V K μ

def MeasLevDefExists : Prop :=
  ∀ V : HSp D, V.SigOK → V.IsDefinite → ∀ K : Subgroup (GL (Fin V.rank) (Lev.EAf D)), IsLevelA V K →
    ∃ μ, Lev.IsMeasLevDef V K μ

def MeasFDExists : Prop :=
  ∀ V : HSp D, V.SigOK → ∀ K : Subgroup (GL (Fin V.rank) (Lev.EAf D)), IsLevelA V K →
    ∃ μ 𝓕, Lev.IsMeasFD V K μ 𝓕

end Formalism.IndefR.Eqv

end
