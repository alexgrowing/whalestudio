import Formalism.PeriodIntegrals.SzCt

noncomputable section

namespace PI.SzCt.UnitaryGroupMassFormula

open Formalism.BasicNotions Formalism.MainNotions.G

def RowA : Prop :=
  ∀ (D : D7) (L : SizeData₂ D), ∀ j ∈ SizeData₂.lifts D, ∀ (u : D.what₂.Word) (τ : D.what₂.Tau),
    nuAbs D u j τ - (DV.nuRow D u j τ 0 - DV.nuRow D u j τ 1) ≤
      (D.R.k : ℝ) * (L.Sc + wj D j τ) + 2 * (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz

def RowB : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (_P : ParameterChoice' D L), ∀ j ∈ SizeData₂.lifts D, ∀ (u : D.what₂.Word) (τ : D.what₂.Tau),
    (D.eTau τ : D.R.GG) ∉ D.host.topPlaces →
    nuAbs D u j τ ≤ ((D.R.k : ℝ) + 2) * L.Sc + (D.R.k : ℝ) * wj D j τ +
      2 * (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz

def RowC : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (_P : ParameterChoice' D L), ∀ j ∈ SizeData₂.lifts D, ∀ (u : D.what₂.Word) (τ : D.what₂.Tau),
    (D.eTau τ : D.R.GG) ∉ D.host.topPlaces →
    DV.nuRow D u j τ 0 ≤ 3 * L.Sc + wj D j τ

def SizeFacts : Prop :=
  ∀ (D : D7) (L : SizeData₂ D), Formalism.MainNotions.SizesAt L → 3 ≤ L.sc.x →
    (∀ t : D.host.TT, (L.bT t : ℝ) ≤ 5 / 4 * L.sc.b') ∧
    L.etaSz ≤ L.sc.w'' D.R.n / L.sc.x ∧
    (D.R.k : ℝ) * L.Sc ≤ L.sc.w'' D.R.n ∧
    L.sc.w'' D.R.n ≤ L.sc.b' / L.sc.x ∧
    (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz ≤ L.sc.w'' D.R.n ∧
    1 ≤ L.sc.b ∧ 0 ≤ L.sc.b'

def PlaceFacts : Prop :=
  ∀ D : D7,
    (∀ t : HH D, (D.eTau (tauPl D (false, t)) : D.R.GG) = D.R.tau1 t) ∧
    (∀ t : HH D, t ∉ D.host.TT → D.host.IsThin (D.eTau (tauPl D (false, t)) : D.R.GG)) ∧
    (∀ t : HH D, (D.eTau (tauPl D (true, t)) : D.R.GG) ∉ D.host.topPlaces) ∧
    (∀ t : HH D, (D.eTau (tauPl D (true, t)) : D.R.GG) ∈ D.host.thickPlaces ∨
      D.host.IsThin (D.eTau (tauPl D (true, t)) : D.R.GG))

end PI.SzCt.UnitaryGroupMassFormula
