import Formalism.LocalRingCardinality.KernelPlaceMeanBound

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.BasicNotions.DV NumberField

def logOmV (D : D7) (dl : ℝ) : ℝ := Real.eulerMascheroniConstant + Real.log (Real.pi / D.host.v) - dl

def LaV (D : D7) (sc : Scale) : ℝ := Real.log (sc.a * D.host.rdE)

def LprimeV (D : D7) (sc : Scale) : ℝ :=
  Real.log (sc.b * D.host.rdE * ((D.host.g 0 : ℝ) * D.host.g 1) * D.R.nV)

def kerPlaceV (D : D7) (dl : ℝ) (u : D.what₂.Word) (j : ℕ) (τ : D.what₂.Tau) : ℝ :=
  (∑ i ∈ Finset.range (D.R.N (j - 1)), phF (nuRow D u j τ i)) -
    (∑ i ∈ Finset.range (D.R.N (j - 1)), nuRow D u j τ i) * logOmV D dl

def SZbKV (D : D7) (sc : Scale) (dl C : ℝ) (u : D.what₂.Word) (j : ℕ) : ℝ :=
  (∑ ρ : D.what₂.Tau, kerPlaceV D dl u j ρ) +
    C * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * LaV D sc +
    C * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * (D.R.N D.R.m : ℝ) ^ 2 * sc.L

def InertJacobiLowerValue (D : D7) (sc : Scale) (C : ℝ) (j : ℕ) : ℝ :=
  (∑ ρ : D.what₂.Tau, logHook (D.R.sigW j).1 (aPlus D j ρ)) -
    C * (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * LprimeV D sc

def SZbPV (D : D7) (sc : Scale) (aT : D.host.TT → ℤ) (η Sc C : ℝ) (u : D.what₂.Word) : ℝ :=
  -(∑ t : D.host.TT, (aT t : ℝ) * Real.log ((D.mem u).A.T : ℝ)) +
    C * ((D.host.TT.card : ℝ) * sc.b' * (D.R.N D.R.m : ℝ) +
      (D.R.f : ℝ) * ((D.R.m : ℝ) * η + Sc) * (D.R.N D.R.m : ℝ) +
      (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2) * LaV D sc

def hVal (D : D7) (sc : Scale) (aT : D.host.TT → ℤ) (η Sc dl C : ℝ) (u : D.what₂.Word) : ℝ :=
  SZbPV D sc aT η Sc C u + (∑ j ∈ SizeData₂.lifts D, SZbKV D sc dl C u j) - ∑ j ∈ SizeData₂.lifts D, InertJacobiLowerValue D sc C j

theorem hExpl_eq (D : D7) (L : SizeData₂ D) (X : DivX D) (C : ℝ) (u : D.what₂.Word) (_h0 : D.what₂.Drows = 0)
    (hk : ∀ e, X.kapR e = 1) : hExpl6 D L X C u = hVal D L.sc L.aT L.etaSz L.Sc L.logDerivativeAtOne C u := by
  have h2 : meanE D (fun e => Real.log (X.kapR e)) = 0 := by
    unfold meanE
    simp [hk]
  unfold hExpl6
  rw [h2, sub_zero]
  rfl

theorem h_eq_of (D : D7) (L : SizeData₂ D) (X : DivX D) (C : ℝ) (h0 : D.what₂.Drows = 0) (hk : ∀ e, X.kapR e = 1)
    (hh : ∀ u, D.div.h u = hVal D L.sc L.aT L.etaSz L.Sc L.logDerivativeAtOne C u) :
    ∀ u, D.div.h u = hExpl6 D L X C u := fun u => (hh u).trans (hExpl_eq D L X C u h0 hk).symm

end Formalism.MainNotions.Inhab

end
