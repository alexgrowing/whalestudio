import Formalism.SharpRestriction.CuspSpanNormBounds.DMiMulVecApply

open MeasureTheory Matrix Finset

noncomputable section

namespace Formalism.MainNotions.FrameBoundFromBesselTorus

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

variable {k r : ℕ}

def trD (L : LocBessel k r) (κ τ : ℝ) (κN₁ : ENNReal)
    (hz : inWb k r ((τ : ℂ) • L.z) ∧ 0 < Tz k r ((τ : ℂ) • L.z))
    (hz' : inWb k r ((τ : ℂ) • L.z') ∧ 0 < Tz k r ((τ : ℂ) • L.z'))
    (hπ : IsHCTypeW k r ((τ : ℂ) • L.z) L.u (fun x => L.π (cjI k r κ τ x)))
    (hπ' : IsHCTypeW k r ((τ : ℂ) • L.z') L.u' (fun x => L.π' (cjI k r κ τ x)))
    (hμW : IsHaarOn (UWset k r ((τ : ℂ) • L.z)) (L.μW.map (cjT k r κ τ)) ∧ L.μW.map (cjT k r κ τ) Set.univ = 1)
    (hμW' : IsHaarOn (UWset k r ((τ : ℂ) • L.z')) (L.μW'.map (cjT k r κ τ)) ∧
      L.μW'.map (cjT k r κ τ) Set.univ = 1) : LocBessel k r where
  ε := L.ε
  lam := L.lam
  hlam := L.hlam
  z := (τ : ℂ) • L.z
  z' := (τ : ℂ) • L.z'
  hz := hz
  hz' := hz'
  u := L.u
  u' := L.u'
  Hs := L.Hs
  σ := L.σ
  hσ := L.hσ
  Wp := L.Wp
  π := fun x => L.π (cjI k r κ τ x)
  hπ := hπ
  Wq := L.Wq
  π' := fun x => L.π' (cjI k r κ τ x)
  hπ' := hπ'
  c := (κ : ℂ) * L.c
  μW := L.μW.map (cjT k r κ τ)
  μW' := L.μW'.map (cjT k r κ τ)
  hμW := hμW
  hμW' := hμW'
  κN := κN₁

end Formalism.MainNotions.FrameBoundFromBesselTorus
