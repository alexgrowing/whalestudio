import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.StSmooth

noncomputable section

open MeasureTheory Matrix LineDeriv

namespace Ad3.LR

def eU (r : Fin 2) (c : Fin 3) : M23 := fun r' c' => if r' = r ∧ c' = c then 1 else 0

def pol (i j : Fin 3) (X : M23) : M23 := fun r c => if c = j then X r i else 0

def crd (r : Fin 2) (i : Fin 3) (X : M23) : ℂ := ((X r i : ℝ) : ℂ)

def Dc (i j : Fin 3) : Sw →L[ℂ] Sw :=
  (∑ r : Fin 2, (SchwartzMap.smulLeftCLM ℂ (crd r i)).comp (lineDerivOpCLM ℂ Sw (eU r j))) +
    if i = j then ContinuousLinearMap.id ℂ Sw else 0

def Dp (i j : Fin 3) : Module.End ℂ Sw := (Dc i j).toLinearMap

end Ad3.LR
