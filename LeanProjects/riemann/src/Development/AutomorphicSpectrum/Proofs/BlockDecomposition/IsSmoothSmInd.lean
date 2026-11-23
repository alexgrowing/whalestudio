import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto

open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZFun

variable {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]

theorem isSmooth_smInd (H : Subgroup G) (σ : Representation ℂ H W) : IsSmooth (smInd H σ) := by
  intro f
  have e : {g : G | smInd H σ g f = f} = {g : G | ind H σ g f.1 = f.1} := by
    ext g
    exact Subtype.ext_iff
  rw [e]
  exact f.2

theorem isSmooth_cInd (H : Subgroup G) (σ : Representation ℂ H W) : IsSmooth (cInd H σ) := by
  intro f
  have e : {g : G | cInd H σ g f = f} = {g : G | smInd H σ g f.1 = f.1} := by
    ext g
    exact Subtype.ext_iff
  rw [e]
  exact isSmooth_smInd H σ f.1

end GlobalTheory.CompanionTheory.BZFun
