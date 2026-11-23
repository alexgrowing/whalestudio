import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemUnipSymBc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.GroupLoc

variable {D : D7}

def ModW (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (S : Set (VA X.B.I)) (y : VA X.B.I) : Prop :=
  y ∈ Submodule.span (Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) S ⊔ wLf X w

def CondAt (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (x : X.B.I.Gf) : Prop :=
  (∀ a : Fin D.R.rS, ModW X w (X.e0 '' {b | b.1 < a.1}) ((X.B.I.fmat x - 1) *ᵥ X.e0 a)) ∧
    ModW X w (Set.range X.e0) ((X.B.I.fmat x - 1) *ᵥ X.z0) ∧
    ∀ i : Fin D.R.k, ModW X w (Set.range X.e0 ∪ X.bw '' {j | j.1 < i.1}) ((X.B.I.fmat x - 1) *ᵥ X.bw i)

def symAllowed (ρ k : ℕ) {r : ℕ} (i j : Fin r) : Prop :=
  j.1 < i.1 ∧ ¬ (ρ ≤ j.1 ∧ j.1 < ρ + k ∧ i.1 = ρ + k)

def ColCond (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (x : X.B.I.Gf) : Prop :=
  ∀ i : Fin D.R.r, ModW X w (GlobalTheory.Mem.SymFrame.symVec X w '' {j | symAllowed D.R.rS D.R.k i j})
    ((X.B.I.fmat x - 1) *ᵥ GlobalTheory.Mem.SymFrame.symVec X w i)

end GlobalTheory.Mem.GroupLoc

end
