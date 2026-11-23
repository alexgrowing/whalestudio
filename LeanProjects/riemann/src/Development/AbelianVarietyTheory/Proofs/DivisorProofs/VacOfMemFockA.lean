import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedHermN
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ResAniso

variable {D : D7}

def vacOf (θ : InfFam D) (V : HSp D) (n : ℕ) (l : D.what₂.Tau → ℝ)
    (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (φ : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ) : Mx D V.rank n → ℂ :=
  fun x => StdUnn.gauss V l s (fun τ => compAt θ τ x) * φ (fun i j => finPart D (x i j))

end GlobalTheory.ResAniso
end
