import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.WordDerivatives
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

namespace GlobalTheory.SmoothForms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def BddDen (V : HSp D) (d : ℕ) (g : GA D V) : Prop :=
  ∀ i j, d • finMat D.sp.cm.sig V.gram g i j ∈ intAE D ∧ d • finMat D.sp.cm.sig V.gram g⁻¹ i j ∈ intAE D

def DenomBound (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) : Prop :=
  ∃ (C : ℝ) (M : ℕ), ∀ g : GA D V, ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g : ℝ) ^ M ∧
    ∀ i : Fin V.rank, (Pi.single i (d : D.host.E) : Fin V.rank → D.host.E) ∈ Formalism.L2.Pj.latG V g

def RealPoints (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) : Prop :=
  (∀ τ, (gramAt D V τ)ᴴ = gramAt D V τ ∧ IsUnit (gramAt D V τ).det) ∧
  (∀ u : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, u τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) →
    ∃ g ∈ GinfC V, ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) g = u τ) ∧
  (∀ g ∈ GinfC V, ∀ g' ∈ GinfC V,
    (∀ τ, infMat D.sp.cm.sig V.gram (θ τ) g = infMat D.sp.cm.sig V.gram (θ τ) g') → g = g') ∧
  (∀ g g' τ, infMat D.sp.cm.sig V.gram (θ τ) (g * g') =
    infMat D.sp.cm.sig V.gram (θ τ) g * infMat D.sp.cm.sig V.gram (θ τ) g') ∧
  (∀ k ∈ GfC V, ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) k = 1) ∧
  (∀ a ∈ GinfC V, ∀ k ∈ GfC V, a * k = k * a) ∧
  (∀ g : GA D V, ∃ k ∈ GfC V, ∃ a ∈ GinfC V, g = k * a) ∧
  ∀ (g : GA D V), ∀ a ∈ GinfC V, finMat D.sp.cm.sig V.gram (g * a) = finMat D.sp.cm.sig V.gram g

end GlobalTheory.SmoothForms

end
