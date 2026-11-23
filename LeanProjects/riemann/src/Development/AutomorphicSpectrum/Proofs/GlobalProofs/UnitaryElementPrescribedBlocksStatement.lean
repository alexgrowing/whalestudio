import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.UnitaryElementPrescribedBlocks
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsAdaptedEmpty
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LanglandsDecompositionUnipotentLevi
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.RealPtExHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_unitary_element_lift : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) {m : ℕ}
    (X : Matrix (Fin V.rank) (Fin m) D.host.E) (u : D.what₂.Tau → Matrix (Fin m) (Fin V.rank) ℂ)
    (w : D.what₂.Tau → Matrix (Fin V.rank) (Fin m) ℂ),
    (∀ τ, 1 + X.map (tauE D τ) * u τ + w τ * (X.map (tauE D τ))ᴴ * gramAt D V τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) →
    ∃ g : GA D V, (∀ τ, infMat D.sp.cm.sig V.gram (θ τ) g = 1 + X.map (tauE D τ) * u τ + w τ * (X.map (tauE D τ))ᴴ * gramAt D V τ) ∧
      ∃ (U : Matrix (Fin m) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E))
        (W : Matrix (Fin V.rank) (Fin m) (AF D.host.F ⊗[D.host.F] D.host.E)),
        (∀ i v, (∀ τ, u τ i v = 0) → U i v = 0) ∧ (∀ v i, (∀ τ, w τ v i = 0) → W v i = 0) ∧
        (∀ i j, (∀ τ, (u τ * X.map (tauE D τ)) i j = 0) → (HMul.hMul U (GlobalTheory.SiegelSet.adMat D.host.F X) : Matrix (Fin m) (Fin m) (AF D.host.F ⊗[D.host.F] D.host.E)) i j = 0) ∧
        (matHom V g).1 = 1 + (HMul.hMul (GlobalTheory.SiegelSet.adMat D.host.F X) U : Matrix (Fin V.rank) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) +
          (HMul.hMul W (GlobalTheory.SiegelSet.adMat D.host.F (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram)) : Matrix (Fin V.rank) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.exists_adelic_of_real_comps | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.exists_adelic_of_real_comps | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.exists_adelic_of_real_comps <;> assumption)
