import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingFifth
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.LocalToGlobal.ProjectiveLattices.ComponentWModel
import Formalism.LocalToGlobal.ProjectiveLattices.NormLaws
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_uniform_embedding_fifth : ThetaUnifAV → Out.Laws → ∀ (D : D7) (Q : Par D), Q.Pins → ∀ (j : ℕ) (hj : InR D j) (σ' : KA Q.l →+* ℂ) (g : ℕ) (ty : Fin g → (D.host.E →+* ℂ)) (F : FamilyUnif (Q.Xo j) σ' ty), σ' (baseKA Q.l).ρ = Q.H.rt0 → IsTypeFn Q.H (Q.Dw j).p (Q.Dw j).q ty → ∀ (M : GlobalTheory.FrameUnif.ModelsOf F D.R.r) (io : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin (D.sp.W j).rank → D.host.E)) (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ), RecOK M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ → ∀ dict : GA D (D.sp.W j) → Σ k, Frame (M.X k).Ψ D.R.r, (∀ h, MarkSpec M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ h (dict h)) → (∀ g₀ : GA D (D.sp.W j), ∃ N ∈ 𝓝 g₀, ∃ (k : _) (x : GA D (D.sp.W j) → Frame (M.X k).Ψ _), ContinuousOn x N ∧ ∀ g ∈ N, x g ∈ (M.X k).dom ∧ ∃ γ ∈ (M.X k).Γ, dict g = ⟨k, lact γ (x g)⟩) := by
  first | exact @GlobalTheory.MarkLocal.dict_locally_continuous | exact GlobalTheory.MarkLocal.dict_locally_continuous | (intros; apply GlobalTheory.MarkLocal.dict_locally_continuous <;> assumption)
