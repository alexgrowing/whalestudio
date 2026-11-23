import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LatticeEmbeddingTraceForm
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
theorem _root_.GlobalTheory.T.lattice_embedding_trace_form : PartI → N1ab → N1c → ThetaUnifAV → Out.Laws → Out.Laws2 → GlobalTheory.Published.HasseNormSt → ∀ (D : D7) (Q : Par D), Q.Pins → (∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q) → ∀ (j : ℕ) (hj : InR D j) (σ : Q.c.F →+* ℂ), GoodEmb Q.c σ → ∀ io : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin (D.sp.W j).rank → D.host.E), LatEmb (D.sp.W j) io → (∀ x y, (((Q.Dw j).EF x y : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-(-D.host.xi0) * herm (gmW (D.sp.W j) (D.sp.W_rank j hj.1 hj.2)) (io x ∘ Fin.cast (D.sp.W_rank j hj.1 hj.2).symm) (io y ∘ Fin.cast (D.sp.W_rank j hj.1 hj.2).symm))) → ∀ Kf : Subgroup (GA D (D.sp.W j)), IsLevelK (D.sp.W j) (D.host.g 0 * D.host.g 1) Kf → ∃ (U : Unf (Q.Xo j) Q.c σ D.R.r) (dict : GA D (D.sp.W j) → Σ k, Frame (U.X k).Ψ D.R.r) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsUnf U ∧ (∀ k la γ, (U.X k).χ la γ = 1) ∧ (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif (D.sp.W j) dict Kf th (D.sp.W_rank j hj.1 hj.2) ∧ (∀ g τ i, ‖dmin (U.X (dict g).1).Gm (dict g).2 τ i‖ = 1) ∧ (∀ g₀ : GA D (D.sp.W j), ∃ N ∈ 𝓝 g₀, ∃ (k : _) (x : GA D (D.sp.W j) → Frame (U.X k).Ψ _), ContinuousOn x N ∧ ∀ g ∈ N, x g ∈ (U.X k).dom ∧ ∃ γ ∈ (U.X k).Γ, dict g = ⟨k, lact γ (x g)⟩) ∧ (∀ k, ModelW (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) (U.X k) ∧ IsOrthogonalFrame (U.X k) x₀) ∧ FJ.LatZ U.X (WeightFamilies.rho D j) ∧ FJ.CuNeF U.X (WeightFamilies.rho D j) ∧ FJ.ExpoMatch U.X 1 (WeightFamilies.rho D j) (D.host.g 0 * D.host.g 1) ∧ ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin ((Q.Dw j).mult τ)) (F : FamilyUnif (Q.Xo j) (σ.comp (IntermediateField.inclusion Q.c.le).toRingHom) (fun i => relab Q.c σ (e i).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ), DictLat U (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) dict io e F ik φ th x₀ := by
  first | exact @GlobalTheory.RecPkg.exists_package | exact GlobalTheory.RecPkg.exists_package | (intros; apply GlobalTheory.RecPkg.exists_package <;> assumption)
