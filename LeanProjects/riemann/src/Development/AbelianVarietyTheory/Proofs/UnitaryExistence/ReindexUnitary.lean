import Mathlib
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
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitFrameEqOrthonormalMulTriangular
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.InfAdeleTensorBijective

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.MarkUnit

theorem infMat_unitary {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (τ : E →+* ℂ)
    (hτ : ∀ x, τ (σ x) = starRingEnd ℂ (τ x)) (θ : Ainf F ⊗[F] E →+* ℂ) (hθ : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ)
    (h : HA (AF F) σ J) :
    ((Formalism.MainNotions.StandardLattice.infMat σ J θ h).map (starRingEnd ℂ)).transpose * J.map τ * Formalism.MainNotions.StandardLattice.infMat σ J θ h =
      J.map τ := by
  let φ : AF F ⊗[F] E →+* ℂ :=
    θ.comp (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom
  have hφ : ∀ (a : AF F) (x : E), φ (a ⊗ₜ x) =
      GlobalTheory.InfAdeleCM.ext (τ.comp (algebraMap F E)) (fstA F a) * τ x := fun a x =>
    GlobalTheory.InfAdeleCM.hom_tmul τ θ hθ.1 hθ.2 (fstA F a) x
  have h1 : ∀ z, φ (sigR (AF F) σ z) = starRingEnd ℂ (φ z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      have : sigR (AF F) σ (a ⊗ₜ x) = a ⊗ₜ σ x := rfl
      rw [this, hφ, hφ, map_mul, GlobalTheory.InfAdeleCM.conj_ext, hτ]
    | add x y hx hy => simp only [map_add, hx, hy]
  have h2 : ∀ x, φ (inclR (AF F) x) = τ x := by
    intro x
    have : inclR (F := F) (AF F) x = (1 : AF F) ⊗ₜ x := rfl
    rw [this, hφ, map_one, map_one, one_mul]
  have hu : Formalism.UG.cT (sigR (AF F) σ) (HA.mat (AF F) σ J h).1 * JR (AF F) J * (HA.mat (AF F) σ J h).1 =
      JR (AF F) J := (show HR (AF F) σ J from h).2
  have hm : Formalism.MainNotions.StandardLattice.infMat σ J θ h = (HA.mat (AF F) σ J h).1.map φ := rfl
  have hJ : (JR (AF F) J).map φ = J.map τ := by
    ext a b
    exact h2 _
  have hc : (Formalism.UG.cT (sigR (AF F) σ) (HA.mat (AF F) σ J h).1).map φ =
      (((HA.mat (AF F) σ J h).1.map φ).map (starRingEnd ℂ)).transpose := by
    ext a b
    exact h1 _
  have := congrArg (fun m => Matrix.map m φ) hu
  simp only [Matrix.map_mul] at this
  rw [hJ, hc] at this
  rw [hm]
  exact this

theorem reindex_unitary {m n : ℕ} (e : Fin m ≃ Fin n) (J u : Matrix (Fin m) (Fin m) ℂ)
    (h : (u.map (starRingEnd ℂ)).transpose * J * u = J) :
    (Matrix.reindex e e u).transpose * (-(Matrix.reindex e e J).transpose) *
      (Matrix.reindex e e u).map (starRingEnd ℂ) = -(Matrix.reindex e e J).transpose := by
  have h' := congrArg (fun x => (Matrix.reindex e e x).transpose) h
  simp only [Matrix.reindex_apply, ← Matrix.submatrix_mul_equiv _ _ _ e.symm _, Matrix.transpose_mul] at h'
  simp only [Matrix.reindex_apply, Matrix.mul_neg, Matrix.neg_mul, neg_inj]
  rw [Matrix.mul_assoc]
  exact h'

set_option maxHeartbeats 1000000 in

theorem mark_frame_unit : ∀ (D : D7) (Q : Par D), Q.Pins → ∀ (j : ℕ) (hj : InR D j) (σ' : KA Q.l →+* ℂ) (g : ℕ) (ty : Fin g → (D.host.E →+* ℂ)) (F : FamilyUnif (Q.Xo j) σ' ty), σ' (baseKA Q.l).ρ = Q.H.rt0 → IsTypeFn Q.H (Q.Dw j).p (Q.Dw j).q ty → ∀ (M : GlobalTheory.FrameUnif.ModelsOf F D.R.r) (io : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin (D.sp.W j).rank → D.host.E)) (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ), RecOK M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ → ∀ (h : GA D (D.sp.W j)) (p : Σ k, Frame (M.X k).Ψ D.R.r), MarkSpec M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ h p → p.2 ∈ (M.X p.1).dom ∧ ∀ τ i, ‖dmin (M.X p.1).Gm p.2 τ i‖ = 1 := by
  intro D Q _ j hj σ' g ty F _ _ M io th x₀ hrec h p hp
  obtain ⟨γ, -, -, -, hfr⟩ := hp
  obtain ⟨-, hW, -, -, hth, hx⟩ := hrec
  obtain ⟨-, h2, h3⟩ := GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular D.host.E D.R.r (M.X p.1).p0
    (M.X p.1).Ψ (M.X p.1).Gm (M.X p.1).Gm_herm
  refine h2 p.2 fun τ => ?_
  rw [hfr τ, h3, hx p.1 τ.1 τ.2]
  haveI : IsTotallyReal D.host.F := by
    letI := D.host.cmStar
    exact D.sp.cm.totReal
  have hu := infMat_unitary D.sp.cm.sig (D.sp.W j).gram τ.1
    (fun x => IsCMField.complexEmbedding_complexConj D.host.E τ.1 x) (th p.1 τ) (hth p.1 τ) (γ * h)
  have hG : (M.X p.1).Gm.map τ.1 = -(Matrix.reindex (finCongr (D.sp.W_rank j hj.1 hj.2))
      (finCongr (D.sp.W_rank j hj.1 hj.2)) ((D.sp.W j).gram.map τ.1)).transpose := by
    rw [(hW p.1).1]
    ext a b
    simp
  rw [hG]
  exact reindex_unitary _ _ _ hu

end GlobalTheory.MarkUnit
