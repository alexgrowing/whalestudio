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
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFlagDomainModelsOfFamilyUniformisation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelGoodAndSign
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NegIndexTransposeOfHasSignature

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

noncomputable section

namespace GlobalTheory.RecModel

theorem exists_isInfEmb (D : D7) (τ : D.host.E →+* ℂ) :
    ∃ θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ, Formalism.MainNotions.StandardLattice.IsInfEmb τ θ := by
  have := D.sp.cm.totReal
  set φ : D.host.F →+* ℂ := τ.comp (algebraMap D.host.F D.host.E) with hφ
  set w : InfinitePlace D.host.F := InfinitePlace.mk φ
  have hw : w.embedding = φ :=
    InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal φ)
  let _ : Algebra D.host.F ℂ := φ.toAlgebra
  let f : Ainf D.host.F →ₐ[D.host.F] ℂ :=
    { toRingHom := (InfinitePlace.Completion.extensionEmbedding w).comp (Pi.evalRingHom _ w)
      commutes' := fun x => by
        show InfinitePlace.Completion.extensionEmbedding w (algebraMap D.host.F (Ainf D.host.F) x w) = φ x
        rw [InfiniteAdeleRing.algebraMap_apply, ← hw]
        exact InfinitePlace.Completion.extensionEmbedding_coe w _ }
  let g : D.host.E →ₐ[D.host.F] ℂ := { toRingHom := τ, commutes' := fun _ => rfl }
  refine ⟨(Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom, fun x => ?_, ?_⟩
  · show f 1 * g x = τ x
    rw [map_one, one_mul]
    rfl
  · have : (fun a : Ainf D.host.F => (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom
        (a ⊗ₜ[D.host.F] (1 : D.host.E))) = fun a => InfinitePlace.Completion.extensionEmbedding w (a w) := by
      funext a
      show f a * g 1 = _
      rw [map_one, mul_one]
      rfl
    rw [this]
    exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)

theorem exists_x0Orth {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) :
    ∃ x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ, ∀ Y : Data E r,
      (∀ τ, τ ∈ Y.Ψ → τ ∈ X.Ψ) → X.Gm = Y.Gm → X.p0 = Y.p0 → IsOrthogonalFrame Y x₀ := by
  classical
  refine ⟨fun τ => if h : τ ∈ X.Ψ then (X.signature ⟨τ, h⟩).choose else 1, fun Y hΨ hG hp τ hτ => ?_⟩
  rw [← hG, ← hp]
  have hτ' := hΨ τ hτ
  simp only [dif_pos hτ']
  exact (X.signature ⟨τ, hτ'⟩).choose_spec.2

theorem exists_recOK : GlobalTheory.Published.HasseNormSt → ∀ (D : D7) (Q : Par D), Q.Pins → ∀ (j : ℕ) (hj : InR D j) (σ' : KA Q.l →+* ℂ) (g : ℕ) (ty : Fin g → (D.host.E →+* ℂ)) (F : FamilyUnif (Q.Xo j) σ' ty), σ' (baseKA Q.l).ρ = Q.H.rt0 → IsTypeFn Q.H (Q.Dw j).p (Q.Dw j).q ty → ∃ (M : GlobalTheory.FrameUnif.ModelsOf F D.R.r) (io : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin (D.sp.W j).rank → D.host.E)) (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ), RecOK M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ ∧ GlobalTheory.FrameUnif.NegXi M ∧ ∀ io' : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin (D.sp.W j).rank → D.host.E), LatEmb (D.sp.W j) io' → (∀ x y, (((Q.Dw j).EF x y : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-(-D.host.xi0) * herm (gmW (D.sp.W j) (D.sp.W_rank j hj.1 hj.2)) (io' x ∘ Fin.cast (D.sp.W_rank j hj.1 hj.2).symm) (io' y ∘ Fin.cast (D.sp.W_rank j hj.1 hj.2).symm))) → RecOK M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io' th x₀ := by
  intro hH D Q hQ j hj σ' g ty F _ _
  have hr := D.sp.W_rank j hj.1 hj.2
  obtain ⟨io, hemb, -, hcc, hdet, hspan, hform⟩ := exists_latEmb_sign_one D Q hQ j hj
  let c : (Fin (D.sp.W j).rank → D.host.E) ≃ₗ[D.host.E] (Fin D.R.r → D.host.E) :=
    LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr hr.symm)
  let ψ : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E) :=
    (c.restrictScalars (𝓞 D.host.E)).toLinearMap ∘ₗ io
  have hξ : cc (-D.host.xi0) = -(-D.host.xi0) := by
    rw [cc, map_neg, conj_xi0_alt]
  have hsp : Submodule.span D.host.E (Set.range ψ) = ⊤ := by
    have : Set.range ψ = c.toLinearMap '' Set.range io := by
      rw [← Set.range_comp]
      rfl
    rw [this, Submodule.span_image, hspan, Submodule.map_top, LinearEquiv.range]
  obtain ⟨M, hB, hN, hM⟩ := GlobalTheory.ModelsExist.exists_modelsOf hH D.host.E Q.H (Q.Dw j) Q.l (Q.Xo j) σ' g ty F D.R.r
    (-D.host.xi0) (gmW (D.sp.W j) hr) ψ hξ (level_good_and_sign D Q hQ).2.2
    ⟨c.injective.comp hemb.1, hsp, hcc, hdet, hform⟩
  choose θ hθ using exists_isInfEmb D
  obtain ⟨x₀, hx₀⟩ := exists_x0Orth (M.X ⟨0, F.n_pos⟩)
  have hx : ∀ k, IsOrthogonalFrame (M.X k) x₀ := fun k =>
    hx₀ _ (fun τ hτ => ((hB.type _).2 τ).2 (((hB.type k).2 τ).1 hτ)) ((hM _).1.trans (hM k).1.symm)
      ((hB.type _).1.trans (hB.type k).1.symm)
  exact ⟨M, io, fun _ τ => θ τ.1, x₀, ⟨hB, hM, hemb, hform, fun _ τ => hθ τ.1, hx⟩, hN,
    fun io' h1 h2 => ⟨hB, hM, h1, h2, fun _ τ => hθ τ.1, hx⟩⟩

end GlobalTheory.RecModel
