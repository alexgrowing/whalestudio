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
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointsAllNormalisationsFamilyUnif
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUniformisationIsComplexUniformisation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsInfEmb
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReindexUnitary
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LatCuspExpo
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingFirstStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingFourthStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingFifthStatement

noncomputable section

namespace GlobalTheory.RecPkg

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

set_option maxHeartbeats 1000000 in

theorem exists_package : PartI → N1ab → N1c → ThetaUnifAV → Out.Laws → Out.Laws2 → GlobalTheory.Published.HasseNormSt → ∀ (D : D7) (Q : Par D), Q.Pins → (∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q) → ∀ (j : ℕ) (hj : InR D j) (σ : Q.c.F →+* ℂ), GoodEmb Q.c σ → ∀ io : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin (D.sp.W j).rank → D.host.E), LatEmb (D.sp.W j) io → (∀ x y, (((Q.Dw j).EF x y : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-(-D.host.xi0) * herm (gmW (D.sp.W j) (D.sp.W_rank j hj.1 hj.2)) (io x ∘ Fin.cast (D.sp.W_rank j hj.1 hj.2).symm) (io y ∘ Fin.cast (D.sp.W_rank j hj.1 hj.2).symm))) → ∀ Kf : Subgroup (GA D (D.sp.W j)), IsLevelK (D.sp.W j) (D.host.g 0 * D.host.g 1) Kf → ∃ (U : Unf (Q.Xo j) Q.c σ D.R.r) (dict : GA D (D.sp.W j) → Σ k, Frame (U.X k).Ψ D.R.r) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsUnf U ∧ (∀ k la γ, (U.X k).χ la γ = 1) ∧ (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif (D.sp.W j) dict Kf th (D.sp.W_rank j hj.1 hj.2) ∧ (∀ g τ i, ‖dmin (U.X (dict g).1).Gm (dict g).2 τ i‖ = 1) ∧ (∀ g₀ : GA D (D.sp.W j), ∃ N ∈ 𝓝 g₀, ∃ (k : _) (x : GA D (D.sp.W j) → Frame (U.X k).Ψ _), ContinuousOn x N ∧ ∀ g ∈ N, x g ∈ (U.X k).dom ∧ ∃ γ ∈ (U.X k).Γ, dict g = ⟨k, lact γ (x g)⟩) ∧ (∀ k, ModelW (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) (U.X k) ∧ IsOrthogonalFrame (U.X k) x₀) ∧ FJ.LatZ U.X (WeightFamilies.rho D j) ∧ FJ.CuNeF U.X (WeightFamilies.rho D j) ∧ FJ.ExpoMatch U.X 1 (WeightFamilies.rho D j) (D.host.g 0 * D.host.g 1) ∧ ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin ((Q.Dw j).mult τ)) (F : FamilyUnif (Q.Xo j) (σ.comp (IntermediateField.inclusion Q.c.le).toRingHom) (fun i => relab Q.c σ (e i).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ), DictLat U (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) dict io e F ik φ th x₀ := by
  intro _ _ hN hTh hL hL2 hH D Q hQ hpq j hj σ hσ io hio hEF Kf hKf
  classical
  let g := Fintype.card (Σ τ : D.host.E →+* ℂ, Fin ((Q.Dw j).mult τ))
  let e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin ((Q.Dw j).mult τ) := (Fintype.equivFin _).symm
  have hty := (GlobalTheory.Relab.relab_good _ Q.H Q.l Q.c σ hσ).2.2.2 (Q.Dw j) g e
  have hρ : (σ.comp (IntermediateField.inclusion Q.c.le).toRingHom) (baseKA Q.l).ρ = Q.H.rt0 := hσ
  obtain ⟨F⟩ := hN _ Q.H (Q.Dw j) Q.l (Q.Xo j) _ g _ (hpq j) hρ hty
  obtain ⟨M, -, th, x₀, -, hneg, hall⟩ := GlobalTheory.RecModel.exists_recOK hH D Q hQ j hj _ g _ F hρ hty
  have hR := hall io hio hEF
  obtain ⟨un, hun⟩ := GlobalTheory.FrameUnif.exists_framesOK hL.secBaseChange hL2.secTwist _ Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c σ g e
    F _ M hσ hR.1 hneg
  have hU := GlobalTheory.FrameUnif.isUnf_built hL.secBaseChange _ Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c σ g e F _ M un hσ hR.1 hneg hun
  have hG := GlobalTheory.T.exists_markSpec_of_recOK hH D Q hQ j hj _ g _ F hρ hty M io th x₀ hR
  have hex : ∀ h : GA D (D.sp.W j), ∃ p, MarkSpec M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ h p ∧
      ((∃ p, MarkSpec M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ h p ∧
        ∀ τ : (M.X p.1).Ψ, mat p.2 τ = x₀ τ.1) → ∀ τ : (M.X p.1).Ψ, mat p.2 τ = x₀ τ.1) := by
    intro h
    by_cases h' : ∃ p, MarkSpec M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ h p ∧
        ∀ τ : (M.X p.1).Ψ, mat p.2 τ = x₀ τ.1
    · obtain ⟨p, hp, hp'⟩ := h'
      exact ⟨p, hp, fun _ => hp'⟩
    · obtain ⟨p, hp⟩ := hG h
      exact ⟨p, hp, fun h'' => (h' h'').elim⟩
  choose dict hd hb using hex
  obtain ⟨c1, c2, c3⟩ := GlobalTheory.RecDict.lat_cusp_expo hH D Q hQ j hj _ g _ F hρ hty M io th x₀ hR
  refine ⟨(GlobalTheory.FrameUnif.unfOf e F M un).toPj, dict, x₀, th, hU, hR.1.chi, hR.2.2.2.2.1,
    GlobalTheory.T.frame_uniform_embedding_fourth hTh hL D Q hQ j hj _ g _ F hρ hty M io th x₀ hR Kf hKf dict hd hb,
    fun h => (GlobalTheory.MarkUnit.mark_frame_unit D Q hQ j hj _ g _ F hρ hty M io th x₀ hR h _ (hd h)).2,
    GlobalTheory.T.frame_uniform_embedding_fifth hTh hL D Q hQ j hj _ g _ F hρ hty M io th x₀ hR dict hd,
    fun k => ⟨hR.2.1 k, hR.2.2.2.2.2 k⟩, c1, c2, c3, g, e, F, id, M.φ, ⟨hR.1.ef, fun k x => ?_⟩, hd⟩
  obtain ⟨Pm, h1, h2, h3, h4, -⟩ := hun.1 k x
  exact ⟨Pm, h1, h2, h3, h4⟩

end GlobalTheory.RecPkg
