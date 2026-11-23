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
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelSubgroup
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryExistsWithPrescribedParts
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFinPartMat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecondStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReindexUnitary
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.MarkLocal

theorem markSpec_arch {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (D.host.E →+* ℂ)} {F : FamilyUnif Xo σ' ty} {r : ℕ}
    (M : GlobalTheory.FrameUnif.ModelsOf F r) (V : HSp D) (hr : V.rank = r)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (g₀ : GA D V) (p : Σ k, Frame (M.X k).Ψ r)
    (hp : MarkSpec M V hr io th x₀ g₀ p) :
    ∃ γ : GA D V, ∀ k ∈ GfC V, ∀ h ∈ GinfC V, MarkSpec M V hr io th x₀ (g₀ * h)
      ⟨p.1, fun τ => (Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th p.1 τ) (γ * (g₀ * k * h))) * x₀ τ.1 :
        Matrix (Fin r) (Fin r) ℂ)⟩ := by
  obtain ⟨γ, hγ, h1, h2, -⟩ := hp
  refine ⟨γ, fun k hk h hh => ?_⟩
  have hk' : infHom V k = 1 := hk
  have hh' : finHom V h = 1 := hh
  have ef : finHom V (γ * (g₀ * h)) = finHom V (γ * g₀) := by
    simp only [map_mul, hh', mul_one]
  have ei : infHom V (γ * (g₀ * k * h)) = infHom V (γ * (g₀ * h)) := by
    simp only [map_mul, hk', mul_one]
  have eg : gLat V (γ * (g₀ * h)) = gLat V (γ * g₀) := by
    unfold gLat
    rw [ef]
  have e1 : latG V (γ * (g₀ * h)) = latG V (γ * g₀) := by
    unfold latG
    rw [eg]
  have e2 : latGHat V (γ * (g₀ * h)) = latGHat V (γ * g₀) := by
    unfold latGHat
    rw [eg]
  refine ⟨γ, hγ, ?_, ?_, fun τ => ?_⟩
  · rw [e1]
    exact h1
  · rw [e2, ef]
    exact h2
  · unfold archM
    rw [← ei]
    rfl

set_option maxHeartbeats 1000000 in

theorem dict_locally_continuous : ThetaUnifAV → Out.Laws → ∀ (D : D7) (Q : Par D), Q.Pins → ∀ (j : ℕ) (hj : InR D j) (σ' : KA Q.l →+* ℂ) (g : ℕ) (ty : Fin g → (D.host.E →+* ℂ)) (F : FamilyUnif (Q.Xo j) σ' ty), σ' (baseKA Q.l).ρ = Q.H.rt0 → IsTypeFn Q.H (Q.Dw j).p (Q.Dw j).q ty → ∀ (M : GlobalTheory.FrameUnif.ModelsOf F D.R.r) (io : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin (D.sp.W j).rank → D.host.E)) (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ), RecOK M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ → ∀ dict : GA D (D.sp.W j) → Σ k, Frame (M.X k).Ψ D.R.r, (∀ h, MarkSpec M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ h (dict h)) → (∀ g₀ : GA D (D.sp.W j), ∃ N ∈ 𝓝 g₀, ∃ (k : _) (x : GA D (D.sp.W j) → Frame (M.X k).Ψ _), ContinuousOn x N ∧ ∀ g ∈ N, x g ∈ (M.X k).dom ∧ ∃ γ ∈ (M.X k).Γ, dict g = ⟨k, lact γ (x g)⟩) := by
  intro hT hL D Q hQ j hj σ' g ty F hσ hty M io th x₀ hrec dict hdict g₀
  obtain ⟨Kf, hK, -⟩ := GlobalTheory.RecDict.exists_isLevelK D (D.sp.W j) (D.host.g 0 * D.host.g 1)
  have hN := GlobalTheory.LevelOpen.level_mem_nhds D (D.sp.W j) _ Kf
    (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos) hK g₀
  obtain ⟨γ, hγ⟩ := markSpec_arch M _ _ io th x₀ g₀ _ (hdict g₀)
  have hc := ((GlobalTheory.UnitaryGlue.adelic_glue D (D.sp.W j)).2 _ (th (dict g₀).1) (M.X (dict g₀).1).cmType
    (hrec.2.2.2.2.1 _)).2.2.1
  refine ⟨_, hN, (dict g₀).1, fun u τ => (Matrix.reindex (finCongr (D.sp.W_rank j hj.1 hj.2))
    (finCongr (D.sp.W_rank j hj.1 hj.2)) (archM _ (th (dict g₀).1 τ) (γ * u)) * x₀ τ.1 :
      Matrix (Fin D.R.r) (Fin D.R.r) ℂ), ?_, ?_⟩
  · haveI : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
    haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
    haveI : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
      IsModuleTopology.isTopologicalRing (AF D.host.F) _
    haveI : IsTopologicalGroup (GA D (D.sp.W j)) :=
      inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig (D.sp.W j).gram))
    refine Continuous.continuousOn (continuous_pi fun τ => ?_)
    exact (((hc τ).comp (continuous_const.mul continuous_id)).matrix_reindex _ _).matrix_mul continuous_const
  · rintro _ ⟨k, hk, h, hh, rfl⟩
    have hkf := ((hK k).1 hk).1
    have hs := hγ k hkf h hh
    refine ⟨(GlobalTheory.MarkUnit.mark_frame_unit D Q hQ j hj σ' g ty F hσ hty M io th x₀ hrec _ _ hs).1, ?_⟩
    have e : g₀ * k * h = 1 * (g₀ * h) * k := by
      rw [one_mul, mul_assoc, mul_assoc, (GlobalTheory.UnitarySplit.real_finite_split D _).2.1 h hh k hkf]
    exact GlobalTheory.T.frame_uniform_embedding_second hT hL D Q hQ j hj σ' g ty F hσ hty M io th x₀ hrec Kf hK (g₀ * h) 1 k _ _ (one_mem _) hk hs
      (e ▸ hdict (g₀ * k * h))

end GlobalTheory.MarkLocal
