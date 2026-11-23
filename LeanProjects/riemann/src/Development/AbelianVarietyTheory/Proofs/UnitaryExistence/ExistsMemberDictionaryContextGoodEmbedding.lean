import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFlagDomainModelsOfFamilyUniformisation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLaws
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGram
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RealAdelesCmFieldEquivComplexCmType
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletion

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem hostCMType_neg_constant_im_neg (D : D7) (τ : D.host.E →+* ℂ)
    (hτ : τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD) : (τ (-D.host.xi0)).im < 0 := by
  have h1 := xi0_embedding_im_pos D τ ((mem_cm_type_iff D τ).2 hτ)
  have hφ : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  have hpos : 0 < (D.host.φ₀ D.host.sqrtMinusD).im := by
    rw [hφ]
    have hd : (0 : ℝ) < D.host.d := by exact_mod_cast d_pos D
    simpa using hd
  rw [if_pos hpos, Int.cast_one, _root_.one_mul] at h1
  rw [map_neg, Complex.neg_im]
  linarith

theorem exists_family_models (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (hι : IotaOK Dw V ι) (hpos : 1 ≤ Dw.p + Dw.q)
    (hσ : GoodEmb c σ) :
    ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
      (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
      (M : GlobalTheory.FrameUnif.ModelsOf F V.rank), GlobalTheory.FrameUnif.ModelBase M ∧ ∀ k, ModelW V rfl (M.X k) := by
  classical
  let e := (Fintype.equivFin (Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))).symm
  have hty := (GlobalTheory.Relab.relab_good D.host.E H l c σ hσ).2.2.2 Dw _ e
  obtain ⟨F⟩ := GlobalTheory.closing_of_abelianSchemeLaws D.host.E H Dw l Xo
    (σ.comp (IntermediateField.inclusion c.le).toRingHom) _ (fun j => relab c σ (e j).1) hpos hσ hty
  obtain ⟨-, -, -, -, -, hcF, -, hherm, hdet, hhT, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have hξ : cc (-D.host.xi0) = -(-D.host.xi0) := by rw [cc, map_neg, conj_xi0_alt]
  have hsp : Submodule.span D.host.E (Set.range ι) = ⊤ := by
    rw [← LinearMap.coe_range, hι.emb.2]
    exact (GlobalTheory.Member.latG_lattice_and_completion D V 1).2.1
  have hG : ∀ a b, cc ((-V.gramᵀ) a b) = (-V.gramᵀ) b a := fun a b => by
    rw [Matrix.neg_apply, Matrix.neg_apply, cc, map_neg, ← hherm a b, hcF, cc]
  have hd : (-V.gramᵀ).det ≠ 0 := by
    rw [Matrix.det_neg]
    exact mul_ne_zero (pow_ne_zero _ (by simp)) hdet
  have hEF : ∀ x y, ((Dw.EF x y : ℤ) : ℚ) =
      Algebra.trace ℚ D.host.E (-(-D.host.xi0) * herm (-V.gramᵀ) (ι x) (ι y)) := fun x y => by
    have h1 : Dw.EF x y = -Dw.EF y x := by
      have h := Dw.alt (x + y)
      simp only [map_add, LinearMap.add_apply, Dw.alt] at h
      linarith
    rw [h1, Int.cast_neg, hι.isom y x, hhT, ← map_neg]
    congr 1
    ring
  obtain ⟨M, hM, -, hMG⟩ := GlobalTheory.ModelsExist.exists_modelsOf GlobalTheory.QNorm.hasseNormSt D.host.E H Dw l Xo _ _ _ F
    V.rank (-D.host.xi0) (-V.gramᵀ) ι hξ
    (fun τ hτ => hostCMType_neg_constant_im_neg D τ (by rw [← hι.rt0, ← hι.rt, hτ])) ⟨hι.emb.1, hsp, hG, hd, hEF⟩
  exact ⟨_, e, F, M, hM, fun k => ⟨(hMG k).1, (hMG k).2⟩⟩

theorem exists_ctx : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (hr : V.rank = r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), IotaOK Dw V ι → 1 ≤ Dw.p + Dw.q → l.A = 1 → GoodEmb c σ → (∃ C : Ctx Xo c σ V r, C.OK ∧ C.ι = ι) ∧ (∀ C : Ctx Xo c σ V r, C.OK → GlobalTheory.FrameUnif.NegXi C.M) ∧ ∀ x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ, (∀ τ : D.host.E →+* ℂ, τ (H.rt : D.host.E) = H.rt0 → gram τ (-(Matrix.reindex (finCongr hr) (finCongr hr) V.gram)ᵀ) (x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn Dw.q (a : ℕ) : ℝ) : ℂ)) → ∃ C : Ctx Xo c σ V r, C.OK ∧ C.ι = ι ∧ C.x₀ = x₀ := by
  intro D H Dw l Xo c σ V r hr ι hι hpos hA hσ
  subst hr
  obtain ⟨g, e, F, M, hM, hW⟩ := exists_family_models D H Dw l Xo c σ V ι hι hpos hσ
  obtain ⟨θ, hθ⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  have key : ∀ x₀ : (D.host.E →+* ℂ) → Matrix (Fin V.rank) (Fin V.rank) ℂ,
      (∀ τ : D.host.E →+* ℂ, τ (H.rt : D.host.E) = H.rt0 →
        gram τ (-(Matrix.reindex (finCongr rfl) (finCongr rfl) V.gram)ᵀ) (x₀ τ) =
          Matrix.diagonal fun a : Fin V.rank => ((sgn Dw.q (a : ℕ) : ℝ) : ℂ)) →
      ∃ C : Ctx Xo c σ V V.rank, C.OK ∧ C.ι = ι ∧ C.x₀ = x₀ := fun x₀ hx =>
    ⟨⟨rfl, g, e, F, M, ι, θ, x₀⟩, ⟨hι, hpos, hA, hσ, hM, hW, hθ, fun k τ hτ => by
      show gram τ (M.X k).Gm (x₀ τ) = Matrix.diagonal fun a : Fin V.rank => ((sgn (M.X k).p0 (a : ℕ) : ℝ) : ℂ)
      rw [(hW k).1, (hM.type k).1]
      exact hx τ (((hM.type k).2 τ).1 hτ)⟩, rfl, rfl⟩
  refine ⟨?_, fun C hC k τ hτ => ?_, key⟩
  · classical
    let k : Fin F.n := ⟨0, F.n_pos⟩
    obtain ⟨C, hC, h, -⟩ := key
      (fun τ => if h : τ ∈ (M.X k).Ψ then ((M.X k).signature ⟨τ, h⟩).choose else 1) fun τ hτ => by
        have h := ((hM.type k).2 τ).2 hτ
        rw [dif_pos h, ← (hW k).1, ← (hM.type k).1]
        exact ((M.X k).signature ⟨τ, h⟩).choose_spec.2
    exact ⟨C, hC, h⟩
  · rw [(hC.modelW k).2]
    exact hostCMType_neg_constant_im_neg D τ (by rw [← hι.rt0, ← hι.rt, ((hC.base.type k).2 τ).1 hτ])

end GlobalTheory.Member
