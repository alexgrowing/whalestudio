import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticModelRationalCoordinates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedFormEqAdelicThetaDistribution
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzThetaDistributionSumNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFunctionalArchimedeanFactorStatement
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section
namespace GlobalTheory.ThetaChange

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) → ∃ c₀ : ℂ, c₀ ≠ 0 ∧ ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (e Φ) = c₀ * thetaSum F Φ := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP M₁ hM₁ e hE hbij
  have hstd : IsStd B.ψ := hP.base.std
  have hrk : Module.finrank F E = 2 := hP.base.cm.2.2.1
  obtain ⟨Φr, hΦr⟩ := GlobalTheory.RatCoord.ratEquiv F E σ n d X W M B.ψ hP.good hrk
  obtain ⟨lθ, hlθ, hlθ'⟩ := GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F (Fin n × Fin d)
  have hcomp := GlobalTheory.EvAdm.comp_mem_adm F E σ B n d n d X W X W M M₁ 1 1 ∅ e hP.good hM₁ hE lθ hlθ
  have hinc1 : ∀ k : ℕ, incM F (1 : Matrix (Fin k) (Fin k) E) = 1 := by
    intro k; unfold incM; exact Matrix.map_one _ (map_zero _) (map_one _)
  obtain ⟨c, hc⟩ := GlobalTheory.T.schwartz_functional_archimedean_factor F B.ψ hstd (Fin n × Fin d) (fun Φ => thetaSum F (e Φ))
    (fun Φ hΦ Ψ hΨ => by
      simp only [map_add]
      exact GlobalTheory.WeilM.thetaSum_add F (hE.maps Φ hΦ) (hE.maps Ψ hΨ))
    (fun c Φ _ => by simp only [map_smul]; exact GlobalTheory.WeilM.thetaSum_smul F c (e Φ))
    (fun g hg => by
      obtain ⟨T, hT⟩ := hcomp g hg
      refine ⟨T, fun f => ?_⟩
      have hm : pureA F f g ∈ schA F (Fin n × Fin d) := Submodule.subset_span ⟨f, g, hg, rfl⟩
      rw [← hlθ' _ (hE.maps _ hm)]
      exact hT f)
    (fun a b Φ hΦ => by
      set x := Φr.symm (a, b) with hx
      have hxe : M.co.e (incM F x) = ((fun i => algebraMap F (AF F) (a i)), (fun i => algebraMap F (AF F) (b i))) := by
        rw [hΦr x, hx, LinearEquiv.apply_symm_apply]
      have h1 : schr B.ψ ((fun i => algebraMap F (AF F) (a i)), (fun i => algebraMap F (AF F) (b i))) Φ =
          M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * incM F x * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) Φ := by
        rw [hinc1, hinc1, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one]
        show _ = schr B.ψ (M.co.e (incM F x)) Φ
        rw [hxe]
      rw [h1, hE.Heisenberg₂ _ Φ hΦ]
      obtain ⟨y, z, hyz⟩ := hM₁.rat x
      show thetaSum F (schr B.ψ (M₁.co.e (incM F x)) (e Φ)) = _
      rw [hyz]
      exact GlobalTheory.ThetaQuasiRat.thetaSum_schr_rat F B.ψ (fun a => hstd.2.1 a) y z (e Φ))
  refine ⟨c, ?_, hc⟩
  rintro rfl
  obtain ⟨φ₀, hφ₀, hne⟩ := GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero F (Fin n × Fin d)
  obtain ⟨Φ, hΦ, rfl⟩ := hbij.surjOn hφ₀
  exact hne (by rw [hc Φ hΦ, zero_mul])

end GlobalTheory.ThetaChange
