import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegFamConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelEisensteinDoubled
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelWeilAnisotropicHermitian
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling

namespace GlobalTheory.ChiDetFun

theorem chiDet_props : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (W : Spc F E n)
    (χ : Chr F E), IsHecke F E χ →
    Continuous (fun h : UA σ W.J => (((χ (Matrix.GeneralLinearGroup.det h.1))⁻¹ : Circle) : ℂ)) ∧
    (∀ h : UA σ W.J, ‖(((χ (Matrix.GeneralLinearGroup.det h.1))⁻¹ : Circle) : ℂ)‖ = 1) ∧
    ∀ γ ∈ ratU σ W.J, ∀ h : UA σ W.J, (((χ (Matrix.GeneralLinearGroup.det (γ * h).1))⁻¹ : Circle) : ℂ) =
      (((χ (Matrix.GeneralLinearGroup.det h.1))⁻¹ : Circle) : ℂ) := by
  intro F E _ _ _ _ _ σ n W χ hχ
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  refine ⟨?_, ?_, ?_⟩
  · have hdet : Continuous (fun h : UA σ W.J => Matrix.GeneralLinearGroup.det h.1) := by
      rw [Units.continuous_iff]
      constructor
      · show Continuous fun h : UA σ W.J => ((h.1 : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)).det
        exact (Units.continuous_val.comp continuous_subtype_val).matrix_det
      · show Continuous fun h : UA σ W.J => (((h.1 : GL (Fin n) (AE F E))⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)).det
        exact (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_det
    have hinv : Continuous fun z : Circle => (((z⁻¹ : Circle)) : ℂ) := by
      have : (fun z : Circle => (((z⁻¹ : Circle)) : ℂ)) = fun z : Circle => ((z : ℂ))⁻¹ := by
        funext z; exact Circle.coe_inv z
      rw [this]
      exact Continuous.inv₀ continuous_subtype_val (fun z => Circle.coe_ne_zero z)
    exact hinv.comp (hχ.1.comp hdet)
  · intro h
    exact Circle.norm_coe _
  · intro γ hγ h
    unfold ratU at hγ
    rw [Subgroup.mem_subgroupOf] at hγ
    obtain ⟨g, hg⟩ := hγ
    have h1 : Matrix.GeneralLinearGroup.det (γ * h).1 =
        Matrix.GeneralLinearGroup.det (γ : GL (Fin n) (AE F E)) * Matrix.GeneralLinearGroup.det h.1 := by
      rw [Subgroup.coe_mul, map_mul]
    have h2 : Matrix.GeneralLinearGroup.det (γ : GL (Fin n) (AE F E)) =
        Units.map (inclR (AF F) : E →+* AE F E).toMonoidHom (Matrix.GeneralLinearGroup.det g) := by
      rw [← hg]
      ext
      simp [Matrix.GeneralLinearGroup.map, RingHom.map_det]
    rw [h1, map_mul, h2, hχ.2, one_mul]

end GlobalTheory.ChiDetFun
