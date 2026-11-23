import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerLocalFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerArchimedeanStatement

noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem GlobalTheory.ThK.EvUniq.evZero_unique : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ r s r' s' i₀ i₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (M : Model σ X W)
    (M₁ : Model σ X W₁), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    M₁.IsGood B.ψ → ∀ e e' : Fn F n d →ₗ[ℂ] Fn F n d₁, IsEv B M M₁ 1 H'.ι (iso0 n H') e → IsEv B M M₁ 1 H'.ι (iso0 n H') e' →
      ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ ∈ PolData B M, e' Φ = c • e Φ := by
  intro hP F E _ _ _ _ _ σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M M₁ hB hX hW hM hH hM₁ e e' he he'
  obtain ⟨ei, ev, hei, hev, hloc⟩ := he.loc
  obtain ⟨ei', ev', hei', hev', hloc'⟩ := he'.loc
  have hfin : ∀ v, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ev' v φ = ev v φ := fun v φ hφ =>
    GlobalTheory.T.eigen_intertwiner_local_factor hP F E σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M M₁ hB hX hW hM hH hM₁ v (ev v) (ev' v)
      (GlobalTheory.T.finRel_local_factor_of_map_pure_eq_pure F E σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M M₁ hB hX hW hM hH hM₁ e he ei ev hei hev hloc v)
      (GlobalTheory.T.finRel_local_factor_of_map_pure_eq_pure F E σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M M₁ hB hX hW hM hH hM₁ e' he' ei' ev' hei' hev' hloc' v)
      (hev v).2 (hev' v).2 (hev v).1 (hev' v).1 φ hφ
  obtain ⟨c, hc⟩ := GlobalTheory.T.eigen_intertwiner_archimedean hP F E σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M M₁ hB hX hW hM hH hM₁ ei ei' hei
    (GlobalTheory.T.eigen_intertwiner_skew_plane_unique_dual F E σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M M₁ hB hX hW hM hH hM₁ e he ei ev hei hev hloc)
    (GlobalTheory.T.eigen_intertwiner_skew_plane_unique_dual F E σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M M₁ hB hX hW hM hH hM₁ e' he' ei' ev' hei' hev' hloc')
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hei' (by rw [hc, zero_smul])
  refine ⟨c, hc0, fun Φ hΦ => ?_⟩
  unfold PolData at hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, -, φ, hφ, hvac, rfl⟩ := hx
    rw [hloc' f φ hφ hvac, hloc f φ hφ hvac, hc]
    have hfe : (fun v => ev' v (φ v)) = fun v => ev v (φ v) := funext fun v => hfin v _ (hφ v)
    rw [hfe]
    funext x
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.smul_apply, smul_eq_mul, ContinuousLinearMap.smul_apply, SchwartzMap.smul_apply, mul_assoc]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, smul_add]
  | smul a x _ hx => rw [map_smul, map_smul, hx, smul_comm]
