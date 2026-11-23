import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftRealLineDerivativeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialThetaKernelSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianTwistToHermitian

open scoped TensorProduct NNReal Matrix ContDiff
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThK.DiffSmooth

open GlobalTheory.ThK.SquareIntegrability GlobalTheory.SiegelSet

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sum_mem_polData {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (T : Finset (Pl F))
    {m : ℕ} (f : Fin m → SInf F (Fin n × Fin d)) (φ : Fin m → ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ)
    (h : ∀ i, f i ∈ M.Pol B.ψ B.emb ∧ (∀ v, φ i v ∈ SB _) ∧ ∀ v ∉ T, φ i v = M.vac v) :
    ∑ i, pure (f i) (φ i) ∈ PolData B M := by
  refine Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f i, (h i).1, φ i, (h i).2.1, ?_, rfl⟩
  refine Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => ?_)
  by_contra hT
  exact hv ((h i).2.2 v hT)

theorem isRealLine_rescale (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {c c' : E} (hc : c ≠ 0)
    (hc' : c' ≠ 0) {γ : ℝ → GAd σ (c • J.map σ)} (hγ : IsRealLine σ (c • J.map σ) γ) :
    IsRealLine σ (c' • J.map σ) fun t => toGAd hσ J hc' ((toGAd hσ J hc).symm (γ t)) := by
  obtain ⟨w, τ, Z, hZ, hy⟩ := hγ
  refine ⟨w, τ, Z, ?_, fun t => ?_⟩
  · have e : ∀ b : E, (b • J.map σ).map τ.1 = τ.1 b • (J.map σ).map τ.1 := fun b =>
      Matrix.ext fun i j => map_mul τ.1 b _
    have h0 : τ.1 c ≠ 0 := (map_ne_zero τ.1).2 hc
    rw [e, Matrix.mul_smul, Matrix.smul_mul, ← smul_add] at hZ ⊢
    rw [(smul_eq_zero.1 hZ).resolve_left h0, smul_zero]
  · obtain ⟨y, e1, e2⟩ := hy t
    have e3 : projArch σ _ w (γ t) = y := by rw [e1, projArch_embArch_self]
    have e4 : embArch σ _ w (projArch σ _ w (γ t)) = γ t := by rw [e3, e1]
    refine ⟨projArch σ _ w (toGAd hσ J hc' ((toGAd hσ J hc).symm (γ t))), ?_, ?_⟩
    · refine Subtype.ext ((congrArg Subtype.val e4).symm.trans ?_)
      exact Units.ext rfl
    · rw [← e2, ← e3]
      rfl

theorem contDiff_diff : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → G.q = 0 → 1 ≤ G.p →
    ∀ c : ℂ, ∀ Φ, ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ' →
    ∀ c₀ : E, c₀ ≠ 0 → ∀ φ' : GAd σ (c₀ • G.W.J.map σ) → ℂ,
      (∀ (g : UA σ G.W.J) (g' : GAd σ (c₀ • G.W.J.map σ)), g.1 = g'.1 → φ' g' = G.M.I om Φ g - c * G.M'.I om' Φ' g) →
      ∀ (k : ℕ) (γ : Fin k → ℝ → GAd σ (c₀ • G.W.J.map σ)), (∀ i, GlobalTheory.SiegelSet.IsRealLine σ (c₀ • G.W.J.map σ) (γ i)) → ∀ g,
        ContDiff ℝ ∞ fun t : Fin k → ℝ => φ' (g * (List.ofFn fun i => γ i (t i)).prod) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM _ _ c Φ Φ' hSo hPM c₀ hc₀ φ' hφ' k γ hγ g
  have hT := hM.triple
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hT.base.cm
  obtain ⟨x, hx⟩ := GlobalTheory.SkewToHerm.exists_sigma_ne σ hT.base.cm
  have hc₁ : x - σ x ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
  have hcc : σ (x - σ x) = -(x - σ x) := by rw [map_sub, hσ, neg_sub]
  obtain ⟨T, -, m, m', f, φ, f₁, φ₁, hf, hf₁, e, e', -⟩ := hPM
  have hP : Φ ∈ PolData B G.M := e ▸ sum_mem_polData G.M T f φ hf
  have hP' : Φ' ∈ PolData B G.M' := e' ▸ sum_mem_polData G.M' T f₁ φ₁ hf₁
  let e₀ := toGAd hσ G.W.J hc₀
  let e₁ := toGAd hσ G.W.J hc₁
  have hγ' : ∀ i, IsRealLine σ ((x - σ x) • G.W.J.map σ) fun t => e₁ (e₀.symm (γ i t)) := fun i =>
    isRealLine_rescale hσ G.W.J hc₀ hc₁ (hγ i)
  have h1 := GlobalTheory.T.theta_lift_real_line_derivative F E σ hσ B a a' G X om om' hKP hT _ hc₁ hcc Φ hP k _ hγ' (e₁ (e₀.symm g))
  have h2 := GlobalTheory.T.polynomial_theta_kernel_smooth F E σ hσ B a a' G X om om' hKP hT _ hc₁ hcc Φ' ⟨hP', hSo⟩ k _ hγ' (e₁ (e₀.symm g))
  have key : ∀ t : Fin k → ℝ, e₁.symm (e₁ (e₀.symm g) * (List.ofFn fun i => e₁ (e₀.symm (γ i (t i)))).prod) =
      e₀.symm (g * (List.ofFn fun i => γ i (t i)).prod) := fun t => by
    simp only [map_mul, map_list_prod, List.map_ofFn, MulEquiv.symm_apply_apply, Function.comp_def]
  have e2 : (fun t : Fin k → ℝ => φ' (g * (List.ofFn fun i => γ i (t i)).prod)) = fun t =>
      G.M.I om Φ (e₁.symm (e₁ (e₀.symm g) * (List.ofFn fun i => e₁ (e₀.symm (γ i (t i)))).prod)) -
        c * G.M'.I om' Φ' (e₁.symm (e₁ (e₀.symm g) * (List.ofFn fun i => e₁ (e₀.symm (γ i (t i)))).prod)) :=
    funext fun t => by rw [key]; exact hφ' _ _ rfl
  rw [e2]
  exact h1.sub (contDiff_const.mul h2)

end GlobalTheory.ThK.DiffSmooth
