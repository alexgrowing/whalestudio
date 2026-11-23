import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegFamConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelEisensteinDoubled
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockDiagUnitaryHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiDetProps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHtLeTwoMulQht
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingSeesawPolynomialDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingGramLatticeThetaStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling

namespace GlobalTheory.CuspDbl

theorem anisoFamily : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s' r₁ s₁ : ℕ), IsPair B M χX χW om r s' r₁ s₁ → min r s' = 0 → 1 ≤ n → 1 ≤ d →
    ∀ Φ₁ ∈ PolData B M, ∀ Φ₂ ∈ PolData B M,
    ∀ μ : Measure (UA σ W.J), μ.IsHaarMeasure →
    ∃ (Ez : ℂ → UA σ W.J → UA σ W.J → ℂ) (φ : ℂ → UA σ W.J → ℂ) (s₀ κ : ℂ) (R₀ : ℝ), κ ≠ 0 ∧
      (∀ h h', GlobalTheory.ThKLiftCusp.kern M om Φ₁ Φ₂ h h' = κ * Ez s₀ h h') ∧
      GlobalTheory.CuspDbl.IsRegFam (fun h : UA σ W.J => (qht h : ℝ)) s₀ Ez ∧
      ∀ s : ℂ, R₀ < s.re → Integrable (φ s) μ ∧
        ∀ 𝓕 : Set (UA σ W.J), IsFundamentalDomain (ratU σ W.J) 𝓕 μ →
        ∀ f : UA σ W.J → ℂ, Continuous f → (∀ γ ∈ ratU σ W.J, ∀ h, f (γ * h) = f h) →
        (∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖f h‖ * (qht h : ℝ) ^ N ≤ C) → GlobalTheory.ThKLiftCusp.IsCuspW W f →
        ∀ h, ∫ h' in 𝓕, f h' * Ez s h h' ∂μ = ∫ g, φ s g * f (h * g) ∂μ := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s' r₁ s₁ hP hmin hn hd Φ₁ hΦ₁ Φ₂ hΦ₂ μ hμ
  have hW := hP.skew
  let W₂ : Spc F E (d + d) := ⟨dblGram finSumFinEquiv W.J, sumLat finSumFinEquiv W.L W.L,
    fun w => blkMat finSumFinEquiv (W.θ w) (-W.θ w), fun _ => 1⟩
  obtain ⟨i, hi⟩ := GlobalTheory.blockDiag_unitary_hom F E σ d W W₂ rfl
  obtain ⟨K, φ₀, Ψ, κ, hK, hI, hφ₀, hconv, hΨ, hκ, hkern⟩ :=
    GlobalTheory.T.doubling_seesaw_polynomial_data hKP F E σ B n d X W M χX χW om r s' r₁ s₁ hP hmin hn hd Φ₂ hΦ₂ Φ₁ hΦ₁ W₂ rfl rfl (fun _ => rfl) i hi
  obtain ⟨Ei, hEi1, hEi2⟩ := hKP.siegelEisensteinDoubled F E σ hP.base.cm hP.base.unram B d hd W hW.skew hW.lat hW.dual hW.cartan
    W₂ rfl rfl (fun _ => rfl) K hK hI χX hP.hX (((n : ℂ) - (d : ℂ)) / 2) φ₀ hφ₀
  obtain ⟨hwc, hw1, hwΓ⟩ := GlobalTheory.ChiDetFun.chiDet_props F E σ d W χX hP.hX
  obtain ⟨R₀, hR₀, hU⟩ := GlobalTheory.T.doubling_gram_lattice_theta hKP F E σ B n d X W M χX χW om r s' r₁ s₁ hP hd W₂ rfl rfl (fun _ => rfl) i hi K hK hI
    φ₀ hφ₀ hconv μ hμ
  refine ⟨fun s h h' => (if s = ((n : ℂ) - (d : ℂ)) / 2 then Ψ (i (h, h')) else Ei s (i (h, h'))) *
      (fun h : UA σ W.J => (((χX (Matrix.GeneralLinearGroup.det h.1))⁻¹ : Circle) : ℂ)) h',
    fun s g => flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ₀ (((n : ℂ) - (d : ℂ)) / 2) s (i (1, g)) *
      (fun h : UA σ W.J => (((χX (Matrix.GeneralLinearGroup.det h.1))⁻¹ : Circle) : ℂ)) g, ((n : ℂ) - (d : ℂ)) / 2, κ,
      max R₀ (((n : ℂ) - (d : ℂ)) / 2).re, hκ, ?_, ?_, ?_⟩
  · intro h h'
    simp only [if_true]
    exact hkern h h'
  · exact isRegFam_doubled F E σ d W W₂ rfl i hi _ hconv Ei (fun s hs g => (hEi1 s hs g).2) hEi2 (((n : ℂ) - (d : ℂ)) / 2) Ψ hΨ
      (fun h : UA σ W.J => (((χX (Matrix.GeneralLinearGroup.det h.1))⁻¹ : Circle) : ℂ)) hwc hw1 hwΓ
  · intro s hs
    have hs0 : R₀ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    obtain ⟨hint, hunf⟩ := hU s hs0
    refine ⟨hint, fun 𝓕 h𝓕 f hfc hfΓ hfd hfcusp h => ?_⟩
    have hs' : (d : ℝ) / 2 < s.re := lt_of_le_of_lt hR₀ hs0
    have hne : s ≠ ((n : ℂ) - (d : ℂ)) / 2 := by
      intro he
      rw [← he] at hs
      exact absurd (lt_of_le_of_lt (le_max_right _ _) hs) (lt_irrefl _)
    rw [← hunf 𝓕 h𝓕 f hfc hfΓ hfd hfcusp h]
    refine congrArg (fun F' : UA σ W.J → ℂ => ∫ h' in 𝓕, F' h' ∂μ) (funext fun h' => ?_)
    simp only [if_neg hne, (hEi1 s hs' _).2]

end GlobalTheory.CuspDbl
