import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneOrthogonalGramRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsConstAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardParabolicUnipotentMono
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewPlaneEisensteinConstantTermStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewPlaneUnipotentIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewPlaneFourierExpansionStatement
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

open Matrix

namespace GlobalTheory.FlagDecomp

theorem fix_aux : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (hσ : ∀ x, σ (σ x) = x) (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
      ∀ (c₀ : E) (hc₀ : c₀ ≠ 0), IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) →
      ∀ (r : ℕ) (Xf Yf : Matrix (Fin n₁) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W₁.J.map σ) Xf Yf →
      ∀ X' Y' : Matrix (Fin n) (Fin (r + 1)) E, GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W.J.map σ) X' Y' →
      (∀ k, X' k 0 = H.x k) → (∀ k, Y' k 0 = c₀⁻¹ * H.y k) →
      (∀ (k : Fin n) (i : Fin r), X' k i.succ = (H.ι * Xf) k i ∧ Y' k i.succ = (H.ι * Yf) k i) → ∀ S' : Finset (Fin r),
      ∀ g : UA σ W.J, GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ g ∈ GlobalTheory.StdPar.unip σ (c₀ • W.J.map σ) X' (insert 0 (S'.map (Fin.succEmb r))) → mat g *ᵥ incV F H.x = incV F H.x := by
  intro F E _ _ _ _ _ σ hCM hσ n n₁ W W₁ H hsk hn hxx hyy hxy hι hJ₁ c₀ hc₀ hN₁ hN r Xf Yf hWf X' Y' hW' hX0 hY0 hXs S' g hg
  have h := (Subgroup.mem_iInf.1 hg.1 0).2 ((GlobalTheory.SiegelSet.adMat F X')ᵀ 0) (Submodule.subset_span ⟨0, rfl, rfl⟩)
  have e : GlobalTheory.StdPar.colSpan F X' {i | ∃ k ∈ insert 0 (S'.map (Fin.succEmb r)), i ≤ k ∧ k < 0} = ⊥ := by
    simp [GlobalTheory.StdPar.colSpan]
  rw [e, Submodule.mem_bot, sub_eq_zero] at h
  have hx : (GlobalTheory.SiegelSet.adMat F X')ᵀ 0 = incV F H.x := funext fun k => by simp [incV, hX0 k]
  rw [hx] at h
  exact h

theorem unipotent_radical_of_skew_plane : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (hσ : ∀ x, σ (σ x) = x) (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
      ∀ (c₀ : E) (hc₀ : c₀ ≠ 0), IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) →
      ∀ M : UA σ W₁.J → UA σ W.J, Continuous M → (∀ h₁, IsLevi (W₁ := W₁) H 1 h₁ (M h₁)) →
      (∀ γ ∈ ratU σ W₁.J, M γ ∈ ratU σ W.J) →
      ∀ (g : UA σ W.J) (h₁ : UA σ W₁.J), mat g *ᵥ incV F H.x = incV F H.x → (∀ z : Fin n₁ → AE F E, ∃ a : AE F E, mat g *ᵥ (incM F H.ι *ᵥ z) = a • incV F H.x + incM F H.ι *ᵥ (mat h₁ *ᵥ z)) → g * (M h₁)⁻¹ ∈ unip σ W H := by
  intro F E _ _ _ _ _ σ hCM hσ n n₁ W W₁ H hsk hn hxx hyy hxy hι hJ₁ c₀ hc₀ hN₁ hN M hMc hM hMr g h₁ hfix hact
  apply Subgroup.subset_closure
  have mm : ∀ {k : ℕ} {J : Matrix (Fin k) (Fin k) E} (a b : UA σ J), mat (a * b) = mat a * mat b := fun _ _ => rfl
  have mi : ∀ {k : ℕ} {J : Matrix (Fin k) (Fin k) E} (a : UA σ J), mat a⁻¹ * mat a = 1 ∧ mat a * mat a⁻¹ = 1 := fun a =>
    ⟨by rw [← mm, inv_mul_cancel]; rfl, by rw [← mm, mul_inv_cancel]; rfl⟩
  have hx1 : mat (M h₁) *ᵥ incV F H.x = incV F H.x := by simpa using (hM h₁).1
  have hι1 := (hM h₁).2.2
  have hinvx : mat (M h₁)⁻¹ *ᵥ incV F H.x = incV F H.x := by
    conv_lhs => rw [← hx1]
    rw [mulVec_mulVec, (mi _).1, one_mulVec]
  have hinvι : mat (M h₁)⁻¹ * incM F H.ι = incM F H.ι * mat h₁⁻¹ := by
    calc mat (M h₁)⁻¹ * incM F H.ι = mat (M h₁)⁻¹ * (incM F H.ι * mat h₁) * mat h₁⁻¹ := by
          rw [Matrix.mul_assoc (mat _), Matrix.mul_assoc (incM F H.ι), (mi h₁).2, Matrix.mul_one]
      _ = incM F H.ι * mat h₁⁻¹ := by
          rw [← hι1, ← Matrix.mul_assoc, (mi _).1, Matrix.one_mul]
  refine ⟨by rw [mm, ← mulVec_mulVec, hinvx, hfix], fun z => ?_⟩
  obtain ⟨a, ha⟩ := hact (mat h₁⁻¹ *ᵥ z)
  refine ⟨a, ?_⟩
  rw [mm, ← mulVec_mulVec, mulVec_mulVec (N := incM F H.ι), hinvι, ← mulVec_mulVec, ha, mulVec_mulVec (M := mat h₁), (mi h₁).2,
    one_mulVec, add_comm]

theorem mem_unip_insert_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (hσ : ∀ x, σ (σ x) = x) (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
      ∀ (c₀ : E) (hc₀ : c₀ ≠ 0), IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) →
      ∀ M : UA σ W₁.J → UA σ W.J, Continuous M → (∀ h₁, IsLevi (W₁ := W₁) H 1 h₁ (M h₁)) →
      (∀ γ ∈ ratU σ W₁.J, M γ ∈ ratU σ W.J) →
      ∀ (r : ℕ) (Xf Yf : Matrix (Fin n₁) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W₁.J.map σ) Xf Yf →
      ∀ X' Y' : Matrix (Fin n) (Fin (r + 1)) E, GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W.J.map σ) X' Y' →
      (∀ k, X' k 0 = H.x k) → (∀ k, Y' k 0 = c₀⁻¹ * H.y k) →
      (∀ (k : Fin n) (i : Fin r), X' k i.succ = (H.ι * Xf) k i ∧ Y' k i.succ = (H.ι * Yf) k i) → ∀ S' : Finset (Fin r),
      ∀ g : GAd σ (c₀ • W.J.map σ), g ∈ GlobalTheory.StdPar.unip σ (c₀ • W.J.map σ) X' (insert 0 (S'.map (Fin.succEmb r))) ↔
        ∃ v ∈ unip σ W H, ∃ u ∈ GlobalTheory.StdPar.unip σ (c₀ • W₁.J.map σ) Xf S', g = GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ v * GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ (M ((GlobalTheory.ThK.SquareIntegrability.toGAd hσ W₁.J hc₀).symm u)) := by
  intro F E _ _ _ _ _ σ hCM hσ n n₁ W W₁ H hsk hn hxx hyy hxy hι hJ₁ c₀ hc₀ hN₁ hN M hMc hM hMr r Xf Yf hWf X' Y' hW' hX0 hY0 hXs S' g
  have hd : W₁.J.det ≠ 0 := fun h0 => hN₁.2 (by
    rw [Matrix.det_smul, show (W₁.J.map σ).det = (σ : E →+* E) W₁.J.det from by rw [RingHom.map_det]; rfl, h0, map_zero, mul_zero])
  have hP : GlobalTheory.ThK.GLTwo.IsHypPlane σ H W W₁ := ⟨hn, hxx, hyy, hxy, hι, hJ₁⟩
  have hB : ∀ v ∈ unip σ W H, GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ v ∈ GlobalTheory.StdPar.unip σ (c₀ • W.J.map σ) X' (insert 0 (S'.map (Fin.succEmb r))) := fun v hv =>
    GlobalTheory.StdPar.unip_mono_of_subset F E σ hCM n _ hN (r + 1) X' Y' hW' _ {0} (by simp)
      ((hP.mem_unip_iff hσ hsk hd hc₀ hW' (Nat.succ_pos r) hX0 v).1 hv)
  constructor
  · intro hg
    set g₀ := (GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀).symm g with hg₀def
    have hg₀ : GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ g₀ ∈ GlobalTheory.StdPar.unip σ (c₀ • W.J.map σ) X' (insert 0 (S'.map (Fin.succEmb r))) := by rw [hg₀def, MulEquiv.apply_symm_apply]; exact hg
    have hfix := fix_aux F E σ hCM hσ n n₁ W W₁ H hsk hn hxx hyy hxy hι hJ₁ c₀ hc₀ hN₁ hN r Xf Yf hWf X' Y' hW' hX0 hY0 hXs S' g₀ hg₀
    obtain ⟨h₁, hh₁⟩ := GlobalTheory.T.skew_plane_eisenstein_constant_term F E σ hCM hσ n n₁ W W₁ H hsk hn hxx hyy hxy hι hJ₁ c₀ hc₀ hN₁ hN g₀ hfix
    refine ⟨g₀ * (M h₁)⁻¹, unipotent_radical_of_skew_plane F E σ hCM hσ n n₁ W W₁ H hsk hn hxx hyy hxy hι hJ₁ c₀ hc₀ hN₁ hN M hMc hM hMr g₀ h₁ hfix hh₁,
      GlobalTheory.ThK.SquareIntegrability.toGAd hσ W₁.J hc₀ h₁, GlobalTheory.T.skew_plane_unipotent_integral F E σ hCM hσ n n₁ W W₁ H hsk hn hxx hyy hxy hι hJ₁ c₀ hc₀ hN₁ hN r Xf Yf hWf X' Y' hW' hX0 hY0 hXs S' g₀ h₁ hg₀ hh₁, ?_⟩
    rw [MulEquiv.symm_apply_apply, ← map_mul, inv_mul_cancel_right, hg₀def, MulEquiv.apply_symm_apply]
  · rintro ⟨v, hv, u, hu, rfl⟩
    set h₁ := (GlobalTheory.ThK.SquareIntegrability.toGAd hσ W₁.J hc₀).symm u with hh₁def
    have hu' : GlobalTheory.ThK.SquareIntegrability.toGAd hσ W₁.J hc₀ h₁ ∈ GlobalTheory.StdPar.unip σ (c₀ • W₁.J.map σ) Xf S' := by rw [hh₁def, MulEquiv.apply_symm_apply]; exact hu
    refine mul_mem (hB v hv) (GlobalTheory.T.skew_plane_fourier_expansion F E σ hCM hσ n n₁ W W₁ H hsk hn hxx hyy hxy hι hJ₁ c₀ hc₀ hN₁ hN r Xf Yf hWf X' Y' hW' hX0 hY0 hXs S' (M h₁) h₁ ?_ ?_ hu')
    · have := (hM h₁).1
      simpa using this
    · intro z
      refine ⟨0, ?_⟩
      rw [zero_smul, zero_add, Matrix.mulVec_mulVec, (hM h₁).2.2, ← Matrix.mulVec_mulVec]

end GlobalTheory.FlagDecomp
