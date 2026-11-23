import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneOrthogonalGramRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsConstAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewPlaneModularCharacter
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

noncomputable section

namespace GlobalTheory.LeviSplitFull

open Matrix GlobalTheory.LeviSplit

set_option maxHeartbeats 600000 in
open GlobalTheory.StdPar GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThK.GLTwo in
theorem levi_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (hσ : ∀ x, σ (σ x) = x) (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
      ∀ (c₀ : E) (hc₀ : c₀ ≠ 0), IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) →
      ∀ M : UA σ W₁.J → UA σ W.J, (∀ h₁, IsLevi (W₁ := W₁) H 1 h₁ (M h₁)) →
      ∀ (r : ℕ) (Xf Yf : Matrix (Fin n₁) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W₁.J.map σ) Xf Yf →
      ∀ X' Y' : Matrix (Fin n) (Fin (r + 1)) E, GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W.J.map σ) X' Y' →
      (∀ k, X' k 0 = H.x k) → (∀ k, Y' k 0 = c₀⁻¹ * H.y k) →
      (∀ (k : Fin n) (i : Fin r), X' k i.succ = (H.ι * Xf) k i ∧ Y' k i.succ = (H.ι * Yf) k i) → ∀ S' : Finset (Fin r),
      ∀ γ : GAd σ (c₀ • W.J.map σ), γ ∈ GlobalTheory.StdPar.levi σ (c₀ • W.J.map σ) X' Y' (insert 0 (S'.map (Fin.succEmb r))) →
        ∃ (t : (AE F E)ˣ) (m : UA σ W.J) (h₁ : UA σ W₁.J), IsLevi (W₁ := W₁) H t 1 m ∧
          GlobalTheory.ThK.SquareIntegrability.toGAd hσ W₁.J hc₀ h₁ ∈ GlobalTheory.StdPar.levi σ (c₀ • W₁.J.map σ) Xf Yf S' ∧
          γ = GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ m * GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ (M h₁) := by
  intro F E _ _ _ _ _ σ hcm hσ n n₁ W W₁ H hskew hn hxx hyy hxy horth hgram c₀ hc₀ hND₁ hND M hM r Xf Yf hW₁ X' Y' hW
    hX0 hY0 hXY S' γ hγ
  obtain ⟨hMm, -⟩ := GlobalTheory.LeviPlaneHom.levi_section_hom F E σ hcm hσ n n₁ W W₁ H hskew hn hxx hyy hxy horth hgram c₀ hc₀
    hND₁ hND M hM
  subst hn
  have hdet : W₁.J.det ≠ 0 := by
    intro h0
    apply hND₁.2
    rw [det_smul, show (W₁.J.map σ).det = σ W₁.J.det from (RingHom.map_det (σ : E →+* E) _).symm, h0, map_zero, mul_zero]
  obtain ⟨L, hL, hLx, hLy, hx, hy, hD⟩ := exists_proj hσ W W₁ H hskew hxx hyy hxy horth hgram hdet
  set e := toGAd hσ W.J hc₀
  set e₁ := toGAd hσ W₁.J hc₀
  have eX : (fun i => X' i 0) = H.x := funext hX0
  have eY : (fun i => Y' i 0) = c₀⁻¹ • H.y := funext hY0
  have eY' : incV F (c₀⁻¹ • H.y) = inclR (F := F) (AF F) c₀⁻¹ • incV F H.y := funext fun i => map_mul _ _ _
  have lineY : ∀ (g : Matrix _ _ (AE F E)) (s : AE F E), g *ᵥ incV F (fun i => Y' i 0) = s • incV F (fun i => Y' i 0) ↔
      g *ᵥ incV F H.y = s • incV F H.y := fun g s => by
    rw [eY, eY', mulVec_smul, smul_comm s]
    exact ((IsUnit.mk0 _ (inv_ne_zero hc₀)).map (inclR (F := F) (AF F))).smul_left_cancel
  have hγ' : ∀ k ∈ insert 0 (S'.map (Fin.succEmb r)),
      γ ∈ frameStab σ _ (initCols X' k) ((⊤ : Subgroup (AE F E)ˣ).comap Matrix.GeneralLinearGroup.det) ∧
      γ ∈ frameStab σ _ (initCols Y' k) ((⊤ : Subgroup (AE F E)ˣ).comap Matrix.GeneralLinearGroup.det) := by
    simpa only [levi, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.comap_top] using hγ
  obtain ⟨h3, h2⟩ := hγ' 0 (Finset.mem_insert_self _ _)
  obtain ⟨s, -, hw⟩ := frameStab_zero.1 h2
  obtain ⟨t, -, hv⟩ := frameStab_zero.1 h3
  obtain ⟨h, hh⟩ := isLevi_of_lines hxy hgram hdet hσ hx hy hD (e.symm γ) (t := t) (s := s) (eX ▸ hv) ((lineY _ _).1 hw)
  have hι : (matHom _ σ _ γ).1 * incM F H.ι = incM F H.ι * (matHom _ σ _ (e₁ h)).1 := hh.2.2
  have a1 := frameStab_succ (yx hcm hND hW) hL (by rw [eX, hLx]) (fun i j => (hXY i j).1) (Subgroup.mem_top _) hv hι
  have a2 := frameStab_succ hW.xy hL (by rw [eY, mulVec_smul, hLy, smul_zero]) (fun i j => (hXY i j).2)
    (Subgroup.mem_top _) hw hι
  have hM1 : M 1 = 1 := by
    have := hMm 1 1
    rw [mul_one] at this
    exact (mul_eq_left.1 this.symm)
  refine ⟨t, e.symm γ * M h⁻¹, h, ?_, ?_, ?_⟩
  · have := GlobalTheory.LeviHom.isLevi_mul H hh (hM h⁻¹)
    rwa [mul_one, mul_inv_cancel] at this
  · simp only [levi, Subgroup.mem_inf, Subgroup.mem_iInf]
    intro k hk
    have := hγ' k.succ (Finset.mem_insert_of_mem (Finset.mem_map.2 ⟨k, hk, rfl⟩))
    rw [a1, a2, Subgroup.comap_top] at this
    exact this
  · rw [← map_mul, mul_assoc, ← hMm, inv_mul_cancel, hM1, mul_one, MulEquiv.apply_symm_apply]

end GlobalTheory.LeviSplitFull
