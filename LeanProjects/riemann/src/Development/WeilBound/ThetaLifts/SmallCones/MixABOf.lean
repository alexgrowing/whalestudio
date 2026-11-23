import Development.WeilBound.ThetaLifts.SmallCones.KerPol
import Development.WeilBound.ThetaLifts.SmallCones.ThetaKernelGeneralIdentity
import Development.WeilBound.ThetaLifts.SmallCones.ConeBasic

noncomputable section

namespace PositivityTheory.ThKCT.Ker

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow PositivityTheory.Mix
open Matrix (vecMulVec)

theorem mixAB_of (hW : MixW) (hX : MixX) (hZ : EvZero) (hP : PairEx) (hE : ThetaExp) (hU : EvUniq) : MixAB := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' χX χW om om₀ hp hp₀
  have hB := hp.base
  have hψ := hB.std
  have p := pg_herm hB hH hp.herm
  have p' := pg_skew hB hH' hp.skew
  refine ⟨fun e he => ?_, fun e he => ?_⟩
  · obtain ⟨⟨M₁, g₁⟩, h1⟩ := hP F E σ B hB n d₁ X W₁ _ _ _ _ hp.herm hp₀.skew
    obtain ⟨om₁, hp₁⟩ := h1 χX χW hp.hX hp.hW hp.resX hp₀.resW M₁ g₁
    obtain ⟨⟨e₀, he₀⟩, -⟩ := hZ F E σ B n d X W M χX χW om _ _ _ _ hp d₁ X W₁ H' i₀ i₁ M₁ rfl hH' g₁
    obtain ⟨⟨e₁, he₁⟩, h2⟩ := hX F E σ B n d₁ X W₁ M₁ χX χW om₁ _ _ _ _ hp₁ n₁ X₁ H j₀ j₁ M₀ om₀ _ _ hH hp₀
    have hc := isEv_comp hψ hp.good g₁ hp₀.good he₀ he₁
      (comp_ne (polX p (skew_det hp₀.skew)) hE hB hp.good g₁ hp₀.good he₀ he₁) (K := isoA H H') (by
        rintro u (h | ⟨z, rfl⟩)
        · exact Or.inl h
        · exact Or.inr ⟨_, ⟨z, rfl⟩, by rw [incM_one, Matrix.one_mul, vv_mul_r]⟩)
    rw [Matrix.one_mul, Matrix.mul_one] at hc
    obtain ⟨c, -, hc⟩ := (polA p p').uniq hU hB hp.good hp₀.good (isEv_sumA hψ p' hc) (isEv_sumA hψ p' he)
    intro t g₁ q hq u hu t' h₁ q' hq' u' hu' Φ hΦ
    rw [hc _ (pair_pres hp _ hΦ), hc _ hΦ, LinearMap.comp_apply, LinearMap.comp_apply,
      hW F E σ B n d X W M χX χW om _ _ _ _ hp d₁ W₁ H' i₀ i₁ M₁ om₁ _ _ hH' hp₁ e₀ he₀ _ t' h₁ q' hq' u' hu' Φ hΦ, map_smul,
      h2 e₁ he₁ h₁ t g₁ q hq u hu _ (he₀.maps Φ hΦ), map_smul, smul_smul, smul_smul, smul_smul]
    congr 1
    ring
  · obtain ⟨⟨M₁, g₁⟩, h1⟩ := hP F E σ B hB n₁ d X₁ W _ _ _ _ hp₀.herm hp.skew
    obtain ⟨om₁, hp₁⟩ := h1 χX χW hp.hX hp.hW hp₀.resX hp.resW M₁ g₁
    obtain ⟨⟨e₀, he₀⟩, h2⟩ := hX F E σ B n d X W M χX χW om _ _ _ _ hp n₁ X₁ H j₀ j₁ M₁ om₁ _ _ hH hp₁
    obtain ⟨⟨e₁, he₁⟩, -⟩ := hZ F E σ B n₁ d X₁ W M₁ χX χW om₁ _ _ _ _ hp₁ d₁ X₁ W₁ H' i₀ i₁ M₀ rfl hH' hp₀.good
    have hc := isEv_comp hψ hp.good g₁ hp₀.good he₀ he₁
      (comp_ne (pol0 (herm_det hp₀.herm) p') hE hB hp.good g₁ hp₀.good he₀ he₁) (K := isoB H H') (by
        rintro u (h | ⟨z, rfl⟩)
        · exact Or.inl h
        · exact Or.inr ⟨_, ⟨z, rfl⟩, by rw [incM_one, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_vecMulVec]⟩)
    rw [Matrix.one_mul, Matrix.mul_one] at hc
    obtain ⟨c, -, hc⟩ := (polB p p').uniq hU hB hp.good hp₀.good (isEv_sumB hψ p hc) (isEv_sumB hψ p he)
    intro t g₁ q hq u hu t' h₁ q' hq' u' hu' Φ hΦ
    rw [hc _ (pair_pres hp _ hΦ), hc _ hΦ, LinearMap.comp_apply, LinearMap.comp_apply,
      h2 e₀ he₀ _ t g₁ q hq u hu Φ hΦ, map_smul,
      hW F E σ B n₁ d X₁ W M₁ χX χW om₁ _ _ _ _ hp₁ d₁ W₁ H' i₀ i₁ M₀ om₀ _ _ hH' hp₀ e₁ he₁ _ t' h₁ q' hq' u' hu' _ (he₀.maps Φ hΦ),
      map_smul, smul_smul, smul_smul, smul_smul]
    congr 1
    ring

end PositivityTheory.ThKCT.Ker
