import Development.WeilBound.ThetaLifts.SmallCones.FormSwapZero
import Development.WeilBound.ThetaLifts.SmallCones.KerPol

noncomputable section

namespace PositivityTheory.ThKCT

open NumberField Matrix GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.ThK PositivityTheory.ThKG So Ker

theorem soZeroA'_of (hL : LinEx) (hX : MixX) (hE : ThetaExp) (hU : EvUniq) : SoZeroA' := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' hB hXh hW hM hM₀ M₁ hM₁
    ⟨χX, χW, om₁, om₀, r₁, s₁, r₀, s₀, r₂, s₂, hP₁, hP₀⟩ e₀ e he₀ he Ψ hΨ hso
  obtain ⟨eX, heX⟩ := (hX F E σ B n d₁ X W₁ M₁ χX χW om₁ r₁ s₁ r₂ s₂ hP₁ n₁ X₁ H j₀ j₁ M₀ om₀ r₀ s₀ hH hP₀).1
  have pg := pg_herm hB hH hXh
  have pg' := pg_skew hB hH' hW
  have hne := comp_ne (polX (W := W₁) pg (skew_det hP₁.skew)) hE hB hM hM₁ hM₀ he₀ heX
  have hc := isEv_comp (K := isoA H H') hB.std hM hM₁ hM₀ he₀ heX hne (by
    rintro u (h | ⟨z, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨_, ⟨z, rfl⟩, by rw [incM_one, Matrix.one_mul, vv_mul_r]⟩)
  rw [Matrix.one_mul, Matrix.mul_one] at hc
  obtain ⟨c, -, h⟩ := (polA pg pg').uniq hU hB hM hM₀ (isEv_sumA hB.std pg' hc) (isEv_sumA hB.std pg' he)
  rw [h Ψ hΨ, LinearMap.comp_apply, ev_zero hL hB hP₁.herm hP₁.skew hM₁ _ eX (x_ne hH) (fun z => heX.inv _ ⟨z, rfl⟩) _ hso, smul_zero]

end PositivityTheory.ThKCT

end
