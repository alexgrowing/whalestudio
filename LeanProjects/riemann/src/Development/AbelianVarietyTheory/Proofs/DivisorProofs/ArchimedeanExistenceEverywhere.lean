import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesOnEqModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormPairQuotientHorizontalGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionQuotientOfContinuousReadingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspSectionAnnihilatorStatement

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCore

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem archEx_continuous_det {r : ℕ} {Ψ : Finset (E →+* ℂ)} (τ : Ψ) :
    Continuous fun y : Frame Ψ r => (mat y τ).det :=
  Continuous.matrix_det (continuous_apply τ)

theorem archEx_continuousOn_horizGen {r : ℕ} (X : Data E r) (τ : X.Ψ) : ContinuousOn (horizGen τ) X.dom :=
  (archEx_continuous_det τ).continuousOn.inv₀ fun _ hy => (hy τ).1

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem archEx_relab_mem {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U) (τ : Psi H) (k : U.Comp) :
    relab c σ τ.1 ∈ (U.X k).Ψ := by
  refine ((hU.2.1 k).2 _).2 ?_
  have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
  exact (congrArg σ (Subtype.ext τ.2)).trans hσ0

end SlopeTestRemainingChoices

theorem archEx_always : Always fun U x => ArchEx U x := by
  intro E _ _ _ H Dw l Xo c r U x hL Z τ
  obtain ⟨G, f, g, -, hf, hg, hf0, hq⟩ := GlobalTheory.T.exists_cuspForm_pair_quotient_horizontal_generator E H Dw l Xo c r U x hL Z τ
  have hfs : f ∈ secZ Xo c (exZ Dw G) := cuspW_le_secZ G hf.1
  have hgs : g ∈ secZ Xo c (exZ Dw (G + wtOf Dw (flatWt Dw τ) 0)) := cuspW_le_secZ _ hg.1
  have hex : exZ Dw (G + wtOf Dw (flatWt Dw τ) 0) - exZ Dw G = exOf Dw (flatWt Dw τ) 0 := by
    funext i; rw [Pi.sub_apply, exZ_add, exOf, add_sub_cancel_left]
  have hmem : ∀ σ (hσ : GoodEmb c σ) k, relab c σ τ.1 ∈ ((U σ).X k).Ψ := fun σ hσ k =>
    archEx_relab_mem (U σ) hσ (hL.unf σ hσ) τ k
  have hgood : ∀ σ, GoodEmb c (goodOf c σ) := fun σ => goodEmb_goodOf c σ
  have hσ₀ := hgood c.F.val.toRingHom
  generalize goodOf c c.F.val.toRingHom = σ₀ at hσ₀
  obtain ⟨a₀, ha₀, h₀⟩ := hq σ₀ hσ₀
  obtain ⟨sig, hsig, hsi, hsf⟩ := GlobalTheory.T.exists_section_quotient_of_continuous_reading E H Dw l Xo c r U x hL Z _ _ f g hfs hf.2 hgs hg.2 hf0 σ₀ hσ₀
    (fun k y => a₀ * horizGen ⟨_, hmem σ₀ hσ₀ k⟩ y)
    (fun k => continuousOn_const.mul (archEx_continuousOn_horizGen _ _)) (fun z hz => h₀ z.1 _ z.2 hz)
  rw [hex] at hsig
  have hrd : ∀ σ (hσ : GoodEmb c σ), ∃ a : ℂ, a ≠ 0 ∧ ∀ z ∈ framesOn (U σ) Z,
      rdU (U σ) sig z.1 z.2 = a * horizGen ⟨_, hmem σ hσ z.1⟩ z.2 := fun σ hσ => by
    obtain ⟨a, ha, h⟩ := hq σ hσ
    exact ⟨a, ha, (GlobalTheory.T.cusp_section_annihilator E H Dw l Xo c r U x hL Z G _ f sig hf hf0 hsig).2 rfl σ hσ
      (fun k y => a * horizGen ⟨_, hmem σ hσ k⟩ y)
      (fun k => continuousOn_const.mul (archEx_continuousOn_horizGen _ _))
      (fun z hz => hsf.symm ▸ h z.1 _ z.2 hz)⟩
  have hnorm : ∀ σ (hσ : GoodEmb c σ), ∃ b : ℝ, 0 < b ∧
      homN (U σ) x (wtOf Dw (flatWt Dw τ) 0) sig '' framesOn (U σ) Z = {b} := fun σ hσ => by
    obtain ⟨a, ha, h⟩ := hrd σ hσ
    obtain ⟨k, hk⟩ := framesOn_eq_model E H Dw l Xo c r U x hL Z σ hσ
    obtain ⟨y, hy⟩ := GlobalTheory.CompBij.frames_nonempty ((U σ).X k)
    refine ⟨lieFacZ Dw x (wtOf Dw (flatWt Dw τ) 0) * (‖a‖ * Real.sqrt ‖relab c σ τ.1 ((U σ).X k).Gm.det‖),
      mul_pos (lieFacZ_pos _ _) (mul_pos (norm_pos_iff.2 ha) (Real.sqrt_pos.2 (norm_pos_iff.2
        ((map_ne_zero _).2 ((U σ).X k).Gm_det)))), image_eq_singleton_iff.2 ⟨⟨⟨k, y⟩, ?_⟩, ?_⟩⟩
    · rw [hk]; exact ⟨rfl, hy⟩
    · rintro ⟨k', y'⟩ hz
      have h1 := h _ hz
      have hz' := hz
      rw [hk] at hz'
      obtain ⟨rfl, hy'⟩ : k' = k ∧ y' ∈ ((U σ).X k').dom := hz'
      rw [← pnorm_horizGen ((U σ).X k') ⟨_, hmem σ hσ k'⟩ hy', homN, ptN,
        modelWt_flatWt (U σ) hσ (hL.unf σ hσ) τ k' (hmem σ hσ k')]
      simp only at h1
      simp only [Data.pnorm, h1, norm_mul, mul_assoc]
  have hg0 : g ≠ 0 := fun h0 => by
    have h1 : sig = 0 := hsi.symm.trans
      ((GlobalTheory.T.cusp_section_annihilator E H Dw l Xo c r U x hL Z G _ f sig hf hf0 hsig).1 (hsf.trans h0))
    obtain ⟨b, hb, h2⟩ := hnorm σ₀ hσ₀
    obtain ⟨⟨z, hz⟩, h3⟩ := image_eq_singleton_iff.1 h2
    have h4 := h3 z hz
    rw [h1, ← zero_smul c.F (0 : Rul Xo c), homN_smul, map_zero, norm_zero, zero_mul] at h4
    exact hb.ne h4
  obtain ⟨inv, hinv, hii, hig⟩ := GlobalTheory.T.exists_section_quotient_of_continuous_reading E H Dw l Xo c r U x hL Z _ _ g f hgs hg.2 hfs hf.2 hg0 σ₀ hσ₀
    (fun k y => a₀⁻¹ * (mat y ⟨_, hmem σ₀ hσ₀ k⟩).det)
    (fun k => (continuous_const.mul (archEx_continuous_det _)).continuousOn) (fun z hz => by
      have hd := (hz.1 ⟨_, hmem σ₀ hσ₀ z.1⟩).1
      rw [h₀ z.1 (hmem σ₀ hσ₀ z.1) z.2 hz, horizGen]
      field_simp)
  rw [← neg_sub, hex] at hinv
  have hif : idem Z * f = f := by rw [← hig, ← mul_assoc, hii]
  have hs0 : sig * inv - idem Z ∈ secZ Xo c 0 := by
    have := mul_mem_secZ hsig hinv
    rw [add_neg_cancel] at this
    exact Submodule.sub_mem _ this (idem_mem_secZ Z)
  have hone : sig * inv = idem Z := by
    have h1 := (GlobalTheory.T.cusp_section_annihilator E H Dw l Xo c r U x hL Z G _ f _ hf hf0 hs0).1 (by
      rw [sub_mul, hif, mul_right_comm, hsf, mul_comm, hig, sub_self])
    rwa [mul_sub, ← mul_assoc, hsi, idem_mul_idem, sub_eq_zero] at h1
  choose b hb hb' using fun σ => hnorm _ (hgood σ)
  exact ⟨⟨sig, inv, hsig, hinv, hsi, hii, hone, b, hb, hb'⟩⟩

end GlobalTheory.FlatCore

end
