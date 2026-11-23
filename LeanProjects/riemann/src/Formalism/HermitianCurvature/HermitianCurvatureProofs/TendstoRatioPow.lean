import Formalism.HermitianCurvature.HermitianCurvatureProofs.MemLpBzOfSup
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TendstoIntegralInnerGermMoving

namespace Formalism.FourierDecayAlt.P.PBK

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

section propGD

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure GermD {ι : Type} (s : ℕ) (β ε : ℂ) (Y : Finset ι) (ut : ι → ℂ → ℂ → H) (bt : ι → ℂ → H) (SS : ℝ) :
    Prop where
  hs : s ≠ 0
  hβ : β ≠ 0
  hε : ‖ε‖ = 1
  memU : ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → MemLp (ut h x) 2 volume
  sup : ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → ∫ D, ‖ut h x D‖ ^ 2 ≤ SS
  meas : ∀ h ∈ Y, StronglyMeasurable (bt h)
  loc : ∀ h ∈ Y, ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → IntegrableOn (fun z => ‖bz s (bt h) z‖ ^ 2) K
  germ : ∀ h ∈ Y, ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → ∃ C : ℝ, ∀ x : ℂ, x ≠ 0 →
    ∀ᵐ D, D ∈ K → ‖ut h x D - mainD s β ε (bt h) x D‖ ≤ C * ‖x‖⁻¹

def Uc {ι : Type} (s : ℕ) (ut : ι → ℂ → ℂ → H) : ι × ℂ → ℂ → H := fun p => cvec s (ut p.1) p.2

def Ac {ι : Type} (s : ℕ) (β ε : ℂ) (bt : ι → ℂ → H) : ι × ℂ → ℂ → H :=
  fun p => cvec s (fun x D => mainD s β ε (bt p.1) x D) p.2

def Nhat {ι : Type} (s : ℕ) (β : ℂ) (bt : ι → ℂ → H) (σ : ℂ) (h h' : ι) : ℂ :=
  ∫ z, G.psi β (σ * z) • ⟪bz s (bt h) z, bz s (bt h') z⟫_ℂ

theorem tendsto_ratio_pow (s : ℕ) (a b : ℂ) :
    Tendsto (fun x : ℂ => (x + a) ^ (s - 1) / (x + b) ^ (s - 1)) (cocompact ℂ) (𝓝 1) := by
  have hn : Tendsto (fun x : ℂ => ‖x + b‖) (cocompact ℂ) atTop := by
    have h0 : Tendsto (fun x : ℂ => ‖x‖) (cocompact ℂ) atTop := tendsto_norm_cocompact_atTop
    refine tendsto_atTop_mono (fun x => ?_) (tendsto_atTop_add_const_right _ (-‖b‖) h0)
    have := norm_sub_norm_le x (-b)
    rw [norm_neg, sub_neg_eq_add] at this
    linarith
  have hi : Tendsto (fun x : ℂ => (x + b)⁻¹) (cocompact ℂ) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact (tendsto_inv_atTop_zero.comp hn).congr fun x => by simp [norm_inv]
  have hne : ∀ᶠ x in cocompact ℂ, x + b ≠ 0 :=
    (hn.eventually_gt_atTop 0).mono fun x hx => norm_pos_iff.mp hx
  have hq : Tendsto (fun x : ℂ => 1 + (a - b) * (x + b)⁻¹) (cocompact ℂ) (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℂ))).add ((tendsto_const_nhds (x := a - b)).mul hi)
  have hp := hq.pow (s - 1)
  rw [one_pow] at hp
  refine hp.congr' ?_
  filter_upwards [hne] with x hx
  rw [← div_pow]
  congr 1
  first
  | (field_simp; ring)
  | field_simp

variable {ι : Type} {s : ℕ} {β ε : ℂ} {Y : Finset ι} {ut : ι → ℂ → ℂ → H} {bt : ι → ℂ → H} {SS : ℝ}

theorem GermD.memLp_bz (hG : GermD s β ε Y ut bt SS) {h : ι} (hh : h ∈ Y) :
    MemLp (bz s (bt h)) 2 volume ∧ ∫ z, ‖bz s (bt h) z‖ ^ 2 ≤ SS := memLp_bz_of_sup hG.hs hG.hβ hG.hε (ut h) (bt h) SS (hG.memU h hh) (hG.sup h hh)
    (hG.meas h hh) (hG.loc h hh) (hG.germ h hh)

theorem GermD.memLp_abar (hG : GermD s β ε Y ut bt SS) {h : ι} (hh : h ∈ Y) :
    MemLp (abar s ε (bt h)) 2 volume ∧ ∫ D, abar s ε (bt h) D ^ 2 ≤ s * SS := by
  obtain ⟨hb, hbS⟩ := hG.memLp_bz hh
  obtain ⟨h1, h2⟩ := Formalism.FourierDecayAlt.P.PBK.memLp_abar hG.hs hG.hε (hG.meas h hh) hb
  exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_left hbS (Nat.cast_nonneg s))⟩

theorem GermD.memLp_mainD (hG : GermD s β ε Y ut bt SS) {h : ι} (hh : h ∈ Y) (x : ℂ) :
    MemLp (mainD s β ε (bt h) x) 2 volume := Formalism.FourierDecayAlt.P.PBK.memLp_mainD hG.hs β hG.hε (hG.meas h hh) (hG.memLp_bz hh).1 x

theorem GermD.tendsto_cross (hG : GermD s β ε Y ut bt SS) {h h' : ι} (hh : h ∈ Y) (hh' : h' ∈ Y) (a b : ℂ) :
    Tendsto (fun x => ∫ c, ⟪cvec s (fun x D => ut h x D - mainD s β ε (bt h) x D) (x + a) c,
      cvec s (fun x D => mainD s β ε (bt h') x D) (x + b) c⟫_ℂ) (cocompact ℂ) (𝓝 0) := by
  obtain ⟨hab', habS'⟩ := hG.memLp_abar hh'
  obtain ⟨hab, habS⟩ := hG.memLp_abar hh
  obtain ⟨hdom1, hdom2, hdom3⟩ := dil_dominator (abar s ε (bt h')) hab'
    (fun x : ℂ => (x + a) ^ (s - 1) / (x + b) ^ (s - 1)) (tendsto_ratio_pow s a b)
  have hev : ∀ᶠ x in cocompact ℂ, x + a ≠ 0 ∧ x + b ≠ 0 := by
    filter_upwards [eventually_ne_cocompact (-a), eventually_ne_cocompact (-b)] with x ha hb
    exact ⟨fun h0 => ha (eq_neg_of_add_eq_zero_left h0), fun h0 => hb (eq_neg_of_add_eq_zero_left h0)⟩
  have key : ∀ᶠ x in cocompact ℂ,
      ∫ D, ⟪ut h (x + a) D - mainD s β ε (bt h) (x + a) D,
        ((‖(x + a) ^ (s - 1) / (x + b) ^ (s - 1)‖ : ℝ) : ℂ) •
          mainD s β ε (bt h') (x + b) ((x + a) ^ (s - 1) / (x + b) ^ (s - 1) * D)⟫_ℂ
      = ∫ c, ⟪cvec s (fun x D => ut h x D - mainD s β ε (bt h) x D) (x + a) c,
          cvec s (fun x D => mainD s β ε (bt h') x D) (x + b) c⟫_ℂ := by
    filter_upwards [hev] with x hx
    rw [cvec_inner s _ _ (x + a) (x + b) hx.1 hx.2]
  refine Tendsto.congr' key ?_
  refine tendsto_integral_inner_germ_moving volume
    (fun x D => ut h (x + a) D - mainD s β ε (bt h) (x + a) D)
    (fun x D => ((‖(x + a) ^ (s - 1) / (x + b) ^ (s - 1)‖ : ℝ) : ℂ) •
      mainD s β ε (bt h') (x + b) ((x + a) ^ (s - 1) / (x + b) ^ (s - 1) * D))
    (abar s ε (bt h'))
    (fun x D => |‖(x + a) ^ (s - 1) / (x + b) ^ (s - 1)‖ *
      abar s ε (bt h') ((x + a) ^ (s - 1) / (x + b) ^ (s - 1) * D) - abar s ε (bt h') D|)
    hab' (2 * SS + 2 * (s * SS)) ?_ hdom2 hdom3 ?_ ?_
  · filter_upwards [hev] with x hx
    have hu := hG.memU h hh _ hx.1
    have hm := hG.memLp_mainD hh (x + a)
    refine ⟨hu.sub hm, ?_⟩
    have h1 := integral_sq_sub_le hu hm hab (ae_of_all _ fun D => norm_mainD_le s β ε (bt h) (x + a) D)
    have hb := hG.sup h hh _ hx.1
    beta_reduce
    linarith
  · filter_upwards with x
    refine ae_of_all _ fun D => ?_
    beta_reduce
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    exact (mul_le_mul_of_nonneg_left (norm_mainD_le _ _ _ _ _ _) (norm_nonneg _)).trans (hdom1 x D)
  · intro K hK hK0 δ hδ
    obtain ⟨C, hC⟩ := hG.germ h hh K hK hK0
    filter_upwards [hev, eventually_rate_cocompact a C δ hδ] with x hx hr
    filter_upwards [hC _ hx.1] with D hD hDK
    exact (hD hDK).trans hr

theorem GermD.propG (hG : GermD s β ε Y ut bt SS) :
    (∀ h ∈ Y, MemLp (bz s (bt h)) 2 volume ∧ ∫ z, ‖bz s (bt h) z‖ ^ 2 ≤ SS) ∧
    (∀ Xs : Finset ℂ, (∀ x ∈ Xs, x ≠ 0) →
      KB.BlockPSD (Y ×ˢ Xs) (Y ×ˢ Xs) (gramL volume (Uc s ut) (Uc s ut)) (gramL volume (Uc s ut) (Ac s β ε bt))
        (gramL volume (Ac s β ε bt) (Ac s β ε bt))) ∧
    (∃ B' : ℝ, ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → ‖gramL volume (Ac s β ε bt) (Ac s β ε bt) (h, x) (h, x)‖ ≤ B') ∧
    ∀ h ∈ Y, ∀ h' ∈ Y, ∀ σ : ℂ,
      Tendsto (fun x => gramL volume (Ac s β ε bt) (Ac s β ε bt) (h, x) (h', x + σ)) (cocompact ℂ)
        (𝓝 (Nhat s β bt σ h h')) ∧
      Tendsto (fun x => gramL volume (Uc s ut) (Ac s β ε bt) (h, x) (h', x + σ)) (cocompact ℂ)
        (𝓝 (Nhat s β bt σ h h')) ∧
      Tendsto (fun x => conj (gramL volume (Uc s ut) (Ac s β ε bt) (h', x + σ) (h, x))) (cocompact ℂ)
        (𝓝 (Nhat s β bt σ h h')) := by
  have hs1 : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr hG.hs
  have memUc : ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → MemLp (Uc s ut (h, x)) 2 volume := fun h hh x hx =>
    (memLp_cvec s (ut h) x hx).1 (hG.memU h hh x hx)
  have memAc : ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → MemLp (Ac s β ε bt (h, x)) 2 volume := fun h hh x hx =>
    (memLp_cvec s (fun x D => mainD s β ε (bt h) x D) x hx).1 (hG.memLp_mainD hh x)
  refine ⟨fun h hh => hG.memLp_bz hh, fun Xs hXs => blockPSD_gramL volume Y _ _ memUc memAc Xs hXs, ?_, ?_⟩
  ·
    refine ⟨s * SS, fun h hh x hx => ?_⟩
    obtain ⟨hab, habS⟩ := hG.memLp_abar hh
    have hmD := hG.memLp_mainD hh x
    have i1 : Integrable (fun D => ‖mainD s β ε (bt h) x D‖ ^ 2) := (memLp_two_iff_integrable_sq_norm hmD.1).1 hmD
    have i2 : Integrable (fun D => abar s ε (bt h) D ^ 2) := (memLp_two_iff_integrable_sq hab.1).1 hab
    calc ‖gramL volume (Ac s β ε bt) (Ac s β ε bt) (h, x) (h, x)‖
        ≤ ∫ c, ‖⟪Ac s β ε bt (h, x) c, Ac s β ε bt (h, x) c⟫_ℂ‖ := norm_integral_le_integral_norm _
      _ = ∫ c, ‖Ac s β ε bt (h, x) c‖ ^ 2 := by
          refine integral_congr_ae (Eventually.of_forall fun c => ?_)
          simp only
          rw [inner_self_eq_norm_sq_to_K]
          norm_cast
          exact abs_of_nonneg (sq_nonneg _)
      _ = ∫ D, ‖mainD s β ε (bt h) x D‖ ^ 2 := integral_norm_cvec_sq s _ x hx
      _ ≤ ∫ D, abar s ε (bt h) D ^ 2 := by
          refine integral_mono i1 i2 fun D => ?_
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_mainD_le s β ε (bt h) x D) 2
      _ ≤ s * SS := habS
  · intro h hh h' hh' σ

    have hAA : Tendsto (fun x => gramL volume (Ac s β ε bt) (Ac s β ε bt) (h, x) (h', x + σ)) (cocompact ℂ)
        (𝓝 (Nhat s β bt σ h h')) := by
      have hρ0 : ∀ᶠ x in cocompact ℂ, rhoR s σ x ≠ 0 :=
        (tendsto_rhoR s σ).eventually_ne one_ne_zero
      have hT := tendsto_pairD hG.hs hG.hβ hG.hε (hG.memLp_bz hh).1 (hG.memLp_bz hh').1 (l := cocompact ℂ)
        id (fun x => x + σ) (rhoR s σ) σ hρ0 (tendsto_rhoR s σ) (tendsto_shift s hs1 σ)
        (fun ζ _ hζ => tendsto_shift_ne s hs1 σ ζ hζ)
      refine hT.congr' ?_
      filter_upwards [eventually_ne_zero_add σ] with x hx
      exact (pairD_of_cvec hG.hs β ε (bt h) (bt h') σ x hx.1 hx.2).symm
    refine ⟨hAA, ?_, ?_⟩
    · have hR := hG.tendsto_cross hh hh' 0 σ
      simp only [add_zero] at hR
      have hsum := hAA.add hR
      rw [add_zero] at hsum
      refine hsum.congr' ?_
      filter_upwards [eventually_ne_zero_add σ] with x hx
      have iA := integrable_inner_of_memLp (memAc h hh x hx.1) (memAc h' hh' _ hx.2)
      have iR : Integrable (fun c => ⟪cvec s (fun x D => ut h x D - mainD s β ε (bt h) x D) x c,
          cvec s (fun x D => mainD s β ε (bt h') x D) (x + σ) c⟫_ℂ) := by
        refine integrable_inner_of_memLp ?_ (memAc h' hh' _ hx.2)
        exact (memLp_cvec s _ x hx.1).1 ((hG.memU h hh x hx.1).sub (hG.memLp_mainD hh x))
      simp only [gramL]
      rw [← integral_add iA iR]
      refine integral_congr_ae (Eventually.of_forall fun c => ?_)
      simp only [Uc, Ac]
      rw [← cvec_sub, inner_sub_left]
      ring
    · have hR := hG.tendsto_cross hh' hh σ 0
      simp only [add_zero] at hR
      have hRc := ((Complex.continuous_conj.tendsto 0).comp hR)
      simp only [map_zero] at hRc
      have hsum := hAA.add hRc
      rw [add_zero] at hsum
      refine hsum.congr' ?_
      filter_upwards [eventually_ne_zero_add σ] with x hx
      have iA := integrable_inner_of_memLp (memAc h hh x hx.1) (memAc h' hh' _ hx.2)
      have iR : Integrable (fun c => ⟪cvec s (fun x D => mainD s β ε (bt h) x D) x c,
          cvec s (fun x D => ut h' x D - mainD s β ε (bt h') x D) (x + σ) c⟫_ℂ) := by
        refine integrable_inner_of_memLp (memAc h hh x hx.1) ?_
        exact (memLp_cvec s _ _ hx.2).1 ((hG.memU h' hh' _ hx.2).sub (hG.memLp_mainD hh' _))
      simp only [gramL, Function.comp_apply]
      rw [← integral_conj, ← integral_conj]
      simp only [inner_conj_symm]
      rw [← integral_add iA iR]
      refine integral_congr_ae (Eventually.of_forall fun c => ?_)
      simp only [Uc, Ac]
      rw [← cvec_sub, inner_sub_right]
      ring

end propGD

end

end Formalism.FourierDecayAlt.P.PBK
