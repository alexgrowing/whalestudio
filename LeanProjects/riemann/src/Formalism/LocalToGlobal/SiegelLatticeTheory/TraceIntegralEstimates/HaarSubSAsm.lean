import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyInst
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.HaarSubS
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.HJSpanLtZero

noncomputable section

open MeasureTheory Measure NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal

namespace Formalism.L2.S.Pv.HaarSubS

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.EnergyAbs

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Abs

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

private theorem lintegral_comp_of_map_eq {μ : Measure G} {φ : G → G} {g : G → ℝ≥0∞} (hφ : Measurable φ) (hμ : μ.map φ = μ)
    (hg : Measurable g) : ∫⁻ x, g (φ x) ∂μ = ∫⁻ x, g x ∂μ := by
  conv_rhs => rw [← hμ]
  rw [lintegral_map hg hφ]

theorem lint_left {μN μH : Measure G} [SFinite μN] [SFinite μH] {N H : Set G} {n₀ h₀ : G}
    (hn₀ : n₀ ∈ N) (hh₀ : h₀ ∈ H) (hNl : ∀ n ∈ N, μN.map (fun x => n * x) = μN)
    (hHl : ∀ h ∈ H, μH.map (fun x => h * x) = μH)
    (hconj : ∀ h ∈ H, μN.map (fun x => h * x * h⁻¹) = μN)
    (f : G → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ n, ∫⁻ h, f (n₀ * h₀ * (n * h)) ∂μH ∂μN = ∫⁻ n, ∫⁻ h, f (n * h) ∂μH ∂μN := by
  have step1 : ∀ n, ∫⁻ h, f (n₀ * h₀ * (n * h)) ∂μH = ∫⁻ h, f (n₀ * (h₀ * n * h₀⁻¹) * h) ∂μH := by
    intro n
    have e : ∀ h, n₀ * h₀ * (n * h) = n₀ * (h₀ * n * h₀⁻¹) * (h₀ * h) := by
      intro h
      group
    simp_rw [e]
    exact lintegral_comp_of_map_eq (φ := fun x => h₀ * x) (g := fun h => f (n₀ * (h₀ * n * h₀⁻¹) * h))
      (measurable_const_mul h₀) (hHl h₀ hh₀) (hf.comp (measurable_const_mul _))
  have hm1 : Measurable fun n => ∫⁻ h, f (n₀ * n * h) ∂μH := by
    have : Measurable fun p : G × G => f (n₀ * p.1 * p.2) :=
      hf.comp ((measurable_fst.const_mul n₀).mul measurable_snd)
    exact this.lintegral_prod_right'
  have hm2 : Measurable fun n => ∫⁻ h, f (n * h) ∂μH := by
    have : Measurable fun p : G × G => f (p.1 * p.2) := hf.comp (measurable_fst.mul measurable_snd)
    exact this.lintegral_prod_right'
  calc ∫⁻ n, ∫⁻ h, f (n₀ * h₀ * (n * h)) ∂μH ∂μN
      = ∫⁻ n, ∫⁻ h, f (n₀ * (h₀ * n * h₀⁻¹) * h) ∂μH ∂μN := lintegral_congr fun n => step1 n
    _ = ∫⁻ n, ∫⁻ h, f (n₀ * n * h) ∂μH ∂μN :=
        lintegral_comp_of_map_eq (φ := fun x => h₀ * x * h₀⁻¹) (g := fun n => ∫⁻ h, f (n₀ * n * h) ∂μH)
          ((measurable_const_mul h₀).mul_const h₀⁻¹) (hconj h₀ hh₀) hm1
    _ = ∫⁻ n, ∫⁻ h, f (n * h) ∂μH ∂μN :=
        lintegral_comp_of_map_eq (φ := fun x => n₀ * x) (g := fun n => ∫⁻ h, f (n * h) ∂μH)
          (measurable_const_mul n₀) (hNl n₀ hn₀) hm2

theorem lint_right {μN μH : Measure G} [SFinite μN] [SFinite μH] {N H : Set G} {n₀ h₀ : G}
    (hn₀ : n₀ ∈ N) (hh₀ : h₀ ∈ H) (hNr : ∀ n ∈ N, μN.map (fun x => x * n) = μN)
    (hHr : ∀ h ∈ H, μH.map (fun x => x * h) = μH) (hnorm : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N)
    (h0H : μH Hᶜ = 0) (f : G → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ n, ∫⁻ h, f (n * h * (n₀ * h₀)) ∂μH ∂μN = ∫⁻ n, ∫⁻ h, f (n * h) ∂μH ∂μN := by
  have hF : Measurable (Function.uncurry fun n h => f (n * h * (n₀ * h₀))) :=
    hf.comp ((measurable_fst.mul measurable_snd).mul_const _)
  have hG : Measurable (Function.uncurry fun n h => f (n * h)) := hf.comp (measurable_fst.mul measurable_snd)
  have hm3 : Measurable fun h => ∫⁻ n, f (n * h) ∂μN := by
    have : Measurable fun p : G × G => f (p.1 * p.2) := hf.comp (measurable_fst.mul measurable_snd)
    exact this.lintegral_prod_left'
  have hae : ∀ᵐ h ∂μH, h ∈ H := (ae_iff (p := fun a => a ∈ H)).mpr h0H
  calc ∫⁻ n, ∫⁻ h, f (n * h * (n₀ * h₀)) ∂μH ∂μN
      = ∫⁻ h, ∫⁻ n, f (n * h * (n₀ * h₀)) ∂μN ∂μH := lintegral_lintegral_swap hF.aemeasurable
    _ = ∫⁻ h, ∫⁻ n, f (n * (h * h₀)) ∂μN ∂μH := by
        apply lintegral_congr_ae
        filter_upwards [hae] with h hh
        have hm : h * n₀ * h⁻¹ ∈ N := hnorm h hh n₀ hn₀
        have e : ∀ n, n * h * (n₀ * h₀) = n * (h * n₀ * h⁻¹) * (h * h₀) := by
          intro n
          group
        simp_rw [e]
        exact lintegral_comp_of_map_eq (φ := fun x => x * (h * n₀ * h⁻¹)) (g := fun n => f (n * (h * h₀)))
          (measurable_mul_const _) (hNr _ hm) (hf.comp (measurable_mul_const _))
    _ = ∫⁻ h, ∫⁻ n, f (n * h) ∂μN ∂μH :=
        lintegral_comp_of_map_eq (φ := fun x => x * h₀) (g := fun h => ∫⁻ n, f (n * h) ∂μN)
          (measurable_mul_const _) (hHr h₀ hh₀) hm3
    _ = ∫⁻ n, ∫⁻ h, f (n * h) ∂μH ∂μN := (lintegral_lintegral_swap hG.aemeasurable).symm

theorem lint_inv {μN μH : Measure G} [SFinite μN] [SFinite μH] {H : Set G}
    (hNi : μN.map (fun x => x⁻¹) = μN) (hHi : μH.map (fun x => x⁻¹) = μH)
    (hconj : ∀ h ∈ H, μN.map (fun x => h * x * h⁻¹) = μN) (hinvH : ∀ h ∈ H, h⁻¹ ∈ H)
    (h0H : μH Hᶜ = 0) (f : G → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ n, ∫⁻ h, f ((n * h)⁻¹) ∂μH ∂μN = ∫⁻ n, ∫⁻ h, f (n * h) ∂μH ∂μN := by
  have hF : Measurable (Function.uncurry fun n h => f ((n * h)⁻¹)) :=
    hf.comp ((measurable_fst.mul measurable_snd).inv)
  have hG : Measurable (Function.uncurry fun n h => f (n * h)) := hf.comp (measurable_fst.mul measurable_snd)
  have hm3 : Measurable fun h => ∫⁻ n, f (n * h) ∂μN := by
    have : Measurable fun p : G × G => f (p.1 * p.2) := hf.comp (measurable_fst.mul measurable_snd)
    exact this.lintegral_prod_left'
  have hae : ∀ᵐ h ∂μH, h ∈ H := (ae_iff (p := fun a => a ∈ H)).mpr h0H
  calc ∫⁻ n, ∫⁻ h, f ((n * h)⁻¹) ∂μH ∂μN
      = ∫⁻ h, ∫⁻ n, f ((n * h)⁻¹) ∂μN ∂μH := lintegral_lintegral_swap hF.aemeasurable
    _ = ∫⁻ h, ∫⁻ n, f (n * h⁻¹) ∂μN ∂μH := by
        apply lintegral_congr_ae
        filter_upwards [hae] with h hh
        have e : ∀ n, (n * h)⁻¹ = h⁻¹ * n⁻¹ * h⁻¹⁻¹ * h⁻¹ := by
          intro n
          group
        simp_rw [e]
        rw [lintegral_comp_of_map_eq (φ := fun x => x⁻¹) (g := fun n => f (h⁻¹ * n * h⁻¹⁻¹ * h⁻¹))
          measurable_inv hNi (hf.comp (((measurable_const_mul _).mul_const _).mul_const _))]
        exact lintegral_comp_of_map_eq (φ := fun x => h⁻¹ * x * h⁻¹⁻¹) (g := fun n => f (n * h⁻¹))
          ((measurable_const_mul _).mul_const _) (hconj _ (hinvH h hh)) (hf.comp (measurable_mul_const _))
    _ = ∫⁻ h, ∫⁻ n, f (n * h) ∂μN ∂μH :=
        lintegral_comp_of_map_eq (φ := fun x => x⁻¹) (g := fun h => ∫⁻ n, f (n * h) ∂μN) measurable_inv hHi hm3
    _ = ∫⁻ n, ∫⁻ h, f (n * h) ∂μH ∂μN := (lintegral_lintegral_swap hG.aemeasurable).symm

theorem isHaarSub_NH [LocallyCompactSpace G] [T2Space G] {S N H : Set G} {μN μH : Measure G}
    [SigmaFinite μN] [SigmaFinite μH]
    (hSc : IsClosed S) (h1 : (1 : G) ∈ S) (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) (hinv : ∀ a ∈ S, a⁻¹ ∈ S)
    (hHc : IsCompact H) (hHinv : ∀ h ∈ H, h⁻¹ ∈ H) (hnorm : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N)
    (hNH : ∀ n ∈ N, ∀ h ∈ H, n * h ∈ S) (hdec : ∀ s ∈ S, ∃ n ∈ N, ∃ h ∈ H, s = n * h)
    (hN0 : μN ≠ 0) (hNc : μN Nᶜ = 0) (hNl : ∀ n ∈ N, μN.map (fun x => n * x) = μN)
    (hH0 : μH ≠ 0) (hHcc : μH Hᶜ = 0) (hHl : ∀ h ∈ H, μH.map (fun x => h * x) = μH)
    (hNk : ∀ K : Set G, IsCompact K → μN K < ⊤) (hNr : ∀ n ∈ N, μN.map (fun x => x * n) = μN)
    (hNi : μN.map (fun x => x⁻¹) = μN) (hconj : ∀ h ∈ H, μN.map (fun x => h * x * h⁻¹) = μN)
    (hHf : IsFiniteMeasure μH) (hHr : ∀ h ∈ H, μH.map (fun x => x * h) = μH)
    (hHi : μH.map (fun x => x⁻¹) = μH) :
    IsHaarSub S ((μN.prod μH).map (fun p => p.1 * p.2)) := by
  haveI := hHf
  have hmul_m : Measurable fun p : G × G => p.1 * p.2 := measurable_fst.mul measurable_snd
  have key : ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ x, f x ∂((μN.prod μH).map (fun p => p.1 * p.2)) = ∫⁻ n, ∫⁻ h, f (n * h) ∂μH ∂μN := by
    intro f hf
    rw [lintegral_map hf hmul_m]
    exact lintegral_prod _ (hf.comp hmul_m).aemeasurable
  have hcpt : ∀ K : Set G, IsCompact K → (μN.prod μH).map (fun p => p.1 * p.2) K < ⊤ := by
    intro K hK
    rw [Measure.map_apply hmul_m hK.isClosed.measurableSet]
    have hTc : IsCompact ((fun p : G × G => p.1 * p.2⁻¹) '' (K ×ˢ H)) :=
      (hK.prod hHc).image (continuous_fst.mul continuous_snd.inv)
    have hsub : (fun p : G × G => p.1 * p.2) ⁻¹' K ⊆
        ((fun p : G × G => p.1 * p.2⁻¹) '' (K ×ˢ H)) ×ˢ H ∪ Set.univ ×ˢ Hᶜ := by
      rintro ⟨n, h⟩ hnh
      by_cases hh : h ∈ H
      · left
        exact ⟨⟨(n * h, h), ⟨hnh, hh⟩, by simp⟩, hh⟩
      · right
        exact ⟨Set.mem_univ _, hh⟩
    calc (μN.prod μH) ((fun p : G × G => p.1 * p.2) ⁻¹' K)
        ≤ (μN.prod μH) (((fun p : G × G => p.1 * p.2⁻¹) '' (K ×ˢ H)) ×ˢ H ∪ Set.univ ×ˢ Hᶜ) :=
          measure_mono hsub
      _ ≤ (μN.prod μH) (((fun p : G × G => p.1 * p.2⁻¹) '' (K ×ˢ H)) ×ˢ H) +
            (μN.prod μH) (Set.univ ×ˢ Hᶜ) := measure_union_le _ _
      _ = μN ((fun p : G × G => p.1 * p.2⁻¹) '' (K ×ˢ H)) * μH H + μN Set.univ * μH Hᶜ := by
          rw [Measure.prod_prod, Measure.prod_prod]
      _ < ⊤ := by
          rw [hHcc, mul_zero, add_zero]
          exact ENNReal.mul_lt_top (hNk _ hTc) (measure_lt_top μH H)
  unfold IsHaarSub
  refine ⟨hSc, h1, hmul, hinv, ?_, ?_, ?_, ?_, hcpt, ?_, ?_⟩
  · haveI : IsFiniteMeasureOnCompacts ((μN.prod μH).map (fun p => p.1 * p.2)) := ⟨hcpt⟩
    infer_instance
  · rw [Ne, ← Measure.measure_univ_eq_zero, Measure.map_apply hmul_m MeasurableSet.univ, Set.preimage_univ,
      ← Set.univ_prod_univ, Measure.prod_prod, mul_eq_zero, not_or, Measure.measure_univ_eq_zero,
      Measure.measure_univ_eq_zero]
    exact ⟨hN0, hH0⟩
  · rw [Measure.map_apply hmul_m hSc.measurableSet.compl]
    refine le_antisymm ?_ (by positivity)
    have hsub : (fun p : G × G => p.1 * p.2) ⁻¹' Sᶜ ⊆ Nᶜ ×ˢ Set.univ ∪ Set.univ ×ˢ Hᶜ := by
      rintro ⟨n, h⟩ hnh
      by_cases hn : n ∈ N
      · by_cases hh : h ∈ H
        · exact absurd (hNH n hn h hh) hnh
        · right
          exact ⟨Set.mem_univ _, hh⟩
      · left
        exact ⟨hn, Set.mem_univ _⟩
    calc (μN.prod μH) ((fun p : G × G => p.1 * p.2) ⁻¹' Sᶜ)
        ≤ (μN.prod μH) (Nᶜ ×ˢ Set.univ ∪ Set.univ ×ˢ Hᶜ) := measure_mono hsub
      _ ≤ (μN.prod μH) (Nᶜ ×ˢ Set.univ) + (μN.prod μH) (Set.univ ×ˢ Hᶜ) := measure_union_le _ _
      _ = 0 := by
          rw [Measure.prod_prod, Measure.prod_prod, hNc, hHcc]
          simp
  · intro s hs
    obtain ⟨n₀, hn₀, h₀, hh₀, rfl⟩ := hdec s hs
    apply Measure.ext_of_lintegral
    intro f hf
    exact (lintegral_map hf (measurable_const_mul _)).trans
      ((key (fun a => f (n₀ * h₀ * a)) (hf.comp (measurable_const_mul _))).trans
        ((lint_left hn₀ hh₀ hNl hHl hconj f hf).trans (key f hf).symm))
  · intro s hs
    obtain ⟨n₀, hn₀, h₀, hh₀, rfl⟩ := hdec s hs
    apply Measure.ext_of_lintegral
    intro f hf
    exact (lintegral_map hf (measurable_mul_const _)).trans
      ((key (fun a => f (a * (n₀ * h₀))) (hf.comp (measurable_mul_const _))).trans
        ((lint_right hn₀ hh₀ hNr hHr hnorm hHcc f hf).trans (key f hf).symm))
  · apply Measure.ext_of_lintegral
    intro f hf
    exact (lintegral_map hf measurable_inv).trans
      ((key (fun a => f a⁻¹) (hf.comp measurable_inv)).trans
        ((lint_inv hNi hHi hconj hHinv hHcc f hf).trans (key f hf).symm))

end Abs

section Glob

def FolnerS : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word),
    IsFolner (X.SinfU u) (Formalism.L2.SG.RealObj.muS X u)

theorem isHaarSub_SinfU (hD : SDecomp) (hN : MeasN) (hH : MeasH) {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (u : D.what₂.Word) : IsHaarSub (X.SinfU u) (Formalism.L2.SG.RealObj.muS X u) := by
  obtain ⟨hSc, h1, hmul, hinv, -, -, -, hHc, -, -, hHinv, hnorm, hNH, hdec⟩ := hD D X u
  obtain ⟨hNk, hNr, hNi, hconj⟩ := hN D X u
  obtain ⟨hHf, hHr, hHi⟩ := hH D X u
  obtain ⟨hNsf, hN0, hNc, hNl⟩ := X.muN_haar u
  obtain ⟨hHsf, hH0, hHcc, hHl⟩ := X.muH_haar u
  haveI := hNsf
  haveI := hHsf
  exact isHaarSub_NH hSc h1 hmul hinv hHc hHinv hnorm hNH hdec hN0 hNc hNl hH0 hHcc hHl hNk hNr hNi hconj
    hHf hHr hHi

theorem stepSubG_of (hD : SDecomp) (hN : MeasN) (hH : MeasH) (hF : FolnerS) (hQ : NuQSFinite) :
    Formalism.L2.SG.RealObj.EnergyInst.StepSubG := by
  intro D X u
  exact ⟨isHaarSub_SinfU hD hN hH X u, hF D X u, Formalism.L2.S.Pv.TauS.tauU_one (X := X) u,
    Formalism.L2.S.Pv.TauS.tauU_mul (X := X) u, hQ D X u⟩

end Glob

end Formalism.L2.S.Pv.HaarSubS
