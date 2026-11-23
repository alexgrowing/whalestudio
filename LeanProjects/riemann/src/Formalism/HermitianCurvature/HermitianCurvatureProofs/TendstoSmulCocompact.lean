import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermRealisation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LastBlockDecay
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormOfMemRootSetOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TendstoIntegralPsiMoving

namespace Formalism.FourierDecayAlt.P.PBK

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

section main

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def mainD (s : ℕ) (β ε : ℂ) (bt : ℂ → H) (x D : ℂ) : H :=
  ∑ z ∈ G.rootSet s (ε * D), G.psi β ((s : ℂ) * z * x) • bt z

def bz (s : ℕ) (bt : ℂ → H) (z : ℂ) : H := (((s : ℝ) * ‖z‖ ^ (s - 1) : ℝ) : ℂ) • bt z

def pairD (s : ℕ) (β ε : ℂ) (bt bt' : ℂ → H) (x x' ρ : ℂ) : ℂ :=
  ∫ D, ⟪mainD s β ε bt x D, ((‖ρ‖ ^ s : ℝ) : ℂ) • mainD s β ε bt' x' (ρ ^ s * D)⟫_ℂ

theorem psi_conj_mul (β a b : ℂ) : conj (G.psi β a) * G.psi β b = G.psi β (b - a) := by
  unfold G.psi
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, mul_sub, Complex.sub_re]
  push_cast
  ring

def termZ (s : ℕ) (β : ℂ) (bt bt' : ℂ → H) (x x' ρ ζ z : ℂ) : ℂ :=
  G.psi β ((s : ℂ) * (ζ * ρ * x' - x) * z) • ⟪bz s bt z, ((‖ρ‖ : ℝ) : ℂ) • bz s bt' (ζ * ρ * z)⟫_ℂ

theorem integrable_termZ {s : ℕ} (_hs : s ≠ 0) (β : ℂ) {bt bt' : ℂ → H} (hb : MemLp (bz s bt) 2 volume)
    (hb' : MemLp (bz s bt') 2 volume) (x x' ρ ζ : ℂ) (hρ : ρ ≠ 0) (hζ : ζ ≠ 0) :
    Integrable (termZ s β bt bt' x x' ρ ζ) := by
  have hd : MemLp (fun z => ((‖ρ‖ : ℝ) : ℂ) • bz s bt' (ζ * ρ * z)) 2 volume :=
    (memLp_comp_mul hb' (ζ * ρ) (mul_ne_zero hζ hρ)).const_smul _
  have hi := integrable_inner_of_memLp hb hd
  refine hi.bdd_smul 1 ?_ (Eventually.of_forall fun z => (norm_psi β _).le)
  exact ((continuous_psi β).comp (continuous_const.mul continuous_id)).aestronglyMeasurable

theorem pairD_eq {s : ℕ} (hs : s ≠ 0) (β : ℂ) {ε : ℂ} (hε : ‖ε‖ = 1) {bt bt' : ℂ → H}
    (hb : MemLp (bz s bt) 2 volume) (hb' : MemLp (bz s bt') 2 volume) (x x' ρ : ℂ) (hρ : ρ ≠ 0) :
    pairD s β ε bt bt' x x' ρ = ∑ ζ ∈ G.rootSet s 1, ∫ z, termZ s β bt bt' x x' ρ ζ z := by
  have hε0 : ε ≠ 0 := by rintro rfl; simp at hε
  have hζ0 : ∀ ζ ∈ G.rootSet s 1, ζ ≠ 0 := fun ζ hζ h0 => by
    have := norm_of_mem_rootSet_one hs hζ; rw [h0, norm_zero] at this; exact zero_ne_one this

  set Φ : ℂ → ℂ := fun z => ∑ ζ ∈ G.rootSet s 1,
    (conj (G.psi β ((s : ℂ) * z * x)) * G.psi β ((s : ℂ) * (ζ * ρ * z) * x')) *
      (((‖ρ‖ ^ s : ℝ) : ℂ) * ⟪bt z, bt' (ζ * ρ * z)⟫_ℂ) with hΦ
  have hjac : ∀ z : ℂ, ‖ε⁻¹ * ((s : ℂ) * z ^ (s - 1))‖ ^ 2 • Φ z =
      ∑ ζ ∈ G.rootSet s 1, termZ s β bt bt' x x' ρ ζ z := by
    intro z
    rw [hΦ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun ζ hζ => ?_
    have hζn := norm_of_mem_rootSet_one hs hζ
    have hn : ‖ζ * ρ * z‖ = ‖ρ‖ * ‖z‖ := by rw [norm_mul, norm_mul, hζn, one_mul]
    have hj : ‖ε⁻¹ * ((s : ℂ) * z ^ (s - 1))‖ ^ 2 = ((s : ℝ) * ‖z‖ ^ (s - 1)) ^ 2 := by
      rw [norm_mul, norm_inv, hε, inv_one, one_mul, norm_mul, norm_pow, Complex.norm_natCast]
    have hps : conj (G.psi β ((s : ℂ) * z * x)) * G.psi β ((s : ℂ) * (ζ * ρ * z) * x') =
        G.psi β ((s : ℂ) * (ζ * ρ * x' - x) * z) := by
      rw [psi_conj_mul]; congr 1; ring
    have hρs : ‖ρ‖ ^ s = ‖ρ‖ * ‖ρ‖ ^ (s - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [hj, hps]
    simp only [termZ, bz, inner_smul_left, inner_smul_right, Complex.conj_ofReal, smul_eq_mul, hn, hρs, mul_pow,
      Complex.real_smul]
    push_cast
    ring
  have hint : Integrable (fun z => ‖ε⁻¹ * ((s : ℂ) * z ^ (s - 1))‖ ^ 2 • Φ z) := by
    simp_rw [hjac]
    exact integrable_finsetSum _ fun ζ hζ => integrable_termZ hs β hb hb' x x' ρ ζ hρ (hζ0 ζ hζ)
  obtain ⟨-, hch⟩ := integral_sum_rootSet s hs ε hε0 Φ hint

  have hD : ∀ D : ℂ, D ≠ 0 → ⟪mainD s β ε bt x D, ((‖ρ‖ ^ s : ℝ) : ℂ) • mainD s β ε bt' x' (ρ ^ s * D)⟫_ℂ =
      ∑ z ∈ G.rootSet s (ε * D), Φ z := by
    intro D hD0
    rw [inner_smul_right, mainD, sum_inner, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z hz => ?_
    have hzs : z ^ s = ε * D := (mem_rootSet' hs).1 hz
    have hw : ε * D ≠ 0 := mul_ne_zero hε0 hD0
    have hrD : ε * (ρ ^ s * D) = ρ ^ s * (ε * D) := by ring
    rw [mainD, hrD, sum_rootSet_mul hs hw hzs rfl (pow_ne_zero _ hρ), inner_sum, Finset.mul_sum, hΦ]
    refine Finset.sum_congr rfl fun ζ _ => ?_
    rw [inner_smul_left, inner_smul_right]
    ring
  have hDae : (fun D => ⟪mainD s β ε bt x D, ((‖ρ‖ ^ s : ℝ) : ℂ) • mainD s β ε bt' x' (ρ ^ s * D)⟫_ℂ) =ᵐ[volume]
      fun D => ∑ z ∈ G.rootSet s (ε * D), Φ z := by
    filter_upwards [Measure.ae_ne volume (0 : ℂ)] with D hD0
    exact hD D hD0
  rw [pairD, integral_congr_ae hDae, hch]
  simp_rw [hjac]
  exact integral_finsetSum _ fun ζ hζ => integrable_termZ hs β hb hb' x x' ρ ζ hρ (hζ0 ζ hζ)

theorem tendsto_smul_cocompact {α : Type} {l : Filter α} (c : ℂ) (hc : c ≠ 0) (y : α → ℂ)
    (hy : Tendsto y l (cocompact ℂ)) : Tendsto (fun a => c * y a) l (cocompact ℂ) := by
  rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded] at hy ⊢
  simp only [norm_mul]
  exact hy.const_mul_atTop (norm_pos_iff.mpr hc)

theorem tendsto_pairD {s : ℕ} (hs : s ≠ 0) {β : ℂ} (hβ : β ≠ 0) {ε : ℂ} (hε : ‖ε‖ = 1) {bt bt' : ℂ → H}
    (hb : MemLp (bz s bt) 2 volume) (hb' : MemLp (bz s bt') 2 volume) {α : Type} {l : Filter α}
    (x x' ρ : α → ℂ) (σ : ℂ) (hρ0 : ∀ᶠ a in l, ρ a ≠ 0) (hρ : Tendsto ρ l (𝓝 1))
    (hsh : Tendsto (fun a => (s : ℂ) * (ρ a * x' a - x a)) l (𝓝 σ))
    (hne : ∀ ζ ∈ G.rootSet s 1, ζ ≠ 1 → Tendsto (fun a => ζ * ρ a * x' a - x a) l (cocompact ℂ)) :
    Tendsto (fun a => pairD s β ε bt bt' (x a) (x' a) (ρ a)) l
      (𝓝 (∫ z, G.psi β (σ * z) • ⟪bz s bt z, bz s bt' z⟫_ℂ)) := by
  set L : ℂ := ∫ z, G.psi β (σ * z) • ⟪bz s bt z, bz s bt' z⟫_ℂ with hL
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have hlim : ∀ ζ ∈ G.rootSet s 1, Tendsto (fun a => ∫ z, termZ s β bt bt' (x a) (x' a) (ρ a) ζ z) l
      (𝓝 (if ζ = 1 then L else 0)) := by
    intro ζ hζ
    have hζn := norm_of_mem_rootSet_one hs hζ
    have hζ0 : ζ ≠ 0 := fun h0 => by rw [h0, norm_zero] at hζn; exact zero_ne_one hζn
    have hf0 : Integrable (fun z => ⟪bz s bt z, bz s bt' (ζ * z)⟫_ℂ) :=
      integrable_inner_of_memLp hb (memLp_comp_mul hb' ζ hζ0)
    have hfi : ∀ᶠ a in l, Integrable (fun z => ⟪bz s bt z, ((‖ρ a‖ : ℝ) : ℂ) • bz s bt' (ζ * ρ a * z)⟫_ℂ) := by
      filter_upwards [hρ0] with a ha
      exact integrable_inner_of_memLp hb ((memLp_comp_mul hb' (ζ * ρ a) (mul_ne_zero hζ0 ha)).const_smul _)
    have hL1 : Tendsto (fun a => ∫ z, ‖⟪bz s bt z, ((‖ρ a‖ : ℝ) : ℂ) • bz s bt' (ζ * ρ a * z)⟫_ℂ -
        ⟪bz s bt z, bz s bt' (ζ * z)⟫_ℂ‖) l (𝓝 0) := by
      have hζρ : Tendsto (fun a => ζ * ρ a) l (𝓝 ζ) := by
        simpa using (tendsto_const_nhds (x := ζ)).mul hρ
      have h1 := (tendsto_inner_dil (bz s bt) (bz s bt') hb hb' ζ hζ0).comp hζρ
      refine h1.congr fun a => ?_
      simp only [Function.comp_apply, norm_mul, hζn, one_mul, Complex.ofReal_one, one_smul]
    by_cases h1 : ζ = 1
    · subst h1
      rw [if_pos rfl]
      have hw : Tendsto (fun a => (s : ℂ) * (1 * ρ a * x' a - x a)) l (𝓝 σ) := by simpa using hsh
      have := tendsto_integral_psi_conv β _ _ hf0 hfi hL1 _ σ hw
      simpa [termZ, hL] using this
    · rw [if_neg h1]
      have hw := tendsto_smul_cocompact (s : ℂ) hs0 _ (hne ζ hζ h1)
      have := tendsto_integral_psi_moving β hβ _ _ hf0 hfi hL1 _ hw
      simpa [termZ, mul_assoc] using this
  have hsum := tendsto_finsetSum (G.rootSet s 1) hlim
  rw [Finset.sum_ite_eq' (G.rootSet s 1) 1 (fun _ => L), if_pos (one_mem_rootSet_one hs)] at hsum
  refine hsum.congr' ?_
  filter_upwards [hρ0] with a ha
  exact (pairD_eq hs β hε hb hb' (x a) (x' a) (ρ a) ha).symm

end main

end

end Formalism.FourierDecayAlt.P.PBK
