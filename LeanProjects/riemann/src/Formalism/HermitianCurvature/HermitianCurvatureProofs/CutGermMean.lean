import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PairingTriangular
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AverageOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MeanBoundsLimits

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.crystallineComparison Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal InnerProductSpace

noncomputable section

open Classical

theorem meanInf_le_limsup {f : ℕ} (Λ : AddSubgroup (V f)) (LIM : (Λ → ℂ) → ℂ) (hL : IsMeanInf Λ LIM)
    (g : Λ → ℂ) (hg : Bdd g) :
    (‖LIM g‖₊ : ℝ≥0∞) ≤
      limsup (fun x : Λ => (‖g x‖₊ : ℝ≥0∞)) (Filter.comap (fun x : Λ => (x : V f)) (atInfAll f)) := by
  refine le_of_forall_gt_imp_ge_of_dense fun b hb => ?_
  by_cases hbt : b = ⊤
  · rw [hbt]; exact le_top
  have hev := Filter.eventually_lt_of_limsup_lt hb
  set B : ℝ := b.toReal with hB
  obtain ⟨Bg, hBg⟩ := hg
  set g₁ : Λ → ℂ := fun x => if ‖g x‖ ≤ B then g x else 0 with hg₁
  set g₂ : Λ → ℂ := fun x => g x - g₁ x with hg₂
  have hb1 : Bdd g₁ := ⟨max B 0, fun x => by
    simp only [hg₁]; split_ifs with h
    · exact h.trans (le_max_left _ _)
    · simp⟩
  have hb2 : Bdd g₂ := ⟨Bg + max B 0, fun x => by
    simp only [hg₂]
    refine (norm_sub_le _ _).trans (add_le_add (hBg x) ?_)
    simp only [hg₁]; split_ifs with h
    · exact h.trans (le_max_left _ _)
    · simp⟩
  have hz : Tendsto g₂ (Filter.comap (fun x : Λ => (x : V f)) (atInfAll f)) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with x hx
    have hx' : ‖g x‖ ≤ B :=
      (ENNReal.ofReal_le_iff_le_toReal hbt).1 (by rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm] at hx; exact hx.le)
    simp [hg₂, hg₁, hx']
  have hsplit : g = g₁ + g₂ := by
    funext x; simp [hg₂]
  have h0 : LIM g₂ = 0 := hL.2 g₂ hb2 hz
  have hLg : LIM g = LIM g₁ := by
    rw [hsplit, hL.1.1 g₁ g₂ hb1 hb2, h0, add_zero]
  have hle : ‖LIM g₁‖ ≤ max B 0 := Formalism.FourierDecayAlt.P.mean_bound_estimate Λ LIM g₁ (max B 0) hL.1 fun x => by
    simp only [hg₁]; split_ifs with h
    · exact h.trans (le_max_left _ _)
    · simp
  rw [hLg]
  have hB0 : max B 0 = B := max_eq_left ENNReal.toReal_nonneg
  rw [hB0] at hle
  calc (‖LIM g₁‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖LIM g₁‖ := by rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
    _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal hle
    _ = b := by rw [hB, ENNReal.ofReal_toReal hbt]

def bD {f : ℕ} (La : Submodule ℤ (V f)) [DiscreteTopology La] [IsZLattice ℝ La] :
    Module.Basis (Fin (Module.finrank ℤ La)) ℝ (V f) :=
  (Pi.basisFun ℝ (Fin (Module.finrank ℤ La))).map (PairingConjugationLemmas.Le La).symm

theorem dual_sub_span {f : ℕ} (La : Submodule ℤ (V f)) [DiscreteTopology La] [IsZLattice ℝ La] (σ : V f)
    (hσ : σ ∈ dualSet La) : σ ∈ Submodule.span ℤ (Set.range (bD La)) := by
  obtain ⟨m, rfl⟩ := PairingConjugationLemmas.ψd_surj La σ hσ
  have hrep : ∀ j, (bD La).repr (PairingConjugationLemmas.ψd La m) j = (m j : ℝ) := by
    intro j
    simp [bD, PairingConjugationLemmas.ψd]
  rw [← (bD La).sum_repr (PairingConjugationLemmas.ψd La m)]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [hrep j, Int.cast_smul_eq_zsmul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

example {f : ℕ} (La : Submodule ℤ (V f)) [DiscreteTopology La] [IsZLattice ℝ La] :
    ∃ LIM : ((Submodule.span ℤ (Set.range (bD La))).toAddSubgroup → ℂ) → ℂ,
      IsMeanInf (Submodule.span ℤ (Set.range (bD La))).toAddSubgroup LIM :=
  Formalism.FourierDecayAlt.P.invariantMeanExists f _

theorem inDual_neg {ω₁ ω₂ σ : ℂ} (h : TBB.InDual ω₁ ω₂ σ) : TBB.InDual ω₁ ω₂ (-σ) := by
  intro a b
  have h1 := h (-a) (-b)
  have e : P5.fsv (-σ) ((a : ℂ) * ω₁ + (b : ℂ) * ω₂) =
      P5.fsv σ (((-a : ℤ) : ℂ) * ω₁ + ((-b : ℤ) : ℂ) * ω₂) := by
    simp only [P5.fsv, map_neg, map_add, map_mul, Int.cast_neg]
    congr 1
    ring
  rw [e, h1]

theorem pdDual_of_pdOn (ω₁ ω₂ : ℂ) (T : Set (V 1)) (A0 : V 1 → ℂ) (hA0 : PDOn T A0) (φ : ℂ → V 1)
    (hφ : Function.Injective φ) (hlin : ∀ a b, φ (a - b) = φ a - φ b)
    (hmem : ∀ σ, TBB.InDual ω₁ ω₂ σ → φ σ ∈ T) (c0 : ℝ) (hc0 : 0 ≤ c0) :
    PDDual ω₁ ω₂ (fun σ => (c0 : ℂ) * A0 (φ σ)) := by
  classical
  intro S c hS
  have hinv : ∀ σ, Function.invFun φ (φ σ) = σ := Function.leftInverse_invFun hφ
  have h0 := hA0 (S.image φ) (fun τ => c (Function.invFun φ τ)) (by
    intro τ hτ
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hτ
    exact hmem σ (hS σ hσ))
  simp only [Finset.sum_image hφ.injOn] at h0
  have e : (∑ σ ∈ S, ∑ σ' ∈ S, (c0 : ℂ) * A0 (φ (σ - σ')) * c σ * conj (c σ')) =
      (c0 : ℂ) * ∑ σ ∈ S, ∑ σ' ∈ S,
        A0 (φ σ - φ σ') * c (Function.invFun φ (φ σ)) * conj (c (Function.invFun φ (φ σ'))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ' _ => ?_
    rw [hinv, hinv, hlin]
    ring
  show 0 ≤ (∑ σ ∈ S, ∑ σ' ∈ S, (c0 : ℂ) * A0 (φ (σ - σ')) * c σ * conj (c σ')).re
  rw [e, Complex.re_ofReal_mul]
  exact mul_nonneg hc0 h0

section vec

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {s : ℕ} {β ε' : ℂ}
  {ut : ℂ → ℂ → H} {bt : ℂ → H} {SS : ℝ}

def uL (hG : PBK.GermD s β ε' ({()} : Finset Unit) (fun _ => ut) (fun _ => bt) SS) (x : ℂ) :
    Lp H 2 (volume : Measure ℂ) :=
  if hx : x ≠ 0 then
    ((PBK.memLp_cvec s ut x hx).1 (hG.memU () (Finset.mem_singleton_self _) x hx)).toLp (PBK.cvec s ut x)
  else 0

def aL (hG : PBK.GermD s β ε' ({()} : Finset Unit) (fun _ => ut) (fun _ => bt) SS) (x : ℂ) :
    Lp H 2 (volume : Measure ℂ) :=
  if hx : x ≠ 0 then
    ((PBK.memLp_cvec s (fun x D => PBK.mainD s β ε' bt x D) x hx).1
      (hG.memLp_mainD (Finset.mem_singleton_self ()) x)).toLp (PBK.cvec s (fun x D => PBK.mainD s β ε' bt x D) x)
  else 0

variable (hG : PBK.GermD s β ε' ({()} : Finset Unit) (fun _ => ut) (fun _ => bt) SS)

theorem inner_uL_uL {x x' : ℂ} (hx : x ≠ 0) (hx' : x' ≠ 0) :
    ⟪uL hG x, uL hG x'⟫_ℂ =
      PBK.gramL volume (PBK.Uc s fun _ => ut) (PBK.Uc s fun _ => ut) ((), x) ((), x') := by
  simp only [uL, aL, dif_pos hx, dif_pos hx']
  rw [MeasureTheory.L2.inner_def, PBK.gramL]
  refine integral_congr_ae ?_
  filter_upwards [((PBK.memLp_cvec s ut x hx).1 (hG.memU () (Finset.mem_singleton_self _) x hx)).coeFn_toLp, ((PBK.memLp_cvec s ut x' hx').1 (hG.memU () (Finset.mem_singleton_self _) x' hx')).coeFn_toLp] with D h1 h2
  rw [h1, h2]
  rfl

theorem inner_uL_aL {x x' : ℂ} (hx : x ≠ 0) (hx' : x' ≠ 0) :
    ⟪uL hG x, aL hG x'⟫_ℂ =
      PBK.gramL volume (PBK.Uc s fun _ => ut) (PBK.Ac s β ε' fun _ => bt) ((), x) ((), x') := by
  simp only [uL, aL, dif_pos hx, dif_pos hx']
  rw [MeasureTheory.L2.inner_def, PBK.gramL]
  refine integral_congr_ae ?_
  filter_upwards [((PBK.memLp_cvec s ut x hx).1 (hG.memU () (Finset.mem_singleton_self _) x hx)).coeFn_toLp, ((PBK.memLp_cvec s (fun x D => PBK.mainD s β ε' bt x D) x' hx').1
      (hG.memLp_mainD (Finset.mem_singleton_self ()) x')).coeFn_toLp] with D h1 h2
  rw [h1, h2]
  rfl

theorem inner_aL_aL {x x' : ℂ} (hx : x ≠ 0) (hx' : x' ≠ 0) :
    ⟪aL hG x, aL hG x'⟫_ℂ =
      PBK.gramL volume (PBK.Ac s β ε' fun _ => bt) (PBK.Ac s β ε' fun _ => bt) ((), x) ((), x') := by
  simp only [uL, aL, dif_pos hx, dif_pos hx']
  rw [MeasureTheory.L2.inner_def, PBK.gramL]
  refine integral_congr_ae ?_
  filter_upwards [((PBK.memLp_cvec s (fun x D => PBK.mainD s β ε' bt x D) x hx).1
      (hG.memLp_mainD (Finset.mem_singleton_self ()) x)).coeFn_toLp, ((PBK.memLp_cvec s (fun x D => PBK.mainD s β ε' bt x D) x' hx').1
      (hG.memLp_mainD (Finset.mem_singleton_self ()) x')).coeFn_toLp] with D h1 h2
  rw [h1, h2]
  rfl

theorem norm_sq_of_inner {v : Lp H 2 (volume : Measure ℂ)} {C : ℝ} (h : ‖⟪v, v⟫_ℂ‖ ≤ C) : ‖v‖ ≤ √C := by
  have h2 : ‖v‖ ^ 2 ≤ C := by
    have e : ‖⟪v, v⟫_ℂ‖ = ‖v‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]
      simp
    linarith
  calc ‖v‖ = √(‖v‖ ^ 2) := (Real.sqrt_sq (norm_nonneg v)).symm
    _ ≤ √C := Real.sqrt_le_sqrt h2

theorem norm_uL_le (x : ℂ) : ‖uL hG x‖ ≤ √SS := by
  by_cases hx : x = 0
  · simp [uL, hx]
  · refine norm_sq_of_inner ?_
    rw [inner_uL_uL hG hx hx, PBK.gramL]
    refine (norm_integral_le_integral_norm _).trans ?_
    have e : ∀ D, ‖⟪PBK.Uc s (fun _ => ut) ((), x) D, PBK.Uc s (fun _ => ut) ((), x) D⟫_ℂ‖ =
        ‖PBK.cvec s ut x D‖ ^ 2 := by
      intro D
      rw [inner_self_eq_norm_sq_to_K]
      simp [PBK.Uc]
    simp_rw [e]
    rw [PBK.integral_norm_cvec_sq s ut x hx]
    exact hG.sup () (Finset.mem_singleton_self _) x hx

theorem norm_aL_le {B' : ℝ} (hB : ∀ x : ℂ, x ≠ 0 →
    ‖PBK.gramL volume (PBK.Ac s β ε' fun _ => bt) (PBK.Ac s β ε' fun _ => bt) ((), x) ((), x)‖ ≤ B') (x : ℂ) :
    ‖aL hG x‖ ≤ √B' := by
  by_cases hx : x = 0
  · simp [aL, hx]
  · exact norm_sq_of_inner (by rw [inner_aL_aL hG hx hx]; exact hB x hx)

end vec

theorem enn_nnnorm (z : ℂ) : (‖z‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖z‖ := by
  rw [ENNReal.ofReal]
  congr 1
  ext
  simp

theorem limsup_link {α : Type} {F : Filter α} (g : α → ℂ) (m : α → ℂ) (Nk : ℂ → ℂ → ℂ) (σ : ℂ) (κ₁ : ℝ)
    (hκ₁ : 0 ≤ κ₁) (hm : Tendsto m F (𝓝[≠] 0))
    (he : ∀ᶠ x in F, ‖Nk (m x) ((m x)⁻¹ + σ)⁻¹‖ = κ₁ * ‖g x‖) :
    ENNReal.ofReal κ₁ * limsup (fun x => (‖g x‖₊ : ℝ≥0∞)) F ≤
      limsup (fun t : ℂ => (‖Nk t (t⁻¹ + σ)⁻¹‖₊ : ℝ≥0∞)) (𝓝[≠] 0) := by
  have heq : (fun x => (‖Nk (m x) ((m x)⁻¹ + σ)⁻¹‖₊ : ℝ≥0∞)) =ᶠ[F]
      fun x => ENNReal.ofReal κ₁ * (‖g x‖₊ : ℝ≥0∞) := by
    filter_upwards [he] with x hx
    rw [enn_nnnorm, enn_nnnorm, hx, ENNReal.ofReal_mul hκ₁]
  rw [← ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top, ← limsup_congr heq]
  calc limsup (fun x => (‖Nk (m x) ((m x)⁻¹ + σ)⁻¹‖₊ : ℝ≥0∞)) F
      = limsup (fun t : ℂ => (‖Nk t (t⁻¹ + σ)⁻¹‖₊ : ℝ≥0∞)) (map m F) :=
        Filter.limsup_comp (fun t : ℂ => (‖Nk t (t⁻¹ + σ)⁻¹‖₊ : ℝ≥0∞)) m F
    _ ≤ _ := limsup_le_limsup_of_le hm

theorem tendsto_inv_shift {α : Type} {F : Filter α} (X : α → ℂ) (δ : ℂ) (hX : Tendsto X F (cocompact ℂ)) :
    Tendsto (fun x => (X x + δ)⁻¹) F (𝓝[≠] 0) := by
  have hn : Tendsto (fun x => ‖X x‖) F atTop := tendsto_norm_cocompact_atTop.comp hX
  have hY : Tendsto (fun x => ‖X x + δ‖) F atTop := by
    refine tendsto_atTop_mono (fun x => ?_) (tendsto_atTop_add_const_right _ (-‖δ‖) hn)
    have := norm_sub_norm_le (X x) (-δ)
    rw [norm_neg, sub_neg_eq_add] at this
    linarith
  rw [tendsto_nhdsWithin_iff]
  constructor
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [norm_inv]
    exact hY.inv_tendsto_atTop
  · filter_upwards [hY.eventually_gt_atTop 0] with x hx
    simpa using norm_pos_iff.mp hx

theorem germ_mean_property : PropGMean := by
  intro H _ _ _ s β ε' η ut bt SS κ₁ κ₂ E Nk hs hκ₂ hκ hη hGD hpsi hNk hE
  have hmem : () ∈ ({()} : Finset Unit) := Finset.mem_singleton_self _
  obtain ⟨hb, -, ⟨B', hB'⟩, hlim⟩ := PBK.GermD.propG hGD
  have hbz : MemLp (PBK.bz s bt) 2 volume := (hb () hmem).1
  have hsq : Integrable (fun z => ‖PBK.bz s bt z‖ ^ 2) := (memLp_two_iff_integrable_sq_norm hbz.1).1 hbz
  have hae : ∀ᵐ z : ℂ, z ≠ 0 := by
    rw [ae_iff]
    simp [measure_singleton]
  have hEae : (fun z => κ₂ * ‖PBK.bz s bt z‖ ^ 2) =ᵐ[volume] E := by
    filter_upwards [hae] with z hz
    exact (hE z hz).symm
  have hEint : Integrable E := (hsq.const_mul κ₂).congr hEae
  refine ⟨hEint, fun ω₁ ω₂ hω => ?_⟩
  have hpi : 0 < Real.pi := Real.pi_pos

  set Nh : ℂ → ℂ := fun σ => PBK.Nhat s β (fun _ => bt) σ () () with hNh
  have hT : ∀ σ : ℂ, (Real.pi⁻¹ : ℂ) * (∫ z, P5.fsv σ z * (E z : ℂ)) =
      ((κ₂ / Real.pi : ℝ) : ℂ) * Nh (η * σ) := by
    intro σ
    have e0 : Nh (η * σ) = ∫ z, G.psi β (η * σ * z) • ⟪PBK.bz s bt z, PBK.bz s bt z⟫_ℂ := rfl
    have e1 : (∫ z, P5.fsv σ z * (E z : ℂ)) =
        (κ₂ : ℂ) * ∫ z, G.psi β (η * σ * z) • ⟪PBK.bz s bt z, PBK.bz s bt z⟫_ℂ := by
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [hae] with z hz
      have hin : ⟪PBK.bz s bt z, PBK.bz s bt z⟫_ℂ = ((‖PBK.bz s bt z‖ ^ 2 : ℝ) : ℂ) := by
        rw [inner_self_eq_norm_sq_to_K]; norm_cast
      rw [hE z hz, hpsi, hin, smul_eq_mul]
      push_cast
      ring
    rw [e1, e0]
    push_cast
    ring

  set La := Submodule.span ℤ (Set.range (TBBx5.lp_b ω₁ ω₂ hω)) with hLa
  set Λs := Submodule.span ℤ (Set.range (bD La)) with hΛs
  obtain ⟨LIM, hLIM⟩ := Formalism.FourierDecayAlt.P.invariantMeanExists 1 Λs
  set X : V 1 → ℂ := fun y => 2 * Real.pi * Complex.I * y 0 with hX
  have hXadd : ∀ y y' : V 1, X (y + y') = X y + X y' := by
    intro y y'
    simp only [hX, Pi.add_apply]
    ring
  have hXt : Tendsto X (atInfAll 1) (cocompact ℂ) := by
    have hn0 : Tendsto (fun y : V 1 => ‖y 0‖) (atInfAll 1) atTop := by
      unfold atInfAll
      exact tendsto_iInf' 0 tendsto_comap
    have hn : Tendsto (fun y : V 1 => ‖X y‖) (atInfAll 1) atTop := by
      have e : (fun y : V 1 => ‖X y‖) = fun y => (2 * Real.pi) * ‖y 0‖ := by
        funext y
        simp only [hX, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi,
          Complex.norm_ofNat, mul_one]
      rw [e]
      exact hn0.const_mul_atTop (by positivity)
    refine (Filter.hasBasis_cocompact.tendsto_right_iff).2 fun K hK => ?_
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    filter_upwards [hn.eventually_gt_atTop R] with x hx hxK
    have := hR hxK
    rw [Metric.mem_closedBall, dist_zero_right] at this
    linarith
  have hne : ∀ c : ℂ, ∀ᶠ y in atInfAll 1, X y + c ≠ 0 := by
    intro c
    filter_upwards [hXt (isCompact_singleton (x := -c)).compl_mem_cocompact] with y hy
    exact fun e => hy (Set.mem_singleton_iff.2 (eq_neg_of_add_eq_zero_left e))
  have hne0 : ∀ᶠ y in atInfAll 1, X y ≠ 0 := by
    filter_upwards [hne 0] with y hy
    simpa using hy
  set a : V 1 → Lp H 2 (volume : Measure ℂ) := fun y => aL hGD (X y) with ha
  set u : V 1 → Lp H 2 (volume : Measure ℂ) := fun y => uL hGD (X y) with hu
  set r : V 1 → Lp H 2 (volume : Measure ℂ) := fun y => u y - a y with hr
  have hau : ∀ y, a y + r y = u y := fun y => by simp only [hr]; abel
  have hBa : ∀ y, ‖a y‖ ≤ √B' := fun y => norm_aL_le hGD (fun x hx => hB' () hmem x hx) (X y)
  have hBu : ∀ y, ‖u y‖ ≤ √SS := fun y => norm_uL_le hGD (X y)
  have hbnd : ∀ y, ‖a y‖ ≤ √SS + √B' ∧ ‖r y‖ ≤ √SS + √B' := by
    intro y
    refine ⟨(hBa y).trans (le_add_of_nonneg_left (Real.sqrt_nonneg _)), ?_⟩
    exact (norm_sub_le _ _).trans (add_le_add (hBu y) (hBa y))
  set Nh' : V 1 → ℂ := fun σ => Nh (X σ) with hNh'
  have hAA : ∀ σ ∈ Λs.toAddSubgroup, Tendsto (fun x => ⟪a x, a (x + σ)⟫_ℂ) (atInfAll 1) (𝓝 (Nh' σ)) := by
    intro σ _
    refine ((hlim () hmem () hmem (X σ)).1.comp hXt).congr' ?_
    filter_upwards [hne0, hne (X σ)] with y h1 h2
    simp only [Function.comp_apply, ha, hXadd]
    exact (inner_aL_aL hGD h1 h2).symm
  have hAR : ∀ σ ∈ Λs.toAddSubgroup, Tendsto (fun x => ⟪a x, r (x + σ)⟫_ℂ) (atInfAll 1) (𝓝 0) := by
    intro σ _
    have h3 := ((hlim () hmem () hmem (X σ)).2.2.comp hXt)
    have h1 := ((hlim () hmem () hmem (X σ)).1.comp hXt)
    rw [← sub_self (Nh' σ)]
    refine (h3.sub h1).congr' ?_
    filter_upwards [hne0, hne (X σ)] with y hy1 hy2
    simp only [Function.comp_apply, hr, ha, hu, hXadd, inner_sub_right]
    rw [← inner_aL_aL hGD hy1 hy2, ← inner_uL_aL hGD hy2 hy1, inner_conj_symm]
  have hRA : ∀ σ ∈ Λs.toAddSubgroup, Tendsto (fun x => ⟪r x, a (x + σ)⟫_ℂ) (atInfAll 1) (𝓝 0) := by
    intro σ _
    have h2 := ((hlim () hmem () hmem (X σ)).2.1.comp hXt)
    have h1 := ((hlim () hmem () hmem (X σ)).1.comp hXt)
    rw [← sub_self (Nh' σ)]
    refine (h2.sub h1).congr' ?_
    filter_upwards [hne0, hne (X σ)] with y hy1 hy2
    simp only [Function.comp_apply, hr, ha, hu, hXadd, inner_sub_left]
    rw [← inner_aL_aL hGD hy1 hy2, ← inner_uL_aL hGD hy1 hy2]
  obtain ⟨hsplit, hpd⟩ := Formalism.FourierDecayAlt.P.mean_split_identity 1 Λs.toAddSubgroup LIM (Lp H 2 (volume : Measure ℂ)) a r
    Nh' (√SS + √B') hLIM hbnd hAA hAR hRA
  set A0 : V 1 → ℂ := fun σ => LIM (fun x : Λs.toAddSubgroup => ⟪r x, r ((x : V 1) + σ)⟫_ℂ) with hA0

  have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := TBBx5.lp_ne
  have hη0 : η ≠ 0 := by rcases hη with h | h <;> simp [h]
  set φ : ℂ → V 1 := fun σ => fun _ => η * σ / (2 * Real.pi * Complex.I) with hφ
  have hXφ : ∀ σ, X (φ σ) = η * σ := by
    intro σ
    simp only [hX, hφ]
    field_simp
  have hφmem : ∀ σ, TBB.InDual ω₁ ω₂ σ → φ σ ∈ Λs := by
    intro σ hσ
    refine dual_sub_span La (φ σ) ((TBBx5.lp_dual ω₁ ω₂ hω (φ σ)).2 ?_)
    have e : 2 * Real.pi * Complex.I * φ σ 0 = η * σ := hXφ σ
    rw [e]
    rcases hη with h | h
    · simpa [h] using hσ
    · simpa [h] using inDual_neg hσ
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have := congrFun hxy 0
    simp only [hφ] at this
    have := (div_left_inj' h2pi).1 this
    exact mul_left_cancel₀ hη0 this
  have hφlin : ∀ x y, φ (x - y) = φ x - φ y := by
    intro x y
    funext i
    simp only [hφ, Pi.sub_apply]
    ring
  have hc0 : 0 ≤ κ₂ / Real.pi := div_nonneg hκ₂ hpi.le
  refine ⟨fun σ => ((κ₂ / Real.pi : ℝ) : ℂ) * A0 (φ σ),
    pdDual_of_pdOn ω₁ ω₂ (Λs.toAddSubgroup : Set (V 1)) A0 hpd φ hφinj hφlin hφmem _ hc0, fun σ hσ => ?_⟩

  have hΛφ : φ σ ∈ Λs.toAddSubgroup := hφmem σ hσ
  have hLg := hsplit (φ σ) hΛφ
  simp_rw [hau] at hLg
  set g : Λs.toAddSubgroup → ℂ := fun x => ⟪u x, u ((x : V 1) + φ σ)⟫_ℂ with hg
  have hgB : Bdd g := ⟨√SS * √SS, fun x => (norm_inner_le_norm _ _).trans
    (mul_le_mul (hBu _) (hBu _) (norm_nonneg _) (Real.sqrt_nonneg _))⟩
  have hmean := meanInf_le_limsup Λs.toAddSubgroup LIM hLIM g hgB
  have hsum : (Real.pi⁻¹ : ℂ) * (∫ z, P5.fsv σ z * (E z : ℂ)) + ((κ₂ / Real.pi : ℝ) : ℂ) * A0 (φ σ) =
      ((κ₂ / Real.pi : ℝ) : ℂ) * LIM g := by
    rw [hT σ, hLg, ← hXφ σ]
    ring
  rw [hsum, enn_nnnorm, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0,
    ENNReal.ofReal_mul hc0, ← enn_nnnorm]

  have hκ₁ : 0 ≤ κ₁ := by
    have := hκ₂.trans hκ
    exact nonneg_of_mul_nonneg_right (by linarith) hpi
  have hcle : ENNReal.ofReal (κ₂ / Real.pi) ≤ ENNReal.ofReal κ₁ :=
    ENNReal.ofReal_le_ofReal ((div_le_iff₀ hpi).2 (by linarith))
  set F : Filter Λs.toAddSubgroup := Filter.comap (fun x : Λs.toAddSubgroup => (x : V 1)) (atInfAll 1) with hF
  have hXtF : Tendsto (fun x : Λs.toAddSubgroup => X x) F (cocompact ℂ) := hXt.comp tendsto_comap
  have hneF : ∀ c : ℂ, ∀ᶠ x : Λs.toAddSubgroup in F, X x + c ≠ 0 := fun c => tendsto_comap.eventually (hne c)
  set δ : ℂ := if η = 1 then 0 else -σ with hδ
  have hlink : ∀ᶠ x : Λs.toAddSubgroup in F, ‖Nk ((X x + δ)⁻¹) (((X x + δ)⁻¹)⁻¹ + σ)⁻¹‖ = κ₁ * ‖g x‖ := by
    filter_upwards [hneF δ, hneF (δ + σ), hneF 0, hneF (η * σ)] with x h1 h2 h3 h4
    rw [inv_inv]
    have h3' : X x ≠ 0 := by simpa using h3
    rw [hNk _ _ (inv_ne_zero h1) (inv_ne_zero (by rwa [add_assoc])), inv_inv, inv_inv]
    congr 1
    simp only [hg, hu]
    rw [hXadd, hXφ σ]
    rcases hη with h | h
    · have hd : δ = 0 := by simp [hδ, h]
      simp only [hd, add_zero, h, one_mul]
      rw [inner_uL_uL hGD h3' (by simpa [h] using h4)]
    · have hd : δ = -σ := by rw [hδ, if_neg (by rw [h]; norm_num)]
      simp only [hd, h, neg_one_mul, neg_add_cancel_right]
      have h4' : X x + -σ ≠ 0 := by simpa [h] using h4
      rw [← sub_eq_add_neg, ← inner_uL_uL hGD (by rwa [sub_eq_add_neg]) h3', sub_eq_add_neg, norm_inner_symm]
  have hfin := limsup_link g (fun x => (X x + δ)⁻¹) Nk σ κ₁ hκ₁ (tendsto_inv_shift _ δ hXtF) hlink
  calc ENNReal.ofReal (κ₂ / Real.pi) * (‖LIM g‖₊ : ℝ≥0∞)
      ≤ ENNReal.ofReal κ₁ * limsup (fun x => (‖g x‖₊ : ℝ≥0∞)) F := mul_le_mul' hcle hmean
    _ ≤ _ := hfin

end

end Formalism.FourierDecayAlt.P.CutBP
