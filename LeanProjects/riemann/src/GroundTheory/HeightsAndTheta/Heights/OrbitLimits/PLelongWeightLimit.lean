import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StLelongWeightLimit
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StLelongWeightDiff
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffDominated
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial Filter Topology Matrix Set
open scoped ContDiff Manifold
open GroundTheory.Heights₂.Heights (varInt chartInt SmoothNear localMult linEval linForm logReg contDiff_linEval
  contDiff_logReg smoothNear_of_contDiff)

namespace LelongWeightLimit

variable {n : ℕ}

theorem exists_contDiff_eqOn {Z : Set (Fin n → ℂ)} (hZ : IsClosed Z) {f : (Fin n → ℂ) → ℝ}
    (hf : SmoothNear Z f) (hfc : HasCompactSupport f) :
    ∃ g : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ ∀ x ∈ Z, g x = f x := by
  obtain ⟨U, hU, hZU, hfU⟩ := hf
  have hK : IsCompact (Z ∩ tsupport f) := hfc.isCompact.inter_left hZ
  obtain ⟨V, hV, hKV, hVU, -⟩ :=
    exists_open_between_and_isCompact_closure hK hU (inter_subset_left.trans hZU)
  obtain ⟨θ, hθ, -, hθs, hθ1⟩ :=
    exists_contMDiff_support_eq_eq_one_iff 𝓘(ℝ, Fin n → ℂ) (n := ⊤) hV hK.isClosed hKV
  rw [contMDiff_iff_contDiff] at hθ
  refine ⟨θ * f, ?_, hfc.mul_left, fun x hx => ?_⟩
  · refine contDiff_iff_contDiffAt.mpr fun x => ?_
    by_cases hx : x ∈ U
    · exact hθ.contDiffAt.mul (hfU.contDiffAt (hU.mem_nhds hx))
    · have hev : θ * f =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds fun h => hx (hVU h)] with y hy
        have : θ y = 0 := by
          by_contra h
          exact hy (subset_closure (hθs ▸ (Function.mem_support.mpr h)))
        simp [this]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  · by_cases hxf : x ∈ tsupport f
    · rw [Pi.mul_apply, (hθ1 x).1 ⟨hx, hxf⟩, one_mul]
    · rw [Pi.mul_apply, image_eq_zero_of_notMem_tsupport hxf, mul_zero]

theorem varInt_congr {J : Ideal (MvPolynomial (Fin n) ℂ)} {d : ℕ} {f g : (Fin n → ℂ) → ℝ}
    (h : ∀ x ∈ ComplexSets.zeroSet J, f x = g x) (φ : Fin d → (Fin n → ℂ) → ℝ) :
    varInt J d f φ = varInt J d g φ := by
  unfold varInt chartInt
  split_ifs
  · rw [CutOffDominated.chartDens_congr_zeroSet h]
  · rfl

theorem smoothNear_weight {Z : Set (Fin n → ℂ)} (u : Fin n → ℂ) {k : (Fin n → ℂ) → ℝ}
    (hk : SmoothNear Z k) (hk0 : ∀ x ∈ Z, 0 < k x) {ε : ℝ} (hε : 0 < ε) :
    SmoothNear Z (fun x => Real.log (‖linEval u x‖ ^ 2 + ε * k x ^ 2) / 2) := by
  obtain ⟨U, hU, hZU, hkU⟩ := hk
  refine ⟨U ∩ k ⁻¹' Ioi 0, hkU.continuousOn.isOpen_inter_preimage hU isOpen_Ioi,
    fun x hx => ⟨hZU hx, hk0 x hx⟩, ?_⟩
  refine ContDiffOn.div_const (ContDiffOn.log ?_ fun x hx => ?_) _
  · exact ((contDiff_norm_sq ℝ).comp (contDiff_linEval u)).contDiffOn.add
      (contDiffOn_const.mul ((hkU.mono inter_subset_left).pow 2))
  · have h1 : 0 < ε * k x ^ 2 := mul_pos hε (pow_pos hx.2 2)
    have h2 : 0 ≤ ‖linEval u x‖ ^ 2 := sq_nonneg _
    exact (by linarith : (0 : ℝ) < ‖linEval u x‖ ^ 2 + ε * k x ^ 2).ne'

end LelongWeightLimit

open LelongWeightLimit in

theorem LelongWeightLimit.proof (hL : GroundTheory.Heights₂.Heights.LelongLimit.Statement)
    (hS : GroundTheory.Heights₂.Heights.StokesOnVariety.Statement) (hD : LelongWeightDiff.Statement) :
    LelongWeightLimit.Statement := by
  intro n d J u f k φ hJ hdim hu hf hfc hφ hk hk0
  obtain ⟨g, hg, hgc, hgf⟩ :=
    exists_contDiff_eqOn (GroundTheory.Heights₂.Heights.SheetSumMeasurable.isClosed_zeroSet J) hf hfc
  have hsum : (∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ)) (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
        (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d g φ) =
      ∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ)) (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
        (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d f φ := by
    refine finsum_congr fun W => finsum_congr fun hW => ?_
    rw [varInt_congr (fun x hx => hgf x fun q hq => hx q (le_sup_left.trans hW.1.2 hq)) φ]
  have hlim := (hL n d J u g φ hJ hdim hu hg hgc hφ).add (hD n d J u g k φ hJ hdim hu hg hgc hφ hk hk0)
  rw [hsum, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [varInt_congr (fun x hx => (hgf x hx).symm) (vecCons _ φ),
    hS n d J g _ φ hJ hdim (smoothNear_of_contDiff hg) (smoothNear_weight u hk hk0 hε) hφ (Or.inl hgc),
    hS n d J g (logReg u ε) φ hJ hdim (smoothNear_of_contDiff hg)
      (smoothNear_of_contDiff (contDiff_logReg u hε)) hφ (Or.inl hgc)]
  ring

end GroundTheory.Heights₂.Heights.Targets
