import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticLogResolution
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PshExtensionOffClosedSet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialBoundarySmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryPotentialPshStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundarySublevelClosureComplementStatement
open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt
open scoped ENNReal

namespace GlobalTheory.PoincareTrunc

open Filter Topology
open scoped ContDiff

theorem exists_exact_truncation : ∀ (e : ℕ) (X : Type) [TopologicalSpace X]
    (A : FinHolAtlas e X) (Om : LocPot X) (Z : Set X) (u : X → ℝ) (M : ℝ), 2 ≤ M → IsClosed Z →
    IsPotential A Om → IsPsh A Om → A.SmoothOn Zᶜ u → (∀ x ∈ Zᶜ, u x ≤ 0) →
    (∀ x j, ∀ y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (Om.U x ∩ Zᶜ), ∀ w : Fin e → ℂ,
      0 ≤ levi ((fun z => Om.φ x z + u z) ∘ (A.chart j).symm) y w) →
    (∀ a : ℝ, closure {x | x ∈ Zᶜ ∧ -a ≤ u x} ⊆ Zᶜ) →
    ∃ v : X → ℝ, A.Smooth v ∧ IsPsh A (Om + LocPot.ofFun v) ∧
      (∀ x ∈ Zᶜ, u x ≤ v x ∧ v x ≤ 0) ∧ ∀ x ∈ Zᶜ, -M + 2 ≤ u x → v x = u x := by
  intro e X _ A Om Z u M hM hZ hpot hpsh hsm hneg hlevi hcl
  obtain ⟨m, hmC, hmconv, hmmono, hmb, hm1, hm2, hmtr⟩ :=
    GlobalTheory.RegularisedMaxTwo.exists_regMaxTwo (1 / 4) (by norm_num)
  set c : ℝ := -M + 1 with hc
  set G : ℝ → ℝ := fun t => m (t, c) - 0 with hG
  obtain ⟨hGC, hG1, hG1', hG2⟩ := GlobalTheory.QuasiPshTruncation.regMax_slice hmC hmconv hmmono hmtr c 0
  have hGC2 : ContDiff ℝ 2 G := hGC.of_le GlobalTheory.QuasiPshTruncation.two_le_inf'
  have hGlow : ∀ t, t + 1 / 2 ≤ c → G t = c := by
    intro t ht
    simp only [hG]
    rw [hm2 t c (by linarith)]
    ring
  classical
  let v : X → ℝ := fun x => if x ∈ Z then c else G (u x)
  set K := closure {x | x ∈ Zᶜ ∧ -M ≤ u x} with hKdef
  have hK : K ⊆ Zᶜ := hcl M
  have hKc : IsOpen Kᶜ := isClosed_closure.isOpen_compl
  have hvK : ∀ x ∈ Kᶜ, v x = c := by
    intro x hx
    by_cases hxZ : x ∈ Z
    · simp [v, hxZ]
    · have hux : u x < -M := by
        by_contra h
        push_neg at h
        exact hx (subset_closure ⟨hxZ, h⟩)
      simp only [v, hxZ, if_false]
      exact hGlow _ (by linarith)
  have hvZ : ∀ x ∈ Zᶜ, v x = G (u x) := by
    intro x hx
    have hx' : x ∉ Z := hx
    simp [v, hx']
  refine ⟨v, ?_, ?_, ?_, ?_⟩
  · intro j y hy
    apply ContDiffAt.contDiffWithinAt
    have hyt : y ∈ (A.chart j).target := hy.1
    by_cases hp : (A.chart j).symm y ∈ Z
    · have hO := (A.chart j).isOpen_inter_preimage_symm hKc
      have hyO : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Kᶜ :=
        ⟨hyt, fun h => hK h hp⟩
      have hev : (v ∘ (A.chart j).symm) =ᶠ[𝓝 y] fun _ => c := by
        filter_upwards [hO.mem_nhds hyO] with y' hy' using hvK _ hy'.2
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · have hO := (A.chart j).isOpen_inter_preimage_symm hZ.isOpen_compl
      have hyO : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Zᶜ := ⟨hyt, hp⟩
      have hu : ContDiffAt ℝ ∞ (u ∘ (A.chart j).symm) y := (hsm j).contDiffAt (hO.mem_nhds hyO)
      have hev : (v ∘ (A.chart j).symm) =ᶠ[𝓝 y] G ∘ (u ∘ (A.chart j).symm) := by
        filter_upwards [hO.mem_nhds hyO] with y' hy' using hvZ _ hy'.2
      exact (hGC.contDiffAt.comp y hu).congr_of_eventuallyEq hev
  · intro x j y hy w
    have hyt : y ∈ (A.chart j).target := hy.1
    have hyU : (A.chart j).symm y ∈ Om.U x := hy.2.1
    have hOφ := (A.chart j).isOpen_inter_preimage_symm (Om.isOpen_U x)
    have hφ : ContDiffAt ℝ 2 (Om.φ x ∘ (A.chart j).symm) y :=
      ((hpot.1 x j).contDiffAt (hOφ.mem_nhds ⟨hyt, hyU⟩)).of_le
        GlobalTheory.QuasiPshTruncation.two_le_inf'
    have hφ0 : 0 ≤ levi (Om.φ x ∘ (A.chart j).symm) y w := hpsh x j y ⟨hyt, hyU⟩ w
    show 0 ≤ levi ((fun z => Om.φ x z + v z) ∘ (A.chart j).symm) y w
    by_cases hp : (A.chart j).symm y ∈ Z
    · have hO := (A.chart j).isOpen_inter_preimage_symm hKc
      have hyO : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Kᶜ :=
        ⟨hyt, fun h => hK h hp⟩
      have hev : ((fun z => Om.φ x z + v z) ∘ (A.chart j).symm) =ᶠ[𝓝 y]
          fun z => (Om.φ x ∘ (A.chart j).symm) z + c := by
        filter_upwards [hO.mem_nhds hyO] with y' hy'
        simp only [Function.comp_apply, hvK _ hy'.2]
      rw [levi_congr hev, GlobalTheory.QuasiPshTruncation.levi_add_const]
      exact hφ0
    · have hO := (A.chart j).isOpen_inter_preimage_symm hZ.isOpen_compl
      have hyO : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Zᶜ := ⟨hyt, hp⟩
      have hu : ContDiffAt ℝ 2 (u ∘ (A.chart j).symm) y :=
        ((hsm j).contDiffAt (hO.mem_nhds hyO)).of_le GlobalTheory.QuasiPshTruncation.two_le_inf'
      have hev : ((fun z => Om.φ x z + v z) ∘ (A.chart j).symm) =ᶠ[𝓝 y]
          fun z => (Om.φ x ∘ (A.chart j).symm) z + G ((u ∘ (A.chart j).symm) z) := by
        filter_upwards [hO.mem_nhds hyO] with y' hy'
        simp only [Function.comp_apply, hvZ _ hy'.2]
      rw [levi_congr hev]
      exact GlobalTheory.QuasiPshTruncation.levi_nonneg_add_comp hφ hu hGC2 (hG1 _) (hG1' _) (hG2 _) hφ0
        (hlevi x j y ⟨hyt, hyU, hp⟩ w)
  · intro x hx
    rw [hvZ x hx]
    simp only [hG, sub_zero]
    have hb := hmb (u x) c
    have hu := hneg x hx
    refine ⟨le_trans (le_max_left _ _) hb.1, ?_⟩
    by_cases h : c + 2 * (1 / 4) ≤ u x
    · rw [hm1 (u x) c h]; exact hu
    · push_neg at h
      have : max (u x) c ≤ c + 1 / 2 := max_le (by linarith) (by linarith)
      linarith [hb.2]
  · intro x hx hux
    rw [hvZ x hx]
    simp only [hG, sub_zero]
    rw [hm1 (u x) c (by linarith)]

end GlobalTheory.PoincareTrunc

namespace GlobalTheory.PoincareTrunc

open Filter Topology
open scoped ContDiff

theorem smooth_trunc_of_parts (hsm : ∀ (d : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas d X) (m : ℕ)
    (Λ : Fin m → LocPot X) (σ : Fin m → X → X → ℂ) (c : ℝ),
    (∀ i, IsPotential A (Λ i) ∧ IsSection A (Λ i) (σ i) ∧ ∀ y, normSec (Λ i) (σ i) y ≤ 1) →
    IsClosed (boundary σ) ∧ A.SmoothOn (boundary σ)ᶜ (fun y => pFun Λ σ c y / 2)) (hlv : ∀ (d : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas d X) (m : ℕ) (α : LocPot X)
    (Λ : Fin m → LocPot X) (σ : Fin m → X → X → ℂ) (c : ℝ),
    IsBoundarySetting A α Λ σ c →
    ∀ (x : X) (j : Fin A.n), ∀ y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (α.U x ∩ (boundary σ)ᶜ),
      ∀ w : Fin d → ℂ, 0 ≤ levi ((fun z => α.φ x z + pFun Λ σ c z / 2) ∘ (A.chart j).symm) y w) (hbt : ∀ (d : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas d X) (m : ℕ) (α : LocPot X)
    (Λ : Fin m → LocPot X) (σ : Fin m → X → X → ℂ) (c : ℝ),
    IsBoundarySetting A α Λ σ c →
    ∀ a : ℝ, closure {x | x ∈ (boundary σ)ᶜ ∧ -a ≤ pFun Λ σ c x / 2} ⊆ (boundary σ)ᶜ) : ∀ (d : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas d X) (m : ℕ) (α : LocPot X) (Λ : Fin m → LocPot X) (σ : Fin m → X → X → ℂ) (c : ℝ),
    IsBoundarySetting A α Λ σ c →
    ∃ (w : ℕ → X → ℝ) (K : ℝ) (O : ℕ → Set X),
      (∀ R, A.Smooth (w R)) ∧ (∀ R, IsPsh A (α + LocPot.ofFun (w R))) ∧
      (∀ R x, x ∉ boundary σ →
        -(K * (1 + ∑ i, Real.log (rFun (Λ i) (σ i) x))) ≤ w R x ∧ w R x ≤ 0) ∧
      (∀ R, IsOpen (O R)) ∧ Monotone O ∧ (∀ R, O R ⊆ (boundary σ)ᶜ) ∧
      (∀ x, x ∉ boundary σ → ∃ R, x ∈ O R) ∧
      (∀ R, ∀ x ∈ O R, w R x = pFun Λ σ c x / 2) := by
  intro d X _ _ _ A m α Λ σ c h
  obtain ⟨hα, hαpos, hΛ, hadm⟩ := h
  have hΛ' : ∀ i, IsPotential A (Λ i) ∧ IsSection A (Λ i) (σ i) ∧ ∀ y, normSec (Λ i) (σ i) y ≤ 1 := fun i => ⟨(hΛ i).1, (hΛ i).2.1, (hΛ i).2.2.2⟩
  obtain ⟨hZ, hsmu⟩ := hsm d X A m Λ σ c hΛ'
  set Z := boundary σ with hZdef
  set u : X → ℝ := fun y => pFun Λ σ c y / 2 with hu
  have hc : 0 < c := hadm.1
  have hlogr : ∀ i y, 0 ≤ Real.log (rFun (Λ i) (σ i) y) := by
    intro i y
    have h0 : 0 ≤ normSec (Λ i) (σ i) y := by unfold normSec; positivity
    have h1 : logNormSec (Λ i) (σ i) y ≤ 0 := Real.log_nonpos h0 ((hΛ i).2.2.2 y)
    have h2 : (1 : ℝ) ≤ rFun (Λ i) (σ i) y := by
      unfold rFun
      linarith [Real.add_one_le_exp (1 : ℝ)]
    exact Real.log_nonneg h2
  have hsum : ∀ y, 0 ≤ ∑ i, Real.log (rFun (Λ i) (σ i) y) :=
    fun y => Finset.sum_nonneg fun i _ => hlogr i y
  have hneg : ∀ x ∈ Zᶜ, u x ≤ 0 := by
    intro x _
    simp only [hu, pFun]
    have := hsum x
    have : 0 ≤ c * ∑ i, Real.log (rFun (Λ i) (σ i) x) := mul_nonneg hc.le this
    linarith
  have hpsh : IsPsh A α := fun x j y hy w => by
    rcases eq_or_ne w 0 with rfl | hw
    · simp [levi]
    · exact (hαpos x j y hy w hw).le
  have htr : ∀ R : ℕ, ∃ v : X → ℝ, A.Smooth v ∧ IsPsh A (α + LocPot.ofFun v) ∧
      (∀ x ∈ Zᶜ, u x ≤ v x ∧ v x ≤ 0) ∧ ∀ x ∈ Zᶜ, -((R : ℝ) + 2) + 2 ≤ u x → v x = u x :=
    fun R => exists_exact_truncation d X A α Z u ((R : ℝ) + 2) (by linarith [(Nat.cast_nonneg R : (0:ℝ) ≤ R)]) hZ hα hpsh hsmu hneg
      (hlv d X A m α Λ σ c ⟨hα, hαpos, hΛ, hadm⟩) (hbt d X A m α Λ σ c ⟨hα, hαpos, hΛ, hadm⟩)
  choose w hw1 hw2 hw3 hw4 using htr

  have hcont : ∀ x ∈ Zᶜ, ContinuousAt u x := by
    intro x hx
    obtain ⟨j, hj⟩ := A.cover x
    have hO := (A.chart j).isOpen_inter_preimage_symm hZ.isOpen_compl
    have hxO : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Zᶜ :=
      ⟨(A.chart j).map_source hj, by simp only [Set.mem_preimage, (A.chart j).left_inv hj]; exact hx⟩
    have h1 : ContinuousAt (u ∘ (A.chart j).symm) (A.chart j x) :=
      ((hsmu j).continuousOn.continuousAt (hO.mem_nhds hxO))
    have h2 : ContinuousAt ((u ∘ (A.chart j).symm) ∘ A.chart j) x :=
      h1.comp ((A.chart j).continuousAt hj)
    refine h2.congr ?_
    filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
    simp [(A.chart j).left_inv hy]
  refine ⟨w, c / 2, fun R => {x | x ∈ Zᶜ ∧ -(R : ℝ) < u x}, hw1, hw2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro R x hx
    have h3 := hw3 R x hx
    refine ⟨?_, h3.2⟩
    have e1 : u x = pFun Λ σ c x / 2 := rfl
    rw [e1] at h3
    unfold pFun at h3
    refine le_trans ?_ h3.1
    nlinarith
  · intro R
    rw [isOpen_iff_mem_nhds]
    intro x hx
    filter_upwards [hZ.isOpen_compl.mem_nhds hx.1,
      (hcont x hx.1).eventually (lt_mem_nhds hx.2)] with y h1 h2
    exact ⟨h1, h2⟩
  · intro R R' hRR' x hx
    refine ⟨hx.1, lt_of_le_of_lt ?_ hx.2⟩
    have : (R : ℝ) ≤ R' := by exact_mod_cast hRR'
    linarith
  · intro R x hx
    exact hx.1
  · intro x hx
    obtain ⟨R, hR⟩ := exists_nat_gt (-u x)
    exact ⟨R, hx, by linarith⟩
  · intro R x hx
    exact hw4 R x hx.1 (by linarith [hx.2])

end GlobalTheory.PoincareTrunc

namespace GlobalTheory.PoincareTrunc

theorem smoothTrunc : ∀ (d : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas d X) (m : ℕ) (α : LocPot X) (Λ : Fin m → LocPot X) (σ : Fin m → X → X → ℂ) (c : ℝ),
    IsBoundarySetting A α Λ σ c →
    ∃ (w : ℕ → X → ℝ) (K : ℝ) (O : ℕ → Set X),
      (∀ R, A.Smooth (w R)) ∧ (∀ R, IsPsh A (α + LocPot.ofFun (w R))) ∧
      (∀ R x, x ∉ boundary σ →
        -(K * (1 + ∑ i, Real.log (rFun (Λ i) (σ i) x))) ≤ w R x ∧ w R x ≤ 0) ∧
      (∀ R, IsOpen (O R)) ∧ Monotone O ∧ (∀ R, O R ⊆ (boundary σ)ᶜ) ∧
      (∀ x, x ∉ boundary σ → ∃ R, x ∈ O R) ∧
      (∀ R, ∀ x ∈ O R, w R x = pFun Λ σ c x / 2) :=
  smooth_trunc_of_parts GlobalTheory.T.potential_boundary_smooth GlobalTheory.T.boundary_potential_psh GlobalTheory.T.boundary_sublevel_closure_complement

end GlobalTheory.PoincareTrunc
