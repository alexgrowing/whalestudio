import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInhab
import ReciprocityTheory.AnalyticForms.LeviForms.TailBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedB
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LeviPullEq

noncomputable section

namespace LevelTowerAlt.Comparison₂

open Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB

variable {e e' : ℕ} {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z] {A : FinHolAtlas e X} {A' : FinHolAtlas e' Z}

theorem holo_mono {U V : Set X} {g : X → ℂ} (h : A.HoloOn U g) (hVU : V ⊆ U) : A.HoloOn V g :=
  fun j => (h j).mono fun _ hy => ⟨hy.1, hVU hy.2⟩

theorem holo_cont {U : Set X} {g : X → ℂ} (h : A.HoloOn U g) {x : X} (hx : x ∈ U) : ContinuousAt g x := by
  obtain ⟨j, hj⟩ := A.cover x
  have hc := (h j _ ⟨(A.chart j).map_source hj, by rwa [Set.mem_preimage, (A.chart j).left_inv hj]⟩).continuousAt
  refine (hc.comp ((A.chart j).continuousAt hj)).congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [(A.chart j).left_inv hy]

theorem holo_comp {U : Set Z} {g : Z → ℂ} (hg : A'.HoloOn U g) {h : X → Z} (hh : HoloMap A A' h) :
    A.HoloOn (h ⁻¹' U) (g ∘ h) := by
  intro j y hy
  obtain ⟨k, hk⟩ := A'.cover (h ((A.chart j).symm y))
  have h1 := hh.2 j k y ⟨hy.1, hk⟩
  have h2 := hg k (A'.chart k (h ((A.chart j).symm y)))
    ⟨(A'.chart k).map_source hk, by rw [Set.mem_preimage, (A'.chart k).left_inv hk]; exact hy.2⟩
  refine (AnalyticAt.comp (f := A'.chart k ∘ h ∘ (A.chart j).symm) h2 h1).congr ?_
  have hc : ContinuousAt (h ∘ (A.chart j).symm) y := hh.1.continuousAt.comp ((A.chart j).continuousAt_symm hy.1)
  filter_upwards [hc.eventually_mem ((A'.chart k).open_source.mem_nhds hk)] with y' hy'
  have : (A'.chart k).symm (A'.chart k (h ((A.chart j).symm y'))) = h ((A.chart j).symm y') := (A'.chart k).left_inv hy'
  simp [this]

def LocRe (A : FinHolAtlas e X) (u : X → ℝ) (x : X) : Prop :=
  ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ G : X → ℂ, A.HoloOn V G ∧ ∀ y ∈ V, u y = (G y).re

theorem LocRe.congr {u u' : X → ℝ} {x : X} (h : LocRe A u x) (hu : ∀ᶠ y in 𝓝 x, u' y = u y) : LocRe A u' x := by
  obtain ⟨V, hV, hx, G, hG, h⟩ := h
  obtain ⟨W, hW, hWo, hxW⟩ := eventually_nhds_iff.1 hu
  exact ⟨V ∩ W, hV.inter hWo, ⟨hx, hxW⟩, G, holo_mono hG Set.inter_subset_left, fun y hy => (hW y hy.2).trans (h y hy.1)⟩

theorem LocRe.zero (x : X) : LocRe A (fun _ => 0) x :=
  ⟨Set.univ, isOpen_univ, trivial, fun _ => 0, fun _ _ _ => analyticAt_const, fun _ _ => rfl⟩

theorem LocRe.add {u u' : X → ℝ} {x : X} (h : LocRe A u x) (h' : LocRe A u' x) : LocRe A (fun y => u y + u' y) x := by
  obtain ⟨V, hV, hx, G, hG, h⟩ := h
  obtain ⟨V', hV', hx', G', hG', h'⟩ := h'
  exact ⟨V ∩ V', hV.inter hV', ⟨hx, hx'⟩, _, holoOn_add A hG hG', fun y hy => by simp [h y hy.1, h' y hy.2]⟩

theorem LocRe.mul {u : X → ℝ} {x : X} (h : LocRe A u x) (c : ℝ) : LocRe A (fun y => c * u y) x := by
  obtain ⟨V, hV, hx, G, hG, h⟩ := h
  exact ⟨V, hV, hx, _, holoOn_mul A hG c, fun y hy => by simp [h y hy]⟩

theorem LocRe.sum {I : Type} (s : Finset I) {u : I → X → ℝ} {x : X} (h : ∀ i ∈ s, LocRe A (u i) x) :
    LocRe A (fun y => ∑ i ∈ s, u i y) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using LocRe.zero x
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (by simp)).add (ih fun j hj => h j (by simp [hj]))

theorem LocRe.comp {u : Z → ℝ} {h : X → Z} (hh : HoloMap A A' h) {x : X} (hu : LocRe A' u (h x)) : LocRe A (fun y => u (h y)) x := by
  obtain ⟨V, hV, hx, G, hG, hu⟩ := hu
  exact ⟨h ⁻¹' V, hV.preimage hh.1, hx, _, holo_comp hG hh, fun y hy => hu _ hy⟩

theorem LocRe.log {U : Set X} (hU : IsOpen U) {f : X → ℂ} (hf : A.HoloOn U f) {x : X} (hx : x ∈ U) (h0 : f x ≠ 0) :
    LocRe A (fun y => Real.log ‖f y‖) x := by
  have hc : ContinuousOn (fun y => f y / f x) U := fun y hy => ((holo_cont hf hy).div_const _).continuousWithinAt
  refine ⟨U ∩ (fun y => f y / f x) ⁻¹' Complex.slitPlane, hc.isOpen_inter_preimage hU Complex.isOpen_slitPlane,
    ⟨hx, by simp [div_self h0]⟩, fun y => Complex.log (f y / f x) + (Real.log ‖f x‖ : ℝ), fun j y hy => ?_, fun y hy => ?_⟩
  · exact (((hf j y ⟨hy.1, hy.2.1⟩).div_const (c := f x)).clog hy.2.2).add analyticAt_const
  · have h1 : f y ≠ 0 := fun h => by simpa [h] using hy.2
    simp [Complex.log_re, Real.log_div, h1, h0]

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem log_h_smul (L : HermLine J) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) {z : (Σ k, J k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (L.h fun p => c p.1 * z p) = ∑ k, (L.a k : ℝ) * Real.log ‖c k‖ + Real.log (L.h z) := by
  have hp : ∀ k, ‖c k‖ ^ L.a k ≠ 0 := fun k => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
  rw [L.smul c z hc, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => hp k) (L.pos z hz).ne', Real.log_prod fun k _ => hp k]
  simp only [Real.log_zpow]

theorem log_diff_orbit {L L' : HermLine J} (h : L.a = L'.a) {z z' : (Σ k, J k) → ℂ} (hz : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0)
    (ho : SameOrbit z z') : Real.log (L.h z) - Real.log (L'.h z) = Real.log (L.h z') - Real.log (L'.h z') := by
  obtain ⟨c, hc, rfl⟩ := ho
  rw [log_h_smul L hc hz, log_h_smul L' hc hz, h]
  ring

theorem locRe_orbit (L : HermLine J) {U : Set X} (hU : IsOpen U) {s s' : X → (Σ k, J k) → ℂ}
    (hs : ∀ p, A.HoloOn U fun y => s y p) (hs' : ∀ p, A.HoloOn U fun y => s' y p) (hne : ∀ y ∈ U, ∀ k, ∃ i, s' y ⟨k, i⟩ ≠ 0)
    (ho : ∀ y ∈ U, SameOrbit (s y) (s' y)) {x : X} (hx : x ∈ U) :
    LocRe A (fun y => Real.log (L.h (s y)) - Real.log (L.h (s' y))) x := by
  choose i hi using hne x hx
  have hi' : ∀ k, s x ⟨k, i k⟩ ≠ 0 := fun k => by
    obtain ⟨c, hc, e⟩ := ho x hx
    rw [e]
    exact mul_ne_zero (hc k) (hi k)
  have h1 := LocRe.sum (A := A) Finset.univ (x := x) (u := fun k y => (L.a k : ℝ) *
      (Real.log ‖s y ⟨k, i k⟩‖ + -1 * Real.log ‖s' y ⟨k, i k⟩‖)) fun k _ =>
    ((LocRe.log hU (hs _) hx (hi' k)).add ((LocRe.log hU (hs' _) hx (hi k)).mul _)).mul _
  refine h1.congr ?_
  filter_upwards [hU.mem_nhds hx, eventually_all.2 fun k => (holo_cont (hs' ⟨k, i k⟩) hx).eventually_ne (hi k)] with y hy hy'
  obtain ⟨c, hc, e⟩ := ho y hy
  rw [e, log_h_smul L hc (hne y hy), add_sub_cancel_right]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [norm_mul, Real.log_mul (norm_ne_zero_iff.2 (hc k)) (norm_ne_zero_iff.2 (hy' k))]
  ring

theorem psh_of_locRe {P Q : LocPot X} (hP : IsPotential A P) (hQ : IsPotential A Q)
    (h : ∀ x, LocRe A (fun y => P.φ x y - Q.φ x y) x) (hq : IsPsh A Q) : IsPsh A P := by
  have hz : A.Smooth (fun _ : X => (0 : ℝ)) := fun j => contDiffOn_const
  have h1 := (PshPull.isPsh_pull e e X X A A id (holoMap_id A) P Q (fun _ => 0) hP hQ hz (fun x _ => h x)).1
    (TailBoundAlt.isPsh_congr A _ _ hq (fun x y hy => hy.1) (by funext x y; exact add_zero _))
  exact TailBoundAlt.isPsh_congr A _ _ h1 (fun x y hy => ⟨hy, trivial⟩) (by funext x y; exact (add_zero _).symm)

theorem pot_rsmul {P : LocPot X} (hP : IsPotential A P) (c : ℝ) : IsPotential A (P.rsmul c) :=
  isPotential_mul A P hP c _ rfl fun _ _ => rfl

theorem exists_psh_pull [CompactSpace X] [T2Space X] {h : X → Z} (hh : HoloMap A A' h) {Θ : LocPot X} (hΘ : IsPotential A Θ)
    (hΘp : IsPosPot A Θ) {Θ' : LocPot Z} (hΘ' : IsPotential A' Θ') :
    ∃ C : ℝ, ∀ (P : LocPot X) (Q : LocPot Z), IsPotential A P → IsPotential A' Q → IsPsh A' (Q + Θ') →
      (∀ x, LocRe A (fun y => P.φ x y - Q.φ (h x) (h y)) x) → IsPsh A (P + Θ.rsmul C) := by
  have hp := isPotentialPullback A' A h hh Θ' hΘ'
  obtain ⟨C, -, -, hC⟩ := TailBoundAlt.exists_psh_chern_bound A Θ _ hΘ hΘp hp
  refine ⟨C, fun P Q hP hQ hq hl => ?_⟩
  have hz : A'.Smooth (fun _ : Z => (0 : ℝ)) := fun j => contDiffOn_const
  have hQ' := isPotentialAdd A' _ _ hQ hΘ'
  have hP' := isPotentialPullback A' A h hh _ hQ'
  have h1 := (PshPull.isPsh_pull e e' X Z A A' h hh _ (Q + Θ') (fun _ => 0) hP' hQ' hz
    (fun x _ => (LocRe.zero x).congr (Eventually.of_forall fun y => sub_self _))).1
    (TailBoundAlt.isPsh_congr A' _ _ hq (fun x y hy => hy.1) (by funext x y; exact add_zero _))
  have h2 : IsPsh A ((Q + Θ').pullback h hh.1) :=
    TailBoundAlt.isPsh_congr A _ _ h1 (fun x y hy => ⟨hy, trivial⟩) (by funext x y; exact (add_zero _).symm)
  have hR := isPotentialAdd A _ _ (pot_rsmul hΘ C) (pot_rsmul hp (-1))
  refine psh_of_locRe (isPotentialAdd A _ _ hP (pot_rsmul hΘ C)) (isPotentialAdd A _ _ hP' hR) (fun x => ?_)
    (isPshAdd A _ _ hP' hR h2 hC)
  refine (hl x).congr (Eventually.of_forall fun y => ?_)
  show P.φ x y + C * Θ.φ x y - (Q.φ (h x) (h y) + Θ'.φ (h x) (h y) + (C * Θ.φ x y + -1 * Θ'.φ (h x) (h y))) = _
  ring

end LevelTowerAlt.Comparison₂
