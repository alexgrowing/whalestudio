import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.ContinuousAtOfClosedRel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection

namespace PositivityTheory.UnitarySelfGeneration.HolomorphicMinorCharts

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology Set
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap)

set_option linter.unusedSectionVars false

section Charts

variable {e e' : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem holo_comp {A : FinHolAtlas e X} {B : FinHolAtlas e' Y} {ρ : Y → X} {N : Set Y} {V : Set X} {g : X → ℂ}
    (hg : A.HoloOn V g) (hN : ∀ y ∈ N, ρ y ∈ V) (hc : ∀ y ∈ N, ContinuousAt ρ y)
    (ha : ∀ y ∈ N, ∀ j k, y ∈ (B.chart j).source → ρ y ∈ (A.chart k).source →
      AnalyticAt ℂ (A.chart k ∘ ρ ∘ (B.chart j).symm) (B.chart j y)) : B.HoloOn N fun y => g (ρ y) := by
  intro j w hw
  obtain ⟨k, hk⟩ := A.cover (ρ ((B.chart j).symm w))
  have h1 := ha _ hw.2 j k ((B.chart j).map_target hw.1) hk
  rw [(B.chart j).right_inv hw.1] at h1
  refine (AnalyticAt.comp (f := A.chart k ∘ ρ ∘ (B.chart j).symm) (holo_analyticAt hg k hk (hN _ hw.2)) h1).congr ?_
  filter_upwards [((hc _ hw.2).comp ((B.chart j).continuousAt_symm hw.1)) ((A.chart k).open_source.mem_nhds hk)]
    with v hv
  simp only [Function.comp_apply]
  exact congrArg g ((A.chart k).left_inv hv)

theorem holo_comp_map {A : FinHolAtlas e X} {B : FinHolAtlas e' Y} {ρ : Y → X} (h : HoloMap B A ρ) {V : Set X}
    {g : X → ℂ} (hg : A.HoloOn V g) : B.HoloOn (ρ ⁻¹' V) fun y => g (ρ y) :=
  holo_comp hg (fun _ hy => hy) (fun _ _ => h.1.continuousAt) fun y _ j k hj hk =>
    h.2 j k _ ⟨(B.chart j).map_source hj, by rwa [mem_preimage, (B.chart j).left_inv hj]⟩

theorem holo_mono {A : FinHolAtlas e X} {U V : Set X} {g : X → ℂ} (hg : A.HoloOn V g) (h : U ⊆ V) : A.HoloOn U g :=
  fun j => (hg j).mono fun _ hw => ⟨hw.1, h hw.2⟩

theorem isOpen_holo_preimage {A : FinHolAtlas e X} {N : Set X} (hN : IsOpen N) {q : X → ℂ} (hq : A.HoloOn N q)
    {T : Set ℂ} (hT : IsOpen T) : IsOpen (N ∩ q ⁻¹' T) :=
  ContinuousOn.isOpen_inter_preimage (fun _ hy => (holo_continuousAt hq hy).continuousWithinAt) hN hT

theorem exists_log {A : FinHolAtlas e X} {N : Set X} (hN : IsOpen N) {q : X → ℂ} (hq : A.HoloOn N q) {x : X}
    (hx : x ∈ N) (h0 : q x ≠ 0) : ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ W ⊆ N ∧ ∃ G : X → ℂ, A.HoloOn W G ∧
      ∀ y ∈ W, Real.log ‖q y‖ = (G y).re := by
  have hq' : A.HoloOn N fun y => q y / q x := fun j w hw => (hq j w hw).div_const
  refine ⟨N ∩ (fun y => q y / q x) ⁻¹' Complex.slitPlane, isOpen_holo_preimage hN hq' Complex.isOpen_slitPlane,
    ⟨hx, by simp [h0]⟩, inter_subset_left, fun y => Complex.log (q y / q x) + (Real.log ‖q x‖ : ℝ),
    fun j w hw => ((hq' j w ⟨hw.1, hw.2.1⟩).clog hw.2.2).add analyticAt_const, fun y hy => ?_⟩
  have h1 : q y ≠ 0 := fun h => Complex.slitPlane_ne_zero hy.2 (by simp [h])
  rw [Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_div,
    Real.log_div (norm_ne_zero_iff.mpr h1) (norm_ne_zero_iff.mpr h0)]
  ring

end Charts

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem log_h_orbit (L : HermLine ι) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (L.h fun p => c p.1 * z p) = Real.log ‖∏ k, c k ^ L.a k‖ + Real.log (L.h z) := by
  rw [L.smul c z hc, Real.log_mul (Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k)))
    (L.pos z hz).ne']
  simp only [norm_prod, norm_zpow]

theorem orbit_re {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} (L : HermLine ι) {N : Set X}
    (hN : IsOpen N) {lam mu : X → (Σ k, ι k) → ℂ} (hl : ∀ p, A.HoloOn N fun y => lam y p)
    (hm : ∀ p, A.HoloOn N fun y => mu y p) (hnz : ∀ y ∈ N, ∀ k, ∃ i, mu y ⟨k, i⟩ ≠ 0)
    (hso : ∀ y ∈ N, SameOrbit (lam y) (mu y)) {x : X} (hx : x ∈ N) :
    ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ W ⊆ N ∧ ∃ G : X → ℂ, A.HoloOn W G ∧
      ∀ y ∈ W, Real.log (L.h (lam y)) - Real.log (L.h (mu y)) = (G y).re := by
  choose p hp using hnz x hx
  have hN' : IsOpen (N ∩ ⋂ k, (N ∩ (fun y => mu y ⟨k, p k⟩) ⁻¹' {0}ᶜ)) :=
    hN.inter (isOpen_iInter_of_finite fun k => isOpen_holo_preimage hN (hm _) isOpen_compl_singleton)
  have hne : ∀ y ∈ N ∩ ⋂ k, (N ∩ (fun y => mu y ⟨k, p k⟩) ⁻¹' {0}ᶜ), ∀ k, mu y ⟨k, p k⟩ ≠ 0 :=
    fun y hy k => (mem_iInter.mp hy.2 k).2
  obtain ⟨W, hW, hxW, hWN, G, hG, hE⟩ := exists_log (A := A) hN'
    (q := fun y => ∏ k, (lam y ⟨k, p k⟩ / mu y ⟨k, p k⟩) ^ L.a k) (x := x)
    (fun j w hw => Finset.analyticAt_fun_prod _ fun k _ =>
      ((hl ⟨k, p k⟩ j w ⟨hw.1, hw.2.1⟩).fun_div (hm ⟨k, p k⟩ j w ⟨hw.1, hw.2.1⟩) (hne _ hw.2 k)).fun_zpow
        (div_ne_zero ((ne_zero_so (hso _ hw.2.1) _).mpr (hne _ hw.2 k)) (hne _ hw.2 k)))
    ⟨hx, mem_iInter.mpr fun k => ⟨hx, hp k⟩⟩
    (Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (div_ne_zero ((ne_zero_so (hso _ hx) _).mpr (hp k)) (hp k)))
  refine ⟨W, hW, hxW, fun y hy => (hWN hy).1, G, hG, fun y hy => ?_⟩
  rw [← hE y hy]
  obtain ⟨c, hc, h⟩ := hso y (hWN hy).1
  rw [h, log_h_orbit L hc (hnz y (hWN hy).1)]
  simp only [fun k => mul_div_cancel_right₀ (c k) (hne y (hWN hy) k)]
  ring

theorem eval_ne_so {g : MRing ι} {a : K → ℕ} (hg : IsMultiHomog g a) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    eval z (map (Int.castRingHom ℂ) g) = 0 ↔ eval z' (map (Int.castRingHom ℂ) g) = 0 := by
  obtain ⟨c, hc, rfl⟩ := h
  rw [eval_smul_homog g a hg, mul_eq_zero]
  exact or_iff_right (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k))

theorem isOpen_nonvan {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) {g : MRing ι} {a : K → ℕ}
    (hg : IsMultiHomog g a) : IsOpen {x | eval (R.lift x x) (map (Int.castRingHom ℂ) g) ≠ 0} := by
  refine isOpen_iff_mem_nhds.mpr fun x hx => ?_
  filter_upwards [(holo_continuousAt (holoOn_eval_lift R x g) (R.mem_U x)).eventually_ne hx,
    (R.isOpen_U x).mem_nhds (R.mem_U x)] with y h1 h2 h3
  exact h1 ((eval_ne_so hg (R.compat x y y ⟨h2, R.mem_U y⟩)).mpr h3)

theorem exists_homog_not_mem {P J : Ideal (MRing ι)} (hJ : IsMultiHomogIdeal J) (h : ¬ J ≤ P) :
    ∃ f a, f ∈ J ∧ f ∉ P ∧ IsMultiHomog f a := by
  obtain ⟨S, hS, rfl⟩ := hJ
  rw [Ideal.span_le] at h
  obtain ⟨f, h1, h2⟩ := Set.not_subset.mp h
  obtain ⟨a, ha⟩ := hS f h1
  exact ⟨f, a, Ideal.subset_span h1, h2, ha⟩

variable {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem so_pull {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hv : IsBlockMap κ v) {z z' : (Σ k, ι' k) → ℂ}
    (h : SameOrbit z z') : SameOrbit (fun p => z (v p)) fun p => z' (v p) := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c (κ k), fun k => hc _, funext fun p => by simp only [hv.2.2.1]⟩

theorem homog_rename {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hv : IsBlockMap κ v) {f : MRing ι} {a : K → ℕ}
    (hf : IsMultiHomog f a) : ∃ b, IsMultiHomog (rename v f) b := by
  classical
  refine ⟨fun k' => ∑ k, if κ k = k' then a k else 0, fun m hm k' => ?_⟩
  obtain ⟨u, rfl, hu⟩ := coeff_rename_ne_zero v f m (mem_support_iff.mp hm)
  have h1 : ∀ m : (Σ k, ι' k) →₀ ℕ, ∑ i, m ⟨k', i⟩ = m.sum fun q n => if q.1 = k' then n else 0 := fun m => by
    rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma, Finset.sum_eq_single k']
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  rw [h1, Finsupp.sum_mapDomain_index (by simp) (fun _ _ _ => by split_ifs <;> simp),
    Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [hv.2.2.1]
  split_ifs
  · exact hf u (mem_support_iff.mpr hu) k
  · simp

end PositivityTheory.UnitarySelfGeneration.HolomorphicMinorCharts
