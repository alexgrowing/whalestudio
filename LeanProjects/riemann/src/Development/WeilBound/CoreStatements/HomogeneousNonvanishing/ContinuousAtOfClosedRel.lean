import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB

namespace PositivityTheory.UnitarySelfGeneration.HolomorphicMinorCharts

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology Set

section Charts

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem holo_analyticAt {A : FinHolAtlas e X} {U : Set X} {g : X → ℂ} (hg : A.HoloOn U g) (j : Fin A.n) {x : X}
    (hj : x ∈ (A.chart j).source) (hx : x ∈ U) : AnalyticAt ℂ (g ∘ (A.chart j).symm) (A.chart j x) :=
  hg j _ ⟨(A.chart j).map_source hj, by rwa [Set.mem_preimage, (A.chart j).left_inv hj]⟩

theorem holo_continuousAt {A : FinHolAtlas e X} {U : Set X} {g : X → ℂ} (hg : A.HoloOn U g) {x : X}
    (hx : x ∈ U) : ContinuousAt g x := by
  obtain ⟨j, hj⟩ := A.cover x
  have hc := (holo_analyticAt hg j hj hx).continuousAt
  exact ((A.chart j).symm.continuousAt_iff_continuousAt_comp_right
    (f := g) (x := x) (by simpa using hj)).mpr (by simpa using hc)

theorem tendsto_symm (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) {x : X} (hx : x ∈ ψ.source) :
    Tendsto ψ.symm (𝓝 (ψ x)) (𝓝 x) := ψ.tendsto_symm hx

theorem holo_compat {A : FinHolAtlas e X} {ψ : OpenPartialHomeomorph X (Fin e → ℂ)} (hψ : IsCompatChart A ψ)
    {U : Set X} {g : X → ℂ} (hg : A.HoloOn U g) {v : Fin e → ℂ} (hv : v ∈ ψ.target) (hU : ψ.symm v ∈ U) :
    AnalyticAt ℂ (g ∘ ψ.symm) v := by
  obtain ⟨j, hj⟩ := A.cover (ψ.symm v)
  have h1 := holo_analyticAt hg j hj hU
  have h2 : AnalyticAt ℂ (A.chart j ∘ ψ.symm) v := (hψ j).2 v ⟨hv, hj⟩
  refine (AnalyticAt.comp (f := A.chart j ∘ ψ.symm) h1 h2).congr ?_
  filter_upwards [(ψ.isOpen_inter_preimage_symm (A.chart j).open_source).mem_nhds ⟨hv, hj⟩] with w hw
  simp only [Function.comp_apply]
  rw [(A.chart j).left_inv hw.2]

theorem holoOn_of_compat {A : FinHolAtlas e X} {ψ : OpenPartialHomeomorph X (Fin e → ℂ)} (hψ : IsCompatChart A ψ)
    {U : Set X} (hU : U ⊆ ψ.source) {G : (Fin e → ℂ) → ℂ} (hG : ∀ x ∈ U, AnalyticAt ℂ G (ψ x)) :
    A.HoloOn U (fun x => G (ψ x)) := fun j v hv =>
  AnalyticAt.comp (g := G) (f := ψ ∘ (A.chart j).symm) (hG _ hv.2) ((hψ j).1 v ⟨hv.1, hU hv.2⟩)

theorem isCompatChart_chart (A : FinHolAtlas e X) (k : Fin A.n) : IsCompatChart A (A.chart k) :=
  fun j => ⟨A.holo j k, A.holo k j⟩

end Charts

theorem continuousAt_of_closed_rel {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X]
    {Γ : Set (X × Y)} (hΓ : IsClosed Γ) {ρ : Y → X} (hρ : ∀ y, (ρ y, y) ∈ Γ) {y₀ : Y}
    (h₀ : ∀ x, (x, y₀) ∈ Γ → x = ρ y₀) : ContinuousAt ρ y₀ := by
  intro W hW
  obtain ⟨O, hOW, hO, hO0⟩ := mem_nhds_iff.mp hW
  have hc : IsClosed (Prod.snd '' (Γ ∩ Prod.fst ⁻¹' Oᶜ)) :=
    isClosedMap_snd_of_compactSpace _ (hΓ.inter (hO.isClosed_compl.preimage continuous_fst))
  have hm : y₀ ∈ (Prod.snd '' (Γ ∩ Prod.fst ⁻¹' Oᶜ))ᶜ := by
    rintro ⟨⟨x, y⟩, ⟨h1, h2⟩, rfl⟩
    exact h2 (by rw [show x = ρ y from h₀ x h1]; exact hO0)
  rw [mem_map]
  filter_upwards [hc.isOpen_compl.mem_nhds hm] with y hy
  by_contra h
  exact hy ⟨(ρ y, y), ⟨hρ y, fun h' => h (hOW h')⟩, rfl⟩

theorem analyticAt_of_immersion {e e' : ℕ} {N : Type} [Fintype N] {f : (Fin e → ℂ) → N → ℂ}
    {h : (Fin e' → ℂ) → Fin e → ℂ} {g : (Fin e' → ℂ) → N → ℂ} {y : Fin e' → ℂ} (hf : AnalyticAt ℂ f (h y))
    (hker : (fderiv ℂ f (h y)).ker = ⊥) (hh : ContinuousAt h y) (hg : AnalyticAt ℂ g y)
    (hE : ∀ᶠ y' in 𝓝 y, f (h y') = g y') : AnalyticAt ℂ h y := by
  obtain ⟨l, hl⟩ := (fderiv ℂ f (h y)).toLinearMap.exists_leftInverse_of_injective hker
  let L : (N → ℂ) →L[ℂ] (Fin e → ℂ) := LinearMap.toContinuousLinearMap l
  have hLe : L.comp (fderiv ℂ f (h y)) =
      ((ContinuousLinearEquiv.refl ℂ (Fin e → ℂ) : (Fin e → ℂ) ≃L[ℂ] (Fin e → ℂ)) : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) := by
    refine ContinuousLinearMap.ext fun v => ?_
    exact LinearMap.congr_fun hl v
  have hφ : HasStrictFDerivAt (fun x => L (f x))
      ((ContinuousLinearEquiv.refl ℂ (Fin e → ℂ) : (Fin e → ℂ) ≃L[ℂ] (Fin e → ℂ)) : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ))
      (h y) := by
    rw [← hLe]
    exact L.hasStrictFDerivAt.comp _ hf.hasStrictFDerivAt
  let Φ := hφ.toOpenPartialHomeomorph (fun x => L (f x))
  have hΦ : ∀ x, Φ x = L (f x) := fun x => rfl
  have hpS : h y ∈ Φ.source := hφ.mem_toOpenPartialHomeomorph_source
  have hφan : AnalyticAt ℂ Φ (h y) := AnalyticAt.comp (g := L) (f := f) (L.analyticAt _) hf
  have hsymm : AnalyticAt ℂ Φ.symm (Φ (h y)) :=
    Φ.analyticAt_symm' (i := ContinuousLinearEquiv.refl ℂ (Fin e → ℂ)) hpS hφan hφ.hasFDerivAt.fderiv
  have h1 : AnalyticAt ℂ (fun y' => L (g y')) y := AnalyticAt.comp (g := L) (f := g) (L.analyticAt _) hg
  have h2 : Φ (h y) = L (g y) := by rw [hΦ, hE.self_of_nhds]
  rw [h2] at hsymm
  refine (AnalyticAt.comp (g := Φ.symm) (f := fun y' => L (g y')) hsymm h1).congr ?_
  filter_upwards [hE, hh (Φ.open_source.mem_nhds hpS)] with y' h3 h4
  simp only [Function.comp_apply]
  rw [← h3, ← hΦ, Φ.left_inv h4]

section Orbit

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem so_refl (z : (Σ k, ι k) → ℂ) : SameOrbit z z := ⟨fun _ => 1, fun _ => one_ne_zero, by simp⟩

theorem so_symm {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), funext fun p => ?_⟩
  rw [← mul_assoc, inv_mul_cancel₀ (hc _), one_mul]

theorem so_trans {a b c : (Σ k, ι k) → ℂ} (h1 : SameOrbit a b) (h2 : SameOrbit b c) : SameOrbit a c := by
  obtain ⟨s, hs, rfl⟩ := h1
  obtain ⟨t, ht, rfl⟩ := h2
  exact ⟨fun k => s k * t k, fun k => mul_ne_zero (hs k) (ht k), funext fun p => by ring⟩

theorem affCoord_so {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (p : (k : K) → ι k) :
    affCoord p z = affCoord p z' := by
  obtain ⟨c, hc, rfl⟩ := h
  funext q
  exact mul_div_mul_left _ _ (hc q.1)

theorem ne_zero_so {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (q : Σ k, ι k) : z q ≠ 0 ↔ z' q ≠ 0 := by
  obtain ⟨c, hc, rfl⟩ := h
  simp [hc q.1]

def Minors (z z' : (Σ k, ι k) → ℂ) : Prop := ∀ k i j, z ⟨k, i⟩ * z' ⟨k, j⟩ = z ⟨k, j⟩ * z' ⟨k, i⟩

theorem minors_of_so {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : Minors z z' := by
  obtain ⟨c, hc, rfl⟩ := h
  intro k i j
  ring

theorem so_of_minors {z z' : (Σ k, ι k) → ℂ} (h : Minors z z') (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (hz' : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0) : SameOrbit z z' := by
  choose p hp using hz'
  have key : ∀ k i, z ⟨k, i⟩ = z ⟨k, p k⟩ / z' ⟨k, p k⟩ * z' ⟨k, i⟩ := fun k i => by
    have := h k i (p k)
    have h0 := hp k
    field_simp
    rw [this]
  refine ⟨fun k => z ⟨k, p k⟩ / z' ⟨k, p k⟩, fun k h0 => ?_, funext fun q => key q.1 q.2⟩
  obtain ⟨i, hi⟩ := hz k
  exact hi (by rw [key k i, show z ⟨k, p k⟩ / z' ⟨k, p k⟩ = 0 from h0, zero_mul])

theorem minors_congr {a a' b b' : (Σ k, ι k) → ℂ} (ha : SameOrbit a a') (hb : SameOrbit b b') (h : Minors a' b') :
    Minors a b := by
  obtain ⟨s, hs, rfl⟩ := ha
  obtain ⟨t, ht, rfl⟩ := hb
  intro k i j
  have := h k i j
  simp only
  linear_combination s k * t k * this

theorem isClosed_minors {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {U : X → Set X}
    {lam : X → X → (Σ k, ι k) → ℂ} {V : Y → Set Y} {mu : Y → Y → (Σ k, ι k) → ℂ}
    (hU : ∀ x, IsOpen (U x) ∧ x ∈ U x) (hl : ∀ x p, ContinuousAt (fun y => lam x y p) x)
    (hlc : ∀ x x', ∀ w ∈ U x ∩ U x', SameOrbit (lam x w) (lam x' w))
    (hV : ∀ x, IsOpen (V x) ∧ x ∈ V x) (hm : ∀ x p, ContinuousAt (fun y => mu x y p) x)
    (hmc : ∀ x x', ∀ w ∈ V x ∩ V x', SameOrbit (mu x w) (mu x' w)) :
    IsClosed {q : X × Y | Minors (lam q.1 q.1) (mu q.2 q.2)} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  rintro ⟨x, y⟩ h
  simp only [mem_compl_iff, mem_setOf_eq, Minors, not_forall] at h
  obtain ⟨k, i, j, h⟩ := h
  have c1 : ∀ p, ContinuousAt (fun q : X × Y => lam x q.1 p) (x, y) := fun p =>
    ContinuousAt.comp (g := fun y => lam x y p) (hl x p) continuousAt_fst
  have c2 : ∀ p, ContinuousAt (fun q : X × Y => mu y q.2 p) (x, y) := fun p =>
    ContinuousAt.comp (g := fun w => mu y w p) (hm y p) continuousAt_snd
  have c3 := (((c1 ⟨k, i⟩).mul (c2 ⟨k, j⟩)).sub ((c1 ⟨k, j⟩).mul (c2 ⟨k, i⟩))).eventually_ne (y := 0)
    (sub_ne_zero.mpr h)
  filter_upwards [c3, prod_mem_nhds ((hU x).1.mem_nhds (hU x).2) ((hV y).1.mem_nhds (hV y).2)] with q h1 h2 h3
  exact h1 (sub_eq_zero.mpr (minors_congr (hlc x q.1 q.1 ⟨h2.1, (hU _).2⟩) (hmc y q.2 q.2 ⟨h2.2, (hV _).2⟩) h3 k i j))

theorem analyticAt_affCoord (p : (k : K) → ι k) {z : (Σ k, ι k) → ℂ} (hz : ∀ k, z ⟨k, p k⟩ ≠ 0) :
    AnalyticAt ℂ (affCoord p) z := by
  refine analyticAt_pi_iff.mpr fun q => ?_
  exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Σ k, ι k => ℂ) q).analyticAt z).div
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Σ k, ι k => ℂ) ⟨q.1, p q.1⟩).analyticAt z) (hz q.1)

theorem analyticAt_factor {e e' : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {A : FinHolAtlas e X} {B : FinHolAtlas e' Y} {U : Set X} {lam : X → (Σ k, ι k) → ℂ} {V : Set Y}
    {mu : Y → (Σ k, ι k) → ℂ} {π : Y → X} {y : Y} (hl : ∀ p, A.HoloOn U fun x => lam x p) (hU : π y ∈ U)
    (hm : ∀ p, B.HoloOn V fun x => mu x p) (hV : y ∈ V) (hπ : ContinuousAt π y)
    (hnz : ∀ k, ∃ i, lam (π y) ⟨k, i⟩ ≠ 0)
    (himm : ∀ p : (k : K) → ι k, (∀ k, lam (π y) ⟨k, p k⟩ ≠ 0) → ∀ j, π y ∈ (A.chart j).source →
      (fderiv ℂ (fun w => affCoord p (lam ((A.chart j).symm w))) (A.chart j (π y))).ker = ⊥)
    (hso : ∀ᶠ w in 𝓝 y, SameOrbit (lam (π w)) (mu w)) (j : Fin B.n) (k : Fin A.n)
    (hj : y ∈ (B.chart j).source) (hk : π y ∈ (A.chart k).source) :
    AnalyticAt ℂ (A.chart k ∘ π ∘ (B.chart j).symm) (B.chart j y) := by
  choose p hp using hnz
  have e1 : (A.chart k ∘ π ∘ (B.chart j).symm) (B.chart j y) = A.chart k (π y) := by
    simp only [Function.comp_apply, (B.chart j).left_inv hj]
  have ht := tendsto_symm (B.chart j) hj
  refine analyticAt_of_immersion (f := fun w => affCoord p (lam ((A.chart k).symm w)))
    (g := fun w => affCoord p (mu ((B.chart j).symm w))) ?_ ?_ ?_ ?_ ?_
  · rw [e1]
    refine AnalyticAt.comp (g := affCoord p) (f := fun w => lam ((A.chart k).symm w))
      (analyticAt_affCoord p ?_) (analyticAt_pi_iff.mpr fun q => holo_analyticAt (hl q) k hk hU)
    rw [(A.chart k).left_inv hk]
    exact hp
  · rw [e1]
    exact himm p hp k hk
  · rw [ContinuousAt, e1]
    exact ((A.chart k).continuousAt hk).tendsto.comp (hπ.tendsto.comp ht)
  · refine AnalyticAt.comp (g := affCoord p) (f := fun w => mu ((B.chart j).symm w))
      (analyticAt_affCoord p ?_) (analyticAt_pi_iff.mpr fun q => holo_analyticAt (hm q) j hj hV)
    rw [(B.chart j).left_inv hj]
    exact fun k' => (ne_zero_so hso.self_of_nhds _).mp (hp k')
  · filter_upwards [ht.eventually hso, (hπ.tendsto.comp ht).eventually ((A.chart k).open_source.mem_nhds hk)]
      with w h1 h2
    simp only [Function.comp_apply] at h2 ⊢
    rw [(A.chart k).left_inv h2]
    exact affCoord_so h1 p

end Orbit

end PositivityTheory.UnitarySelfGeneration.HolomorphicMinorCharts
