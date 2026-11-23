import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.IsMultiHomogChartMonomial
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}

namespace HermMetricEq

theorem isValueAt_iff {s : Ω} {v : ℂ} :
    IsValueAt y s z v ↔ IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt y s z v := by
  constructor
  · rintro ⟨d, g, h, hg, hh, hy, hyg, hz, hv⟩
    exact ⟨d, g, h, hg, hh, hy, hyg, hz, by rw [hv, div_mul_cancel₀ _ hz]⟩
  · rintro ⟨d, g, h, hg, hh, hy, hyg, hz, hv⟩
    exact ⟨d, g, h, hg, hh, hy, hyg, hz, by rw [hv, mul_div_cancel_right₀ _ hz]⟩

theorem regularAt_inv {f : Ω} (hf0 : f ≠ 0) (hf : IsUnitAt y f z) :
    IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y f⁻¹ z := by
  obtain ⟨v, ⟨d, g, h, hg, hh, hy, hyg, hz, hv⟩, hv0⟩ := hf
  have hgz : eval z (map (Int.castRingHom ℂ) g) ≠ 0 := by
    intro h0
    rw [h0, zero_div] at hv
    exact hv0 hv
  have hgy : aeval y g ≠ 0 := by
    rw [hyg]
    exact mul_ne_zero hf0 hy
  refine ⟨v⁻¹, d, h, g, hh, hg, hgy, ?_, hgz, ?_⟩
  · rw [hyg, inv_mul_cancel_left₀ hf0]
  · rw [hv, inv_div, div_mul_cancel₀ _ hgz]

theorem regularAt_pow {a : Ω} (ha : IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y a z) (n : ℕ) :
    IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y (a ^ n) z := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact ⟨1, IndefiniteRowSideFullHecke.LowerBoundFree.isValueAt_one⟩
  | succ n ih =>
    rw [pow_succ]
    exact ih.mul ha

theorem segreCoord_ne_zero (hz : z ∈ mcPts (mCoordIdeal y)) {c : (k : K) → ι k}
    (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) : segreCoord y c ≠ 0 := by
  intro h0
  have hm := IndefiniteRowSideFullHecke.LowerBoundFree.mem_mCoordIdeal_of_aeval (y := y)
    (IndefiniteRowSideFullHecke.LowerBoundFree.isMultiHomog_chartMonomial c) (by simpa [segreCoord] using h0)
  have := hz.2 _ hm
  simp only [map_prod, map_X, eval_X] at this
  exact Finset.prod_ne_zero_iff.2 (fun k _ => hc k) this

variable {E : Type} [AddCommGroup E] [Module Ω E] {N : ℕ}

theorem isFrameAt_of_isFrameOver {W : ChartBundle ℤ (segreCoord y) N E} {c : (k : K) → ι k} {f : Ω}
    {b : Fin N → E} (hb : IsFrameOver y W c f b) (hz : z ∈ mcPts (mCoordIdeal y))
    (hd : InFrameDomain y c f z) : IndefiniteRowSideFullHecke.LowerBoundFree.IsFrameAt y W z b := by
  obtain ⟨hx, -, hf0, -, hiff⟩ := hb
  have hfi : IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y f⁻¹ z := regularAt_inv hf0 hd.2
  have hloc : ∀ a : Ω, (∃ n : ℕ, f ^ n * a ∈ chartRing ℤ (segreCoord y) c) →
      IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y a z := by
    rintro a ⟨n, hn⟩
    have h1 := (regularAt_pow hfi n).mul (IndefiniteRowSideFullHecke.LowerBoundFree.regularAt_of_mem_chartRing hz hd.1 hn)
    rwa [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hf0, one_pow, one_mul] at h1
  have hsec : ∀ c' : (k : K) → ι k, (∀ k, z ⟨k, c' k⟩ ≠ 0) → ∀ s ∈ W.lat c',
      ∃ a : Fin N → Ω, (∀ q, IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y (a q) z) ∧ s = ∑ q, a q • b q := by
    intro c' hc' s hs
    have hx' := segreCoord_ne_zero hz hc'
    obtain ⟨m, hm⟩ := W.overlap c' c hx' hx s hs
    obtain ⟨a, ha, hae⟩ := (hiff _).1 ⟨0, by rwa [pow_zero, one_smul]⟩
    have hr : IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y ((segreCoord y c / segreCoord y c') ^ m) z :=
      regularAt_pow (IndefiniteRowSideFullHecke.LowerBoundFree.regularAt_of_mem_chartRing hz hc'
        (Algebra.subset_adjoin ⟨c, rfl⟩)) m
    refine ⟨fun q => (segreCoord y c / segreCoord y c') ^ m * a q,
      fun q => hr.mul (hloc _ (ha q)), ?_⟩
    have hone : (segreCoord y c / segreCoord y c') ^ m * (segreCoord y c' / segreCoord y c) ^ m = 1 := by
      rw [← mul_pow, div_mul_div_comm, mul_comm (segreCoord y c) (segreCoord y c'),
        div_self (mul_ne_zero hx' hx), one_pow]
    calc s = ((segreCoord y c / segreCoord y c') ^ m * (segreCoord y c' / segreCoord y c) ^ m) • s := by
          rw [hone, one_smul]
      _ = (segreCoord y c / segreCoord y c') ^ m • ∑ q, a q • b q := by rw [mul_smul, hae]
      _ = ∑ q, ((segreCoord y c / segreCoord y c') ^ m * a q) • b q := by
          rw [Finset.smul_sum]
          simp only [mul_smul]
  refine ⟨fun q => ?_, fun e he => ?_⟩
  · have hex : ∃ n : ℕ, f ^ n • b q ∈ W.lat c := by
      refine (hiff (b q)).2 ⟨Pi.single q 1, fun q' => ⟨0, ?_⟩, ?_⟩
      · rw [pow_zero, one_mul]
        rcases eq_or_ne q' q with rfl | h
        · rw [Pi.single_eq_same]
          exact one_mem _
        · rw [Pi.single_eq_of_ne h]
          exact zero_mem _
      · simp [Pi.single_apply, ite_smul]
    obtain ⟨n, hn⟩ := hex
    refine ⟨c, hd.1, 1, fun _ => (f ^ n)⁻¹, fun _ => f ^ n • b q, fun _ => hn, fun _ => ?_, ?_⟩
    · rw [← inv_pow]
      exact regularAt_pow hfi n
    · rw [Fin.sum_univ_one]
      exact (inv_smul_smul₀ (pow_ne_zero _ hf0) _).symm
  · obtain ⟨c', hc', m, a, s, hs, ha, rfl⟩ := he
    choose α hα hαe using fun l => hsec c' hc' (s l) (hs l)
    refine ⟨fun q => ∑ l, a l * α l q,
      fun q => IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt.sum _ fun l _ => (ha l).mul (hα l q), ?_⟩
    simp only [Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hαe l, Finset.smul_sum]

theorem coeff_unique {b : Fin N → E} (hli : LinearIndependent Ω b) {S S' : Matrix (Fin N) (Fin N) Ω}
    (h : ∀ q, ∑ p, S p q • b p = ∑ p, S' p q • b p) : S = S' := by
  ext p q
  exact Fintype.linearIndependent_iffₛ.1 hli (fun p => S p q) (fun p => S' p q) (h q) p

theorem exists_coeff {W : ChartBundle ℤ (segreCoord y) N E} {c : (k : K) → ι k} {f : Ω}
    {b : Fin N → E} (hb : IsFrameOver y W c f b) (hz : z ∈ mcPts (mCoordIdeal y))
    (hd : InFrameDomain y c f z) {b' : Fin N → E}
    (hb' : ∀ q, IndefiniteRowSideFullHecke.LowerBoundFree.IsLocSection y W z (b' q)) :
    ∃ S : Matrix (Fin N) (Fin N) Ω, (∀ p q, IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y (S p q) z) ∧
      ∀ q, b' q = ∑ p, S p q • b p := by
  choose a ha hae using fun q => (isFrameAt_of_isFrameOver hb hz hd).2 _ (hb' q)
  exact ⟨Matrix.of fun p q => a q p, fun p q => ha q p, fun q => hae q⟩

def valM (y : (Σ k, ι k) → Ω) (S : Matrix (Fin N) (Fin N) Ω) (z : (Σ k, ι k) → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun p q => IndefiniteRowSideFullHecke.LowerBoundFree.valAt y (S p q) z

theorem isValueAt_mul {S T : Matrix (Fin N) (Fin N) Ω} {Sz Tz : Matrix (Fin N) (Fin N) ℂ}
    (hS : ∀ p q, IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt y (S p q) z (Sz p q))
    (hT : ∀ p q, IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt y (T p q) z (Tz p q)) (p q : Fin N) :
    IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt y ((S * T) p q) z ((Sz * Tz) p q) := by
  simp only [Matrix.mul_apply]
  exact IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt.sum _ fun r _ => (hS p r).mul (hT r q)

theorem isValueAt_one_matrix (p q : Fin N) :
    IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt y ((1 : Matrix (Fin N) (Fin N) Ω) p q) z
      ((1 : Matrix (Fin N) (Fin N) ℂ) p q) := by
  rcases eq_or_ne p q with rfl | h
  · simpa using IndefiniteRowSideFullHecke.LowerBoundFree.isValueAt_one (y := y) (z := z)
  · simpa [Matrix.one_apply_ne h] using IndefiniteRowSideFullHecke.LowerBoundFree.isValueAt_zero (y := y) (z := z)

theorem valM_eq (hz : z ∈ mcPts (mCoordIdeal y)) {S : Matrix (Fin N) (Fin N) Ω}
    {Sz : Matrix (Fin N) (Fin N) ℂ} (hS : ∀ p q, IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt y (S p q) z (Sz p q)) :
    valM y S z = Sz := by
  ext p q
  exact IndefiniteRowSideFullHecke.LowerBoundFree.valAt_eq hz (hS p q)

theorem regularAt_smul {a : Ω} (s : K → ℂ) (hs : ∀ k, s k ≠ 0)
    (ha : IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y a z) :
    IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y a (fun p => s p.1 * z p) :=
  ⟨_, ha.choose_spec.smul s hs⟩

theorem regularAt_conj {a : Ω} (ha : IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y a z) :
    IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y a (fun p => starRingEnd ℂ (z p)) :=
  ⟨_, ha.choose_spec.conj⟩

theorem isLocSection_smul {W : ChartBundle ℤ (segreCoord y) N E} {e : E} (s : K → ℂ)
    (hs : ∀ k, s k ≠ 0) {z' : (Σ k, ι k) → ℂ} (hz' : z' = fun p => s p.1 * z p)
    (he : IndefiniteRowSideFullHecke.LowerBoundFree.IsLocSection y W z e) : IndefiniteRowSideFullHecke.LowerBoundFree.IsLocSection y W z' e := by
  subst hz'
  obtain ⟨c, hc, m, a, t, ht, ha, rfl⟩ := he
  exact ⟨c, fun k => mul_ne_zero (hs k) (hc k), m, a, t, ht, fun l => regularAt_smul s hs (ha l), rfl⟩

theorem isLocSection_conj {W : ChartBundle ℤ (segreCoord y) N E} {e : E}
    (he : IndefiniteRowSideFullHecke.LowerBoundFree.IsLocSection y W z e) :
    IndefiniteRowSideFullHecke.LowerBoundFree.IsLocSection y W (fun p => starRingEnd ℂ (z p)) e := by
  obtain ⟨c, hc, m, a, t, ht, ha, rfl⟩ := he
  exact ⟨c, fun k => (map_ne_zero _).2 (hc k), m, a, t, ht, fun l => regularAt_conj (ha l), rfl⟩

theorem isFrameAt_smul {W : ChartBundle ℤ (segreCoord y) N E} {b : Fin N → E} (s : K → ℂ)
    (hs : ∀ k, s k ≠ 0) (hb : IndefiniteRowSideFullHecke.LowerBoundFree.IsFrameAt y W z b) :
    IndefiniteRowSideFullHecke.LowerBoundFree.IsFrameAt y W (fun p => s p.1 * z p) b := by
  refine ⟨fun q => isLocSection_smul s hs rfl (hb.1 q), fun e he => ?_⟩
  have he' : IndefiniteRowSideFullHecke.LowerBoundFree.IsLocSection y W z e :=
    isLocSection_smul (fun k => (s k)⁻¹) (fun k => inv_ne_zero (hs k))
      (funext fun p => (inv_mul_cancel_left₀ (hs p.1) (z p)).symm) he
  obtain ⟨a, ha, hae⟩ := hb.2 e he'
  exact ⟨a, fun q => regularAt_smul s hs (ha q), hae⟩

theorem isFrameAt_conj {W : ChartBundle ℤ (segreCoord y) N E} {b : Fin N → E}
    (hb : IndefiniteRowSideFullHecke.LowerBoundFree.IsFrameAt y W z b) :
    IndefiniteRowSideFullHecke.LowerBoundFree.IsFrameAt y W (fun p => starRingEnd ℂ (z p)) b := by
  refine ⟨fun q => isLocSection_conj (hb.1 q), fun e he => ?_⟩
  have he' : IndefiniteRowSideFullHecke.LowerBoundFree.IsLocSection y W z e := by
    have h := isLocSection_conj he
    simp only [RCLike.conj_conj] at h
    exact h
  obtain ⟨a, ha, hae⟩ := hb.2 e he'
  exact ⟨a, fun q => regularAt_conj (ha q), hae⟩

theorem inFrameDomain_smul {c : (k : K) → ι k} {f : Ω} (s : K → ℂ) (hs : ∀ k, s k ≠ 0)
    (hd : InFrameDomain y c f z) : InFrameDomain y c f (fun p => s p.1 * z p) := by
  obtain ⟨hc, v, hv, hv0⟩ := hd
  exact ⟨fun k => mul_ne_zero (hs k) (hc k), v, isValueAt_iff.2 ((isValueAt_iff.1 hv).smul s hs), hv0⟩

theorem inFrameDomain_conj {c : (k : K) → ι k} {f : Ω} (hd : InFrameDomain y c f z) :
    InFrameDomain y c f (fun p => starRingEnd ℂ (z p)) := by
  obtain ⟨hc, v, hv, hv0⟩ := hd
  exact ⟨fun k => (map_ne_zero _).2 (hc k), starRingEnd ℂ v, isValueAt_iff.2 (isValueAt_iff.1 hv).conj,
    (map_ne_zero _).2 hv0⟩

theorem eventually_regularAt {m : ℕ} {γ : (Fin m → ℂ) → (Σ k, ι k) → ℂ} {w : Fin m → ℂ}
    (hγ : ContinuousAt γ w) {a : Ω} (ha : IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y a (γ w)) :
    ∀ᶠ w' in 𝓝 w, IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y a (γ w') := by
  obtain ⟨v, d, g, h, hg, hh, hy, hyg, hz, -⟩ := ha
  have hc : ContinuousAt (fun w' => eval (γ w') (map (Int.castRingHom ℂ) h)) w :=
    (MvPolynomial.continuous_eval (map (Int.castRingHom ℂ) h)).continuousAt.comp hγ
  filter_upwards [hc.eventually_ne hz] with w' hw'
  exact ⟨_, d, g, h, hg, hh, hy, hyg, hw', (div_mul_cancel₀ _ hw').symm⟩

theorem eventually_inFrameDomain {m : ℕ} {γ : (Fin m → ℂ) → (Σ k, ι k) → ℂ} {w : Fin m → ℂ}
    (hγ : ContinuousAt γ w) {c : (k : K) → ι k} {f : Ω} (hd : InFrameDomain y c f (γ w)) :
    ∀ᶠ w' in 𝓝 w, InFrameDomain y c f (γ w') := by
  obtain ⟨hc, v, ⟨d, g, h, hg, hh, hy, hyg, hz, hv⟩, hv0⟩ := hd
  have hgz : eval (γ w) (map (Int.castRingHom ℂ) g) ≠ 0 := by
    intro h0
    rw [h0, zero_div] at hv
    exact hv0 hv
  have hG : ContinuousAt (fun w' => eval (γ w') (map (Int.castRingHom ℂ) g)) w :=
    (MvPolynomial.continuous_eval (map (Int.castRingHom ℂ) g)).continuousAt.comp hγ
  have hH : ContinuousAt (fun w' => eval (γ w') (map (Int.castRingHom ℂ) h)) w :=
    (MvPolynomial.continuous_eval (map (Int.castRingHom ℂ) h)).continuousAt.comp hγ
  have hC : ∀ᶠ w' in 𝓝 w, ∀ k, γ w' ⟨k, c k⟩ ≠ 0 := Filter.eventually_all.2 fun k =>
    ((continuous_apply (⟨k, c k⟩ : Σ k, ι k)).continuousAt.comp hγ).eventually_ne (hc k)
  filter_upwards [hG.eventually_ne hgz, hH.eventually_ne hz, hC] with w' hg' hh' hc'
  exact ⟨hc', _, ⟨d, g, h, hg, hh, hy, hyg, hh', rfl⟩, div_ne_zero hg' hh'⟩

end HermMetricEq

end GroundTheory.Heights₂.Heights.LowerBoundFree
