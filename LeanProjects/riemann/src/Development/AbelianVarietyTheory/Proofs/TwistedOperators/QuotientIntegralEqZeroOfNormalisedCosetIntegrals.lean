import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas

open MeasureTheory Set GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal

noncomputable section

namespace GlobalTheory.Orb

theorem isMulRightInvariant_of_isMulCommutative {G : Type*} [Group G] [IsMulCommutative G] [MeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] : μ.IsMulRightInvariant :=
  ⟨fun g => by
    have : (fun x : G => x * g) = fun x => g * x := funext fun x => IsMulCommutative.is_comm.comm x g
    rw [this]
    exact map_mul_left_eq_self μ g⟩

section Weight

variable {H : Type} [Group H]

theorem exists_nt_mul {T N : Subgroup H} (hnorm : ∀ t ∈ T, ∀ n ∈ N, t * n * t⁻¹ ∈ N) (p q : N × T) :
    ∃ r : N × T, (r.1 : H) * r.2 = ((p.1 : H) * p.2) * ((q.1 : H) * q.2) :=
  ⟨(p.1 * ⟨(p.2 : H) * q.1 * (p.2 : H)⁻¹, hnorm _ p.2.2 _ q.1.2⟩, p.2 * q.2), by simp [mul_assoc]⟩

theorem exists_nt_inv {T N : Subgroup H} (hnorm : ∀ t ∈ T, ∀ n ∈ N, t * n * t⁻¹ ∈ N) (q : N × T) :
    ∃ r : N × T, (r.1 : H) * r.2 = ((q.1 : H) * q.2)⁻¹ :=
  ⟨(⟨(q.2 : H)⁻¹ * (q.1 : H)⁻¹ * (q.2 : H)⁻¹⁻¹, hnorm _ (inv_mem q.2.2) _ (inv_mem q.1.2)⟩, q.2⁻¹), by
    simp only [Subgroup.coe_inv, inv_inv, mul_inv_rev]; group⟩

variable [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H] [LocallyCompactSpace H]
  [T2Space H] [MeasurableSpace H] [BorelSpace H]

theorem exists_weight_nt (T N : Subgroup H) (hT : IsClosed (T : Set H)) (hN : IsClosed (N : Set H))
    (hnorm : ∀ t ∈ T, ∀ n ∈ N, t * n * t⁻¹ ∈ N)
    (hj : Topology.IsClosedEmbedding (fun p : N × T => (p.1 : H) * p.2))
    (dt : Measure T) [dt.IsHaarMeasure] [dt.IsMulRightInvariant]
    (dn : Measure N) [dn.IsHaarMeasure] [dn.IsMulRightInvariant] :
    ∃ β : H → ℝ≥0∞, Measurable β ∧ (∀ x, β x ≠ ∞) ∧ (∀ n ∈ N, ∀ x, β (n * x) = β x) ∧
      ∀ x, ∫⁻ t : T, β (t * x) ∂dt = 1 := by
  haveI : LocallyCompactSpace T := hT.locallyCompactSpace
  haveI : LocallyCompactSpace N := hN.locallyCompactSpace
  set j : N × T → H := fun p => (p.1 : H) * p.2 with hjdef
  have hjc : Continuous j := hj.continuous
  let K := CompactExhaustion.choice H
  let W : ℕ → Set H := fun k => interior (K (k + 1))
  have hWo : ∀ k, IsOpen (W k) := fun k => isOpen_interior
  let U : ℕ → Set H := fun k => {x | ∃ p : N × T, j p * x ∈ W k}
  have hUfwd : ∀ k q x, x ∈ U k → j q * x ∈ U k := by
    rintro k q x ⟨p, hp⟩
    obtain ⟨r, hr⟩ := exists_nt_inv hnorm q
    obtain ⟨s, hs⟩ := exists_nt_mul hnorm p r
    refine ⟨s, ?_⟩
    have e : j s * (j q * x) = j p * x := by
      rw [show j s = j p * j r from hs, show j r = (j q)⁻¹ from hr]; group
    rw [e]; exact hp
  have hU : ∀ k q x, j q * x ∈ U k ↔ x ∈ U k := by
    refine fun k q x => ⟨fun h => ?_, hUfwd k q x⟩
    obtain ⟨r, hr⟩ := exists_nt_inv hnorm q
    have := hUfwd k r _ h
    rwa [show j r = (j q)⁻¹ from hr, inv_mul_cancel_left] at this
  have hUo : ∀ k, IsOpen (U k) := fun k => by
    have : U k = ⋃ p : N × T, (fun x => j p * x) ⁻¹' W k := by ext x; simp [U]
    rw [this]
    exact isOpen_iUnion fun p => (hWo k).preimage (continuous_mul_left _)
  have hcov : ∀ x, ∃ k, x ∈ U k := fun x => by
    obtain ⟨k, hk⟩ := K.exists_mem x
    exact ⟨k, (1, 1), by simpa [j] using K.subset_interior_succ k hk⟩
  let P : ℕ → Set H := disjointed U
  have hPm : ∀ k, MeasurableSet (P k) := MeasurableSet.disjointed fun k => (hUo k).measurableSet
  have hP : ∀ k q x, j q * x ∈ P k ↔ x ∈ P k := fun k q x => by
    simp only [P, disjointed_eq_inter_compl, mem_inter_iff, mem_iInter, mem_compl_iff, hU]
  have hPcov : ∀ x, ∃ k, x ∈ P k := fun x => by
    have : x ∈ ⋃ k, P k := by rw [iUnion_disjointed]; exact mem_iUnion.2 (hcov x)
    exact mem_iUnion.1 this
  have hPd : ∀ k k' x, x ∈ P k → x ∈ P k' → k = k' := fun k k' x h h' => by
    by_contra hne
    exact Set.disjoint_left.1 (disjoint_disjointed U hne) h h'
  let h : H → ℝ≥0∞ := fun x => ∑' k, (P k).indicator ((W k).indicator 1) x
  have hh : Measurable h := Measurable.ennreal_tsum fun k =>
    (measurable_one.indicator (hWo k).measurableSet).indicator (hPm k)
  have hval : ∀ k x, x ∈ P k → ∀ q, h (j q * x) = (W k).indicator 1 (j q * x) := by
    intro k x hx q
    have hx' := (hP k q x).2 hx
    refine (tsum_eq_single k fun k' hk' => ?_).trans (indicator_of_mem hx' _)
    exact indicator_of_notMem (fun h' => hk' (hPd _ _ _ h' hx')) _
  let g : H → ℝ≥0∞ := fun x => ∫⁻ n : N, h (n * x) ∂dn
  let I : H → ℝ≥0∞ := fun x => ∫⁻ t : T, g (t * x) ∂dt
  have hg : Measurable g := measurable_fiber hh
  have hI : Measurable I := measurable_fiber hg
  have hgN : ∀ n ∈ N, ∀ x, g (n * x) = g x := fun n hn x => by
    simpa [g, mul_assoc] using lintegral_mul_right_eq_self (μ := dn) (fun m : N => h (m * x)) ⟨n, hn⟩
  have hIN : ∀ n ∈ N, ∀ x, I (n * x) = I x := fun n hn x => by
    refine lintegral_congr fun t => ?_
    have e : (t : H) * (n * x) = ((t : H) * n * (t : H)⁻¹) * (t * x) := by group
    rw [e, hgN _ (hnorm _ t.2 _ hn)]
  have hIT : ∀ s ∈ T, ∀ x, I (s * x) = I x := fun s hs x => by
    simpa [I, mul_assoc] using lintegral_mul_right_eq_self (μ := dt) (fun t : T => g (t * x)) ⟨s, hs⟩
  have hIprod : ∀ x, I x = ∫⁻ p, h (j p * x) ∂(dn.prod dt) := fun x => by
    rw [lintegral_prod_symm (fun p => h (j p * x)) (hh.comp (hjc.measurable.mul_const x)).aemeasurable]
    simp [I, g, j, mul_assoc]
  have hcpt : ∀ k x, IsCompact ((fun y => y * x) ⁻¹' K (k + 1)) := fun k x => by
    have := (Homeomorph.mulRight x).isCompact_preimage.2 (K.isCompact (k + 1))
    simpa using this
  have hIpos : ∀ x, I x ≠ 0 ∧ I x ≠ ∞ := fun x => by
    obtain ⟨k, hk⟩ := hPcov x
    set E := (fun p => j p * x) ⁻¹' W k with hEdef
    have hE : IsOpen E := (hWo k).preimage (hjc.mul continuous_const)
    have e : I x = dn.prod dt E := by
      rw [hIprod, ← lintegral_indicator_one hE.measurableSet]
      exact lintegral_congr fun p => by rw [hval k x hk p]; rfl
    obtain ⟨p, hp⟩ := disjointed_subset U k hk
    refine ⟨e ▸ hE.measure_ne_zero _ ⟨p, hp⟩, e ▸ ?_⟩
    refine (measure_mono (μ := dn.prod dt) (s := E) (t := j ⁻¹' ((fun y => y * x) ⁻¹' K (k + 1))) ?_).trans_lt
      (hj.isCompact_preimage (hcpt k x)).measure_lt_top |>.ne
    intro q hq
    exact interior_subset (s := K (k + 1)) hq
  have hgfin : ∀ x, g x ≠ ∞ := fun x => by
    obtain ⟨k, hk⟩ := hPcov x
    set C : Set N := (↑) ⁻¹' ((fun y => y * x) ⁻¹' K (k + 1))
    have hC : IsCompact C := hN.isClosedEmbedding_subtypeVal.isCompact_preimage (hcpt k x)
    refine ne_of_lt (lt_of_le_of_lt ?_ (hC.measure_lt_top (μ := dn)))
    rw [← lintegral_indicator_one hC.measurableSet]
    refine lintegral_mono fun n => ?_
    have e : h ((n : H) * x) = (W k).indicator 1 ((n : H) * x) := by
      simpa [j] using hval k x hk (n, 1)
    rw [e]
    by_cases hn : (n : H) * x ∈ W k
    · rw [indicator_of_mem hn, indicator_of_mem (show n ∈ C from interior_subset (s := K (k + 1)) hn)]; exact le_rfl
    · rw [indicator_of_notMem hn]; exact zero_le
  refine ⟨fun x => g x * (I x)⁻¹, hg.mul hI.inv, fun x => ENNReal.mul_ne_top (hgfin x)
    (ENNReal.inv_ne_top.2 (hIpos x).1), fun n hn x => by simp only [hgN n hn, hIN n hn], fun x => ?_⟩
  have e : ∀ t : T, g (t * x) * (I (t * x))⁻¹ = g (t * x) * (I x)⁻¹ := fun t => by rw [hIT _ t.2]
  simp_rw [e]
  rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 (hIpos x).1)]
  exact ENNReal.mul_inv_cancel (hIpos x).1 (hIpos x).2

end Weight

theorem quotInt_eq_zero_of_integral_coset_eq_zero : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
    (T N : Subgroup H), IsClosed (T : Set H) → IsClosed (N : Set H) → IsMulCommutative T →
    (∀ t ∈ T, ∀ n ∈ N, t * n * t⁻¹ ∈ N) → Topology.IsClosedEmbedding (fun p : N × T => (p.1 : H) * p.2) →
    ∀ (dh : Measure H) [dh.IsHaarMeasure] (dt : Measure T) [dt.IsHaarMeasure] (dn : Measure N) [dn.IsHaarMeasure]
    [dn.IsMulRightInvariant] (φ : H → ℂ), Measurable φ → LeftInv T φ →
    Integrable (descend T φ) (quotMeas T dt dh) → (∀ x, ∫ n : N, φ (n * x) ∂dn = 0) → quotInt T dt dh φ = 0 := by
  intro H _ _ _ _ _ _ _ _ T N hT hN hc hnorm hj dh _ dt _ dn _ _ φ hφ hφT hint h0
  haveI : dt.IsMulRightInvariant := isMulRightInvariant_of_isMulCommutative dt
  haveI : LocallyCompactSpace T := hT.locallyCompactSpace
  haveI : LocallyCompactSpace N := hN.locallyCompactSpace
  obtain ⟨β, hβm, hβf, hβN, hβ1⟩ := exists_weight_nt T N hT hN hnorm hj dt dn
  have hν : quotMeas T dt dh = (dh.withDensity β).map (mk T) :=
    (isQuotMeasure_quotMeas dt dh hT).eq_map hβm hβ1
  have hlt : ∀ᵐ x ∂dh, β x < ∞ := .of_forall fun x => lt_top_iff_ne_top.2 (hβf x)
  have hD : Measurable (descend T φ) := measurable_descend hφT hφ
  have hcomp : descend T φ ∘ mk T = φ := funext hφT.descend_mk
  have hφβ : Integrable φ (dh.withDensity β) := by
    rw [hν] at hint
    have := (integrable_map_measure hD.aestronglyMeasurable measurable_mk.aemeasurable).1 hint
    rwa [hcomp] at this
  have hF : Integrable (fun x => (β x).toReal • φ x) dh :=
    (integrable_withDensity_iff_integrable_smul' hβm hlt).1 hφβ
  have e1 : quotInt T dt dh φ = ∫ x, (β x).toReal • φ x ∂dh := by
    rw [quotInt, hν, integral_map measurable_mk.aemeasurable hD.aestronglyMeasurable,
      ← integral_withDensity_eq_integral_toReal_smul hβm hlt]
    exact integral_congr_ae (.of_forall fun x => hφT.descend_mk x)
  have hW := (weil_integral (dt := dn) hN hF).2
  have e2 : (fun x => ∫ n : N, (β (n * x)).toReal • φ (n * x) ∂dn) = fun _ => (0 : ℂ) := funext fun x => by
    have e : ∀ n : N, (β (n * x)).toReal • φ (n * x) = (β x).toReal • φ (n * x) := fun n => by
      rw [hβN _ n.2 x]
    simp_rw [e]
    rw [integral_smul, h0 x, smul_zero]
  rw [e1, ← hW.2, e2]
  simp [quotInt, descend]

end GlobalTheory.Orb
