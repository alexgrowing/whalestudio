import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.CellAbs

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.RswCell.NullCompl

open PositivityTheory.Rg.Rsw.Cell

variable {G : Type} [Group G]

theorem rp_mk_inv (P : Subgroup G) (g : G) : ∃ p ∈ P, rp (P := P) (((g⁻¹ : G)) : G ⧸ P) = p * g := by
  refine ⟨(Quotient.out ((g⁻¹ : G) : G ⧸ P))⁻¹ * g⁻¹, ?_, ?_⟩
  · exact QuotientGroup.eq.mp (QuotientGroup.out_eq' ((g⁻¹ : G) : G ⧸ P))
  · simp [rp]

theorem rp_smul (P : Subgroup G) (x : G) (q : G ⧸ P) : ∃ p ∈ P, rp (x⁻¹ • q) = p * (rp q * x) := by
  refine ⟨(Quotient.out (x⁻¹ • q))⁻¹ * (x⁻¹ * Quotient.out q), ?_, ?_⟩
  · rw [← QuotientGroup.eq, QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_coe,
      QuotientGroup.out_eq']
  · simp [rp, mul_assoc]

variable [TopologicalSpace G]

theorem isOpen_rp [IsTopologicalGroup G] (P : Subgroup G) {Ω : Set G} (hΩ : IsOpen Ω)
    (hP : ∀ p ∈ P, ∀ x ∈ Ω, p * x ∈ Ω) : IsOpen {q : G ⧸ P | rp q ∈ Ω} := by
  have hset : {q : G ⧸ P | rp q ∈ Ω} = ((↑) : G → G ⧸ P) '' {g | g⁻¹ ∈ Ω} := by
    ext q
    constructor
    · intro hq
      refine ⟨(rp q)⁻¹, by simpa using hq, ?_⟩
      simp only [rp, inv_inv]
      exact QuotientGroup.out_eq' q
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨p, hp, hrp⟩ := rp_mk_inv P g⁻¹
      simp only [inv_inv] at hrp
      show rp (g : G ⧸ P) ∈ Ω
      rw [hrp]
      exact hP p hp _ hg
  rw [hset]
  exact QuotientGroup.isOpenMap_coe _ (hΩ.preimage continuous_inv)

theorem ratio_bound {P : Subgroup G} {h : G → ℝ} {mu : (G → ℂ) → ℂ} [IsTopologicalGroup G]
    (hS : Setup P h mu) {V : Set G} (hV : IsCompact V) :
    ∃ B : ℝ, ∀ g, ∀ x ∈ V, h (g * x) / h g ≤ B := by
  obtain ⟨C, hC, hcov⟩ := hS.cocpt
  have hcont : Continuous (fun z : G × G => h (z.1 * z.2) / h z.1) :=
    (hS.cont.comp continuous_mul).div (hS.cont.comp continuous_fst) (fun z => (hS.pos _).ne')
  obtain ⟨B, hB⟩ := (hC.prod hV).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨B, fun g x hx => ?_⟩
  obtain ⟨q, hq, c, hc, rfl⟩ := hcov g
  have hlaw := hS.law q hq c (c * x)
  have heq : h (q * c * x) / h (q * c) = h (c * x) / h c := by
    rw [div_eq_div_iff (hS.pos _).ne' (hS.pos _).ne', mul_assoc]
    linear_combination (-1 : ℝ) * hlaw
  rw [heq]
  have hb := hB (c, x) ⟨hc, hx⟩
  simp only [Real.norm_eq_abs] at hb
  exact le_trans (le_abs_self _) hb

theorem local_null [IsTopologicalGroup G] [LocallyCompactSpace G] {P : Subgroup G}
    [MeasurableSpace (G ⧸ P)] [BorelSpace (G ⧸ P)] {h : G → ℝ} {mu : (G → ℂ) → ℂ}
    (hS : Setup P h mu) {ν : Measure (G ⧸ P)} [IsFiniteMeasure ν]
    (hInv : ∀ x, Inv P h mu x → ∀ F : G ⧸ P → ℝ≥0∞, Measurable F →
      ∫⁻ q, F (x⁻¹ • q) * ENNReal.ofReal (h (rp q * x) / h (rp q)) ∂ν = ∫⁻ q, F q ∂ν)
    {Ω : Set G} (hΩ : IsOpen Ω) (hP : ∀ p ∈ P, ∀ x ∈ Ω, p * x ∈ Ω) (hF : Few P h mu Ω) (q0 : G ⧸ P) :
    ∃ W : Set (G ⧸ P), IsOpen W ∧ q0 ∈ W ∧ ν ({q | rp q ∉ Ω} ∩ W) = 0 := by
  classical
  obtain ⟨U, d, hUo, hgU, hUP, hfew⟩ := hF (rp q0)
  have hφ : Continuous (fun z : G × G => rp q0 * z.1 * z.2⁻¹) :=
    (continuous_const.mul continuous_fst).mul continuous_snd.inv
  have hmem : (fun z : G × G => rp q0 * z.1 * z.2⁻¹) ⁻¹' U ∈ 𝓝 ((1 : G), (1 : G)) :=
    hφ.continuousAt.preimage_mem_nhds (hUo.mem_nhds (by simpa using hgU))
  obtain ⟨N0, hN0, N1, hN1, hsub⟩ := mem_nhds_prod_iff.mp hmem
  obtain ⟨V, hV1, hVN1, hVc⟩ := local_compact_nhds hN1
  obtain ⟨B, hB⟩ := ratio_bound hS hVc
  have hNo : IsOpen (interior N0) := isOpen_interior
  have h1N : (1 : G) ∈ interior N0 := mem_interior_iff_mem_nhds.mpr hN0
  let U' : Set G := {y | ∃ p ∈ P, ∃ n ∈ interior N0, y = p * (rp q0 * n)}
  have hU'o : IsOpen U' := by
    rw [isOpen_iff_forall_mem_open]
    rintro y ⟨p, hp, n, hn, rfl⟩
    refine ⟨(fun z => (p * rp q0)⁻¹ * z) ⁻¹' interior N0, ?_, ?_, ?_⟩
    · intro z hz
      exact ⟨p, hp, (p * rp q0)⁻¹ * z, hz, by group⟩
    · exact hNo.preimage (continuous_const.mul continuous_id)
    · show (p * rp q0)⁻¹ * (p * (rp q0 * n)) ∈ interior N0
      simpa [mul_assoc] using hn
  have hU'P : ∀ p ∈ P, ∀ x ∈ U', p * x ∈ U' := by
    rintro p hp x ⟨p', hp', n, hn, rfl⟩
    exact ⟨p * p', P.mul_mem hp hp', n, hn, (mul_assoc _ _ _).symm⟩
  have hgU' : rp q0 ∈ U' := ⟨1, P.one_mem, 1, h1N, by simp⟩
  have hshift : ∀ y ∈ U', ∀ γ ∈ V, y * γ⁻¹ ∈ U := by
    rintro y ⟨p, hp, n, hn, rfl⟩ γ hγ
    have h1 := hsub (Set.mk_mem_prod (interior_subset hn) (hVN1 hγ))
    simp only [Set.mem_preimage] at h1
    have h2 := hUP p hp _ h1
    simpa [mul_assoc] using h2
  refine ⟨{q | rp q ∈ U'}, isOpen_rp P hU'o hU'P, hgU', ?_⟩
  have hopenU : IsOpen {q : G ⧸ P | rp q ∈ U} := isOpen_rp P hUo hUP
  have hopenΩ0 : IsOpen {q : G ⧸ P | rp q ∈ Ω} := isOpen_rp P hΩ hP
  have hopenR : ∀ (S : Set G), IsOpen S → (∀ p ∈ P, ∀ x ∈ S, p * x ∈ S) → ∀ γ : G,
      IsOpen {q : G ⧸ P | rp q * γ ∈ S} := fun S hSo hSP γ =>
    isOpen_rp P (hSo.preimage (continuous_mul_const γ)) (fun p hp x hx => by
      show p * x * γ ∈ S
      rw [mul_assoc]
      exact hSP p hp _ hx)
  let A : G → Set (G ⧸ P) := fun γ => {q | rp q ∈ U} ∩ {q | rp q * γ ∈ Ω}ᶜ
  let E' : G → Set (G ⧸ P) := fun γ => {q | rp q ∈ Ω}ᶜ ∩ {q | rp q * γ⁻¹ ∈ U}
  have hAm : ∀ γ, MeasurableSet (A γ) := fun γ =>
    hopenU.measurableSet.inter (hopenR Ω hΩ hP γ).measurableSet.compl
  have hE'm : ∀ γ, MeasurableSet (E' γ) := fun γ =>
    hopenΩ0.measurableSet.compl.inter (hopenR U hUo hUP γ⁻¹).measurableSet
  have hEsub : ∀ γ ∈ V, {q | rp q ∉ Ω} ∩ {q | rp q ∈ U'} ⊆ E' γ := by
    rintro γ hγ q ⟨hq1, hq2⟩
    exact ⟨hq1, hshift _ hq2 γ hγ⟩
  have htrans : ∀ γ q, γ⁻¹ • q ∈ E' γ → q ∈ A γ := by
    rintro γ q ⟨h1, h2⟩
    obtain ⟨p, hp, hrp⟩ := rp_smul P γ q
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at h1 h2
    rw [hrp] at h1 h2
    refine ⟨?_, ?_⟩
    · have h3 := hUP p⁻¹ (P.inv_mem hp) _ h2
      show rp q ∈ U
      simpa [mul_assoc] using h3
    · show ¬ (rp q * γ ∈ Ω)
      intro h4
      exact h1 (hP p hp _ h4)
  have hfin : ENNReal.ofReal B * ((d : ℝ≥0∞) * ν univ) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top d) (measure_ne_top ν univ))
  by_contra hne
  obtain ⟨M, hM⟩ := ENNReal.exists_nat_mul_gt hne hfin
  obtain ⟨γ, hγ, hcnt⟩ := hfew V hV1 M
  have hstep : ∀ j, ν ({q | rp q ∉ Ω} ∩ {q | rp q ∈ U'}) ≤ ENNReal.ofReal B * ν (A (γ j)) := by
    intro j
    have hI := hInv (γ j) (hγ j).2 ((E' (γ j)).indicator 1) (measurable_one.indicator (hE'm _))
    calc ν ({q | rp q ∉ Ω} ∩ {q | rp q ∈ U'}) ≤ ν (E' (γ j)) := measure_mono (hEsub _ (hγ j).1)
      _ = ∫⁻ q, (E' (γ j)).indicator 1 q ∂ν := (lintegral_indicator_one (hE'm _)).symm
      _ = ∫⁻ q, (E' (γ j)).indicator 1 ((γ j)⁻¹ • q) *
            ENNReal.ofReal (h (rp q * γ j) / h (rp q)) ∂ν := hI.symm
      _ ≤ ∫⁻ q, (A (γ j)).indicator 1 q * ENNReal.ofReal B ∂ν := by
          apply lintegral_mono
          intro q
          apply mul_le_mul'
          · simp only [Set.indicator_apply, Pi.one_apply]
            split_ifs with h1 h2 <;>
              first | exact le_rfl | exact zero_le | exact absurd (htrans _ _ h1) h2
          · exact ENNReal.ofReal_le_ofReal (hB _ _ (hγ j).1)
      _ = ν (A (γ j)) * ENNReal.ofReal B := by
          rw [lintegral_mul_const _ (measurable_one.indicator (hAm _)), lintegral_indicator_one (hAm _)]
      _ = ENNReal.ofReal B * ν (A (γ j)) := mul_comm _ _
  have hpt : ∀ q, ∑ j, (A (γ j)).indicator 1 q ≤ (d : ℝ≥0∞) := by
    intro q
    by_cases hq : rp q ∈ U
    · have hc := hcnt (rp q) hq
      have e : (↑(Finset.univ.filter (fun j => rp q * γ j ∉ Ω)) : Set (Fin M))
          = {j | rp q * γ j ∉ Ω} := by
        ext j
        simp
      rw [← e, Set.ncard_coe_finset] at hc
      calc ∑ j, (A (γ j)).indicator (1 : G ⧸ P → ℝ≥0∞) q
          ≤ ∑ j, (if rp q * γ j ∉ Ω then (1 : ℝ≥0∞) else 0) := by
            apply Finset.sum_le_sum
            intro j _
            simp only [Set.indicator_apply, Pi.one_apply]
            split_ifs with h1 h2 <;> first | exact le_rfl | exact zero_le | exact absurd h2 h1.2
        _ = ((Finset.univ.filter (fun j => rp q * γ j ∉ Ω)).card : ℝ≥0∞) := by
            rw [Finset.sum_boole]
        _ ≤ d := by exact_mod_cast hc
    · calc ∑ j, (A (γ j)).indicator (1 : G ⧸ P → ℝ≥0∞) q = 0 :=
            Finset.sum_eq_zero (fun j _ => Set.indicator_of_notMem (fun h => hq h.1) _)
        _ ≤ d := zero_le
  have hsumA : ∑ j, ν (A (γ j)) ≤ (d : ℝ≥0∞) * ν univ := by
    calc ∑ j, ν (A (γ j)) = ∑ j, ∫⁻ q, (A (γ j)).indicator 1 q ∂ν :=
          Finset.sum_congr rfl (fun j _ => (lintegral_indicator_one (hAm _)).symm)
      _ = ∫⁻ q, ∑ j, (A (γ j)).indicator 1 q ∂ν :=
          (lintegral_finsetSum _ (fun j _ => measurable_one.indicator (hAm _))).symm
      _ ≤ ∫⁻ _q, (d : ℝ≥0∞) ∂ν := lintegral_mono hpt
      _ = (d : ℝ≥0∞) * ν univ := lintegral_const _
  have hMle : (M : ℝ≥0∞) * ν ({q | rp q ∉ Ω} ∩ {q | rp q ∈ U'})
      ≤ ENNReal.ofReal B * ((d : ℝ≥0∞) * ν univ) := by
    calc (M : ℝ≥0∞) * ν ({q | rp q ∉ Ω} ∩ {q | rp q ∈ U'})
        = ∑ _j : Fin M, ν ({q | rp q ∉ Ω} ∩ {q | rp q ∈ U'}) := by simp
      _ ≤ ∑ j, ENNReal.ofReal B * ν (A (γ j)) := Finset.sum_le_sum (fun j _ => hstep j)
      _ = ENNReal.ofReal B * ∑ j, ν (A (γ j)) := (Finset.mul_sum _ _ _).symm
      _ ≤ ENNReal.ofReal B * ((d : ℝ≥0∞) * ν univ) := by gcongr
  exact absurd hM (not_lt.mpr hMle)

theorem nullC_of_invM : InvM → NullC := by
  intro hInvM
  unfold NullC ForSet
  intro G _ _ _ _ _ _ P _ _ h mu hS ν hRepr Ω hΩ hP hF
  have : IsFiniteMeasure ν := hRepr.1
  have hInv : ∀ x : G, Inv P h mu x → ∀ F : G ⧸ P → ℝ≥0∞, Measurable F →
      ∫⁻ q, F (x⁻¹ • q) * ENNReal.ofReal (h (rp q * x) / h (rp q)) ∂ν = ∫⁻ q, F q ∂ν :=
    fun x hx => (hInvM G P h mu hS ν hRepr x hx).2
  apply measure_null_of_locally_null
  intro q0 _
  obtain ⟨W, hWo, hq0W, hWnull⟩ := local_null hS hInv hΩ hP hF q0
  exact ⟨{q | rp q ∉ Ω} ∩ W, inter_mem_nhdsWithin _ (hWo.mem_nhds hq0W), hWnull⟩

end GlobalTheory.CompanionTheory.RswCell.NullCompl
