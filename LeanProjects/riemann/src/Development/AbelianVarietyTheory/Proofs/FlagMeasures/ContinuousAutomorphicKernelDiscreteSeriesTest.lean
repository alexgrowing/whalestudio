import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsAutIdemElementary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SummableAndTsumLeOfBoxCount
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ShellSumMajorant
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountRationalElementsBoundedDistanceStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesCoefficientIntegrableMajorantStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec

theorem decE_dOp_le_exp_floor {n : ℕ} (ε : Fin n → Bool) (h : ℝ) (hn : 1 ≤ n)
    (hh : 32 * (n : ℝ) ^ 2 * Real.sqrt (rkR ε) ≤ h) (g : Formalism.REAL.UJ ε) :
    decE (rkR ε) h (dOp (uMat g)) ≤ Real.exp (-(4 * (n : ℝ) ^ 2 * (⌊dOp (uMat g)⌋₊ : ℝ))) := by
  obtain ⟨-, hHS, -, -, -⟩ := GlobalTheory.Count.Cartan.cartan_distances n ε
  obtain ⟨hd0, -, -, hle, hge⟩ := hHS g g hn
  set d := dOp (uMat g) with hd
  rcases Nat.eq_zero_or_pos (rkR ε) with h0 | hq
  ·
    have hz : d = 0 := by
      have h1 : dHS (uMat g) ≤ 0 := by simpa [h0] using hge
      have h2 : Real.sqrt 2 * d ≤ 0 := hle.trans h1
      have h3 : d ≤ 0 := by
        by_contra hc
        have : 0 < Real.sqrt 2 * d := mul_pos (by positivity) (lt_of_not_ge hc)
        linarith
      exact le_antisymm h3 hd0
    simp [decE, hz, h0]
  · obtain ⟨hanti, hint, -, -⟩ := shell_sum_majorant n (rkR ε) h hn hq hh
    have hfl : ((⌊d⌋₊ : ℕ) : ℝ) ≤ d := Nat.floor_le hd0
    calc decE (rkR ε) h d ≤ decE (rkR ε) h (⌊d⌋₊ : ℕ) :=
          hanti (Set.mem_Ici.mpr (Nat.cast_nonneg _)) (Set.mem_Ici.mpr hd0) hfl
      _ ≤ _ := hint _

theorem continuous_kern_phe : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → 1 ≤ B.I.n →
    LocDec B h → HBig B 32 h → Continuous (fun p : B.I.GA × B.I.GA => kern B.I (phe B d) p.1 p.2) := by
  intro B d h hd hn hl hb
  classical
  obtain ⟨-, he1, he, hec⟩ := GlobalTheory.rowsAut_idem_elementary B
  obtain ⟨hphc, hphm, -⟩ := GlobalTheory.T.discrete_series_coefficient_integrable_majorant B d h hd hl
  obtain ⟨-, -, -, -, hsupp, -, -⟩ := B.e_adm
  have hC := fun v => GlobalTheory.Count.Cartan.cartan_distances B.I.n (B.I.ε v)

  have hKmul : ∀ a w b : B.I.Gf, a ∈ B.I.Kset → w ∈ B.I.Kset → b ∈ B.I.Kset →
      a * w * b⁻¹ ∈ B.I.Kset := by
    intro a w b ha hw hbm
    simp only [AutInst.Kset, Set.mem_ofPred_eq] at ha hw hbm ⊢
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using mul_mem (mul_mem ha hw) (inv_mem hbm)

  obtain ⟨K1, hK1o, hK1one, hK1K⟩ : ∃ K1 : Set B.I.Gf, IsOpen K1 ∧ (1 : B.I.Gf) ∈ K1 ∧ K1 ⊆ B.I.Kset := by
    refine ⟨_, B.I.topf_open 1 le_rfl, ?_, ?_⟩
    · refine ⟨one_mem _, fun y _ => ⟨0, zero_mem _, ?_⟩⟩
      simp
    · intro x hx
      exact hx.1
  obtain ⟨Mv, hMv⟩ : ∃ Mv : InfinitePlace B.I.F → ℝ,
      ∀ v, Mv v = dOp (uMat (1 : Formalism.REAL.UJ (B.I.ε v))) + 1 := ⟨_, fun v => rfl⟩
  rw [continuous_iff_continuousAt]
  rintro ⟨x0, y0⟩

  have c1 : Continuous fun p : B.I.GA × B.I.GA => x0⁻¹ * p.1 := continuous_const.mul continuous_fst
  have c2 : Continuous fun p : B.I.GA × B.I.GA => y0⁻¹ * p.2 := continuous_const.mul continuous_snd
  have hNn : {p : B.I.GA × B.I.GA | (∀ v, dOp (uMat ((x0⁻¹ * p.1).1 v)) < Mv v) ∧ (x0⁻¹ * p.1).2 ∈ K1 ∧
      (∀ v, dOp (uMat ((y0⁻¹ * p.2).1 v)) < Mv v) ∧ (y0⁻¹ * p.2).2 ∈ K1} ∈ nhds (x0, y0) := by
    have e1 : ∀ᶠ p in nhds (x0, y0), ∀ v, dOp (uMat (((x0⁻¹ * p.1) : B.I.GA).1 v)) < Mv v := by
      rw [Filter.eventually_all]
      intro v
      have hc : Continuous fun p : B.I.GA × B.I.GA => dOp (uMat ((x0⁻¹ * p.1).1 v)) :=
        (hC v).2.2.2.2.comp ((continuous_apply v).comp (continuous_fst.comp c1))
      have h0 : dOp (uMat ((x0⁻¹ * (x0, y0).1).1 v)) < Mv v := by simp [hMv]
      exact (hc.tendsto (x0, y0)).eventually (eventually_lt_nhds h0)
    have e2 : ∀ᶠ p in nhds (x0, y0), (x0⁻¹ * p.1).2 ∈ K1 :=
      ((continuous_snd.comp c1).tendsto (x0, y0)).eventually (hK1o.mem_nhds (by simpa using hK1one))
    have e3 : ∀ᶠ p in nhds (x0, y0), ∀ v, dOp (uMat (((y0⁻¹ * p.2) : B.I.GA).1 v)) < Mv v := by
      rw [Filter.eventually_all]
      intro v
      have hc : Continuous fun p : B.I.GA × B.I.GA => dOp (uMat ((y0⁻¹ * p.2).1 v)) :=
        (hC v).2.2.2.2.comp ((continuous_apply v).comp (continuous_fst.comp c2))
      have h0 : dOp (uMat ((y0⁻¹ * (x0, y0).2).1 v)) < Mv v := by simp [hMv]
      exact (hc.tendsto (x0, y0)).eventually (eventually_lt_nhds h0)
    have e4 : ∀ᶠ p in nhds (x0, y0), (y0⁻¹ * p.2).2 ∈ K1 :=
      ((continuous_snd.comp c2).tendsto (x0, y0)).eventually (hK1o.mem_nhds (by simpa using hK1one))
    filter_upwards [e1, e2, e3, e4] with p h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩

  set n := B.I.n with hnn
  set C' : ℝ := |∏ v, d v| * (B.e 1).re * ∏ v, Real.exp (4 * (n : ℝ) ^ 2 * (1 + 2 * Mv v)) with hC'
  have hC'0 : 0 ≤ C' :=
    mul_nonneg (mul_nonneg (abs_nonneg _) he1) (Finset.prod_nonneg fun v _ => (Real.exp_pos _).le)
  set D : B.I.GFset → InfinitePlace B.I.F → ℝ := fun γ v => dOp (uMat ((x0⁻¹ * γ.1 * y0).1 v)) with hD
  set t : B.I.GFset → ℝ := fun γ => if (x0⁻¹ * γ.1 * y0).2 ∈ B.I.Kset then
      C' * ∏ v, Real.exp (-(2 * (2 * (n : ℝ) ^ 2) * (⌊D γ v⌋₊ : ℝ))) else 0 with ht
  have ht0 : ∀ γ, 0 ≤ t γ ∧ t γ ≤ C' * ∏ v, Real.exp (-(2 * (2 * (n : ℝ) ^ 2) * (⌊D γ v⌋₊ : ℝ))) := by
    intro γ
    have hp : 0 ≤ C' * ∏ v, Real.exp (-(2 * (2 * (n : ℝ) ^ 2) * (⌊D γ v⌋₊ : ℝ))) :=
      mul_nonneg hC'0 (Finset.prod_nonneg fun v _ => (Real.exp_pos _).le)
    by_cases hK : (x0⁻¹ * γ.1 * y0).2 ∈ B.I.Kset
    · simp only [ht, if_pos hK]
      exact ⟨hp, le_rfl⟩
    · simp only [ht, if_neg hK]
      exact ⟨le_rfl, hp⟩
  have hDnn : ∀ γ v, 0 ≤ D γ v := fun γ v => ((hC v).2.1 ((x0⁻¹ * γ.1 * y0).1 v) 1 hn).1
  have ha : Real.exp (-(2 * (n : ℝ) ^ 2)) ≤ 1 / 2 := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h1 : Real.exp (-(2 * (n : ℝ) ^ 2)) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by nlinarith)
    have h2 : (1 + 1 : ℝ) ≤ Real.exp 1 := Real.add_one_le_exp 1
    have h3 : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
    have h4 := Real.exp_pos (-1)
    nlinarith
  have hA : 0 ≤ (3 * Real.sqrt n / (tau1 B.I x0 * tau1 B.I y0)) ^ (2 * n ^ 2 * B.I.f) :=
    Even.pow_nonneg ⟨n ^ 2 * B.I.f, by ring⟩ _
  have hcount : ∀ r : InfinitePlace B.I.F → ℝ, (∀ v, 0 ≤ r v) →
      {γ | t γ ≠ 0 ∧ ∀ v, D γ v ≤ r v}.Finite ∧
      (({γ | t γ ≠ 0 ∧ ∀ v, D γ v ≤ r v}.ncard : ℕ) : ℝ) ≤
        (3 * Real.sqrt n / (tau1 B.I x0 * tau1 B.I y0)) ^ (2 * n ^ 2 * B.I.f) *
          Real.exp (2 * (n : ℝ) ^ 2 * ∑ v, r v) := by
    intro r hr
    obtain ⟨hfin, hcard⟩ := GlobalTheory.T.count_rational_elements_bounded_distance B.I x0 y0 r hn hr
    have hsub : {γ | t γ ≠ 0 ∧ ∀ v, D γ v ≤ r v} ⊆ Subtype.val ⁻¹'
        {γ ∈ B.I.GFset | (x0⁻¹ * γ * y0).2 ∈ B.I.Kset ∧ ∀ v, dOp (uMat ((x0⁻¹ * γ * y0).1 v)) ≤ r v} := by
      rintro γ ⟨htγ, hrγ⟩
      refine ⟨γ.2, ?_, hrγ⟩
      by_contra hK
      exact htγ (by simp only [ht, if_neg hK])
    have hpre := Set.Finite.preimage (f := (Subtype.val : B.I.GFset → B.I.GA)) Subtype.val_injective.injOn hfin
    refine ⟨hpre.subset hsub, ?_⟩
    calc (({γ | t γ ≠ 0 ∧ ∀ v, D γ v ≤ r v}.ncard : ℕ) : ℝ)
        ≤ ((Subtype.val ⁻¹' {γ ∈ B.I.GFset | (x0⁻¹ * γ * y0).2 ∈ B.I.Kset ∧
            ∀ v, dOp (uMat ((x0⁻¹ * γ * y0).1 v)) ≤ r v}).ncard : ℝ) :=
          Nat.cast_le.mpr (Set.ncard_le_ncard hsub hpre)
      _ = (({γ ∈ B.I.GFset | (x0⁻¹ * γ * y0).2 ∈ B.I.Kset ∧
            ∀ v, dOp (uMat ((x0⁻¹ * γ * y0).1 v)) ≤ r v}.ncard : ℕ) : ℝ) := by
          rw [Set.ncard_preimage_of_injective_subset_range Subtype.val_injective
            (fun γ hγ => ⟨⟨γ, hγ.1⟩, rfl⟩)]
      _ ≤ _ := hcard
  obtain ⟨hsum, -⟩ := GlobalTheory.summable_and_tsum_le_of_box_count (InfinitePlace B.I.F) B.I.GFset D t
    (2 * (n : ℝ) ^ 2) _ C' hA hC'0 ha hDnn ht0 hcount

  have hcγ : ∀ γ : B.I.GFset, Continuous fun p : B.I.GA × B.I.GA => phe B d (p.1⁻¹ * γ.1 * p.2) := by
    intro γ
    have hm : Continuous fun p : B.I.GA × B.I.GA => p.1⁻¹ * γ.1 * p.2 :=
      (continuous_fst.inv.mul continuous_const).mul continuous_snd
    exact (hphc.comp (continuous_fst.comp hm)).mul (hec.comp (continuous_snd.comp hm))

  have hbound : ∀ γ : B.I.GFset, ∀ p ∈ {p : B.I.GA × B.I.GA | (∀ v, dOp (uMat ((x0⁻¹ * p.1).1 v)) < Mv v) ∧
      (x0⁻¹ * p.1).2 ∈ K1 ∧ (∀ v, dOp (uMat ((y0⁻¹ * p.2).1 v)) < Mv v) ∧ (y0⁻¹ * p.2).2 ∈ K1},
      ‖phe B d (p.1⁻¹ * γ.1 * p.2)‖ ≤ t γ := by
    rintro γ ⟨x, y⟩ ⟨hax, hKx, hby, hKy⟩
    simp only at hax hKx hby hKy ⊢
    set a := x0⁻¹ * x with ha'
    set b := y0⁻¹ * y with hb'
    set w := x⁻¹ * γ.1 * y with hw
    have hz : x0⁻¹ * γ.1 * y0 = a * w * b⁻¹ := by rw [ha', hb', hw]; group
    have hphe : ‖phe B d w‖ = ‖ph B d w.1‖ * ‖B.e w.2‖ := norm_mul _ _
    rw [hphe]
    by_cases hew : B.e w.2 = 0
    · rw [hew, norm_zero, mul_zero]
      exact (ht0 γ).1
    have hzK : (x0⁻¹ * γ.1 * y0).2 ∈ B.I.Kset := by
      rw [hz]
      exact hKmul a.2 w.2 b.2 (hK1K hKx) (hsupp _ hew) (hK1K hKy)
    simp only [ht, if_pos hzK]

    have hmaj : ‖ph B d w.1‖ ≤ |∏ v, d v| *
        ∏ v, Real.exp (-(4 * (n : ℝ) ^ 2 * (⌊dOp (uMat (w.1 v))⌋₊ : ℝ))) := by
      refine (hphm w.1).trans ?_
      simp only [majPh]
      refine mul_le_mul (le_abs_self _) ?_ (Finset.prod_nonneg fun v _ => (Real.exp_pos _).le)
        (abs_nonneg _)
      refine Finset.prod_le_prod (fun v _ => (Real.exp_pos _).le) fun v _ => ?_
      exact decE_dOp_le_exp_floor (B.I.ε v) h hn (hb v) (w.1 v)
    have hshift : ∀ v, Real.exp (-(4 * (n : ℝ) ^ 2 * (⌊dOp (uMat (w.1 v))⌋₊ : ℝ))) ≤
        Real.exp (4 * (n : ℝ) ^ 2 * (1 + 2 * Mv v)) *
          Real.exp (-(2 * (2 * (n : ℝ) ^ 2) * (⌊D γ v⌋₊ : ℝ))) := by
      intro v
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      obtain ⟨hnn0, hinv, -⟩ := (hC v).2.1 (b.1 v) (b.1 v) hn
      have htri1 := ((hC v).2.1 (a.1 v * w.1 v) (b.1 v)⁻¹ hn).2.2.1
      have htri2 := ((hC v).2.1 (a.1 v) (w.1 v) hn).2.2.1
      have hzv : (x0⁻¹ * γ.1 * y0).1 v = a.1 v * w.1 v * (b.1 v)⁻¹ := by rw [hz]; rfl
      have hDz : D γ v ≤ dOp (uMat (a.1 v)) + dOp (uMat (w.1 v)) + dOp (uMat (b.1 v)) := by
        simp only [hD, hzv]
        linarith
      have hwnn : 0 ≤ dOp (uMat (w.1 v)) := ((hC v).2.1 (w.1 v) (w.1 v) hn).1
      have hfz : ((⌊D γ v⌋₊ : ℕ) : ℝ) ≤ D γ v := Nat.floor_le (hDnn γ v)
      have hfw : dOp (uMat (w.1 v)) < (⌊dOp (uMat (w.1 v))⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
      have hav := hax v
      have hbv := hby v
      have hkey : ((⌊D γ v⌋₊ : ℕ) : ℝ) ≤ (⌊dOp (uMat (w.1 v))⌋₊ : ℝ) + 1 + 2 * Mv v := by linarith
      have hn2 : (0 : ℝ) ≤ 4 * (n : ℝ) ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hkey hn2]
    have hprod : ∏ v, Real.exp (-(4 * (n : ℝ) ^ 2 * (⌊dOp (uMat (w.1 v))⌋₊ : ℝ))) ≤
        (∏ v, Real.exp (4 * (n : ℝ) ^ 2 * (1 + 2 * Mv v))) *
          ∏ v, Real.exp (-(2 * (2 * (n : ℝ) ^ 2) * (⌊D γ v⌋₊ : ℝ))) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod (fun v _ => (Real.exp_pos _).le) fun v _ => hshift v
    calc ‖ph B d w.1‖ * ‖B.e w.2‖
        ≤ (|∏ v, d v| * ((∏ v, Real.exp (4 * (n : ℝ) ^ 2 * (1 + 2 * Mv v))) *
            ∏ v, Real.exp (-(2 * (2 * (n : ℝ) ^ 2) * (⌊D γ v⌋₊ : ℝ))))) * (B.e 1).re := by
          refine mul_le_mul ?_ (he _) (norm_nonneg _) ?_
          · exact hmaj.trans (mul_le_mul_of_nonneg_left hprod (abs_nonneg _))
          · exact mul_nonneg (abs_nonneg _) (mul_nonneg
              (Finset.prod_nonneg fun v _ => (Real.exp_pos _).le)
              (Finset.prod_nonneg fun v _ => (Real.exp_pos _).le))
      _ = C' * ∏ v, Real.exp (-(2 * (2 * (n : ℝ) ^ 2) * (⌊D γ v⌋₊ : ℝ))) := by
          rw [hC']; ring
  have key := continuousOn_tsum (fun γ => (hcγ γ).continuousOn) hsum hbound
  exact key.continuousAt hNn

end GlobalTheory.Dec
