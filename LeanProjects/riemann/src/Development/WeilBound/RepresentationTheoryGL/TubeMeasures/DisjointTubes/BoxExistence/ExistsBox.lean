import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.LowSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMeasureFinitePartPreimage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousRealComponentHomUnitaryAdelic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfNormLtOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
import Formalism.LocalToGlobal.LatticeGeometry.DegFlLApply

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.Tam.B

theorem exists_box {ι : Type} [Fintype ι] {X : ι → Type} [∀ i, Group (X i)] [∀ i, TopologicalSpace (X i)]
    [∀ i, IsTopologicalGroup (X i)] [∀ i, LocallyCompactSpace (X i)] [∀ i, T2Space (X i)]
    [∀ i, MeasurableSpace (X i)] [∀ i, BorelSpace (X i)] [∀ i, SecondCountableTopology (X i)]
    (m : ∀ i, Measure (X i)) (hm : ∀ i, (m i).IsHaarMeasure) :
    ∃ B : Set (∀ i, X i), MeasurableSet B ∧ Measure.pi m B ≠ 0 ∧ Measure.pi m B ≠ ⊤ := by
  choose K hK hK1 using fun i => exists_compact_mem_nhds (1 : X i)
  haveI := hm
  refine ⟨Set.univ.pi K, MeasurableSet.univ_pi fun i => (hK i).measurableSet, ?_, ?_⟩
  · rw [Measure.pi_pi]
    exact Finset.prod_ne_zero_iff.2 fun i _ => (MeasureTheory.Measure.measure_pos_of_mem_nhds (μ := m i) (hK1 i)).ne'
  · rw [Measure.pi_pi]
    exact ENNReal.prod_ne_top fun i _ => (hK i).measure_lt_top.ne

theorem exp_le (f r : ℕ) (dd : ℝ) (hf : 1 ≤ f) (hr : 2 ≤ r) (hd : 1 ≤ dd) :
    Real.exp (-(3 * ((f : ℝ) * (r : ℝ) ^ 2 * (Real.log ((f : ℝ) * r + 3) + 1) + Real.log dd))) ≤
      (((r : ℝ) ^ (r ^ 2))⁻¹) ^ f * ((3 : ℝ) ^ (2 * f * r ^ 2))⁻¹ := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hpos : 0 < (((r : ℝ) ^ (r ^ 2))⁻¹) ^ f * ((3 : ℝ) ^ (2 * f * r ^ 2))⁻¹ := by positivity
  rw [← Real.exp_log hpos]
  apply Real.exp_le_exp.2
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_inv, Real.log_pow, Real.log_inv,
    Real.log_pow]
  push_cast
  have hf0 : (0 : ℝ) ≤ f := by positivity
  have hfr : (0 : ℝ) ≤ (f : ℝ) * (r : ℝ) ^ 2 := by positivity
  have h1 : Real.log r ≤ Real.log ((f : ℝ) * r + 3) := by
    apply Real.log_le_log hr0
    have : (1 : ℝ) ≤ f := by exact_mod_cast hf
    nlinarith
  have h3 : Real.log 3 ≤ Real.log ((f : ℝ) * r + 3) := by
    apply Real.log_le_log (by norm_num)
    have : (0 : ℝ) ≤ (f : ℝ) * r := by positivity
    linarith
  have hl3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hd0 : 0 ≤ Real.log dd := Real.log_nonneg hd
  have e1 : (f : ℝ) * ((r : ℝ) ^ 2 * Real.log r) ≤ (f : ℝ) * (r : ℝ) ^ 2 * Real.log ((f : ℝ) * r + 3) := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left h1 hfr
  have e2 : 2 * (f : ℝ) * (r : ℝ) ^ 2 * Real.log 3 ≤ 2 * ((f : ℝ) * (r : ℝ) ^ 2 * Real.log ((f : ℝ) * r + 3)) := by
    have := mul_le_mul_of_nonneg_left h3 hfr
    linarith
  nlinarith

end MainStatements.Tam.B

namespace MainStatements.Tam

theorem low : VolSt → StabSt → NumSt → LowSt := by
  intro hv hs hn
  refine ⟨3, by norm_num, ?_⟩
  intro D Tu Cl t0 hC i P μ 𝓕 hF
  letI : IsCMField D.host.E := D.host.isCMField_hostE
  have hrk : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hr : 2 ≤ D.R.r := Formalism.L2.Geo.two_le_r D
  have hV : (Wc D i).SigOK := D.sp.W_sig _
  have hsig := D.sp.W_sigval _ (Nat.le_add_left _ _) i.2
  haveI : IsTopologicalGroup (GA D (Wc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI := hF.1.1
  obtain ⟨⟨θ, hθ⟩, H1⟩ := hF.1.2
  obtain ⟨⟨A, hA⟩, H2⟩ := H1 θ hθ
  obtain ⟨⟨m, hm⟩, -⟩ := H2 A hA
  obtain ⟨rp, hrpc, hrp⟩ := GlobalTheory.CovTop.VolUp.exists_realPart_hom D (Wc D i) θ A hV hθ hA
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  obtain ⟨B, hBm, hB0, hBt⟩ := MainStatements.Tam.B.exists_box m (fun ρ => (hm ρ).1)
  have hKo : IsOpen {h : GA D (Wc D i) | finE (Wc D i) h ∈ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i P} :=
    GlobalTheory.ParahoricCompact.isOpen_comap_lev _ _ _
  have heq := GlobalTheory.CovTop.VolPush.meas_translate_eq D (Wc D i) θ A m rp _ μ hV hθ hA hm hrpc hrp hKo hF.1 1 (one_mem _) B hBm
  have hsub : {h | finE (Wc D i) (1⁻¹ * h) ∈ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i P ∧ rp h ∈ B} ⊆
      {h | h ∈ Stab (Wc D i) ∧ rp h ∈ B} := by
    intro h hh
    refine ⟨hs.2 D Tu Cl t0 hC i P h ?_, hh.2⟩
    simpa using hh.1
  have hle : Measure.pi m B ≤ μ {h | h ∈ Stab (Wc D i) ∧ rp h ∈ B} := heq ▸ measure_mono hsub
  have hvol := hv D (Wc D i) _ _ hV hsig μ 𝓕 hF.2 θ A m rp hθ hA hm hrpc hrp B hBm
  set X : ℝ := ReciprocityTheory.ChartRestriction.DS.volU (Wc D i).rank ^ D.R.f * Formalism.MainNotions.StandardLattice.massI D (Wc D i).rank with hX
  have hXle : ENNReal.ofReal X ≤ μ 𝓕 := by
    have h1 : ENNReal.ofReal X * Measure.pi m B ≤ μ 𝓕 * Measure.pi m B := by
      rw [hvol, mul_comm]
      gcongr
    first
      | exact (ENNReal.mul_le_mul_right hB0 hBt).1 h1
      | exact (ENNReal.mul_le_mul_iff_left hB0 hBt).1 h1
      | exact (ENNReal.mul_le_mul_iff_right hB0 hBt).1 h1
  have hfin : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [show Module.finrank ℚ D.host.E = 4 * D.R.ord from D.host.finrank_cmField]
    unfold Ranks.f Ranks.n; ring
  have hf : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega
  have hmass : ((3 : ℝ) ^ (2 * D.R.f * D.R.r ^ 2))⁻¹ ≤ Formalism.MainNotions.StandardLattice.massI D D.R.r := by
    have := GlobalTheory.StdMassLower.main D.host.E (fun _ => rfl) D.R.r
    rw [hfin] at this
    exact this
  obtain ⟨hn1, -⟩ := hn D.R.r hr
  have hlow : (((D.R.r : ℝ) ^ (D.R.r ^ 2))⁻¹) ^ D.R.f * ((3 : ℝ) ^ (2 * D.R.f * D.R.r ^ 2))⁻¹ ≤ X := by
    rw [hX, hrk]
    have hr0 : (0 : ℝ) < ((D.R.r : ℝ) ^ (D.R.r ^ 2))⁻¹ := by
      have : (0 : ℝ) < D.R.r := by exact_mod_cast (by omega : 0 < D.R.r)
      positivity
    have hv0 : 0 ≤ ReciprocityTheory.ChartRestriction.DS.volU D.R.r := hr0.le.trans hn1
    exact mul_le_mul (pow_le_pow_left₀ hr0.le hn1 _) hmass (by positivity) (pow_nonneg hv0 _)
  have hd : (1 : ℝ) ≤ |(discr D.host.E : ℝ)| := by
    exact_mod_cast Int.one_le_abs (NumberField.discr_ne_zero D.host.E)
  have hexp := MainStatements.Tam.B.exp_le D.R.f D.R.r _ hf hr hd
  calc ENNReal.ofReal (Real.exp (-(3 * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * (Real.log ((D.R.f : ℝ) * D.R.r + 3) + 1) +
        Real.log |(discr D.host.E : ℝ)|))))
      ≤ ENNReal.ofReal X := ENNReal.ofReal_le_ofReal (hexp.trans hlow)
    _ ≤ μ 𝓕 := hXle

end MainStatements.Tam

end
