import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.LowSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureTranslateLevelRealBoxLeIndexMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePartMemFullLevelOfKeepsSelfDualLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousRealComponentHomUnitaryAdelicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelIndexBoundOfPrintsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMassUpperBound
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
import Formalism.LocalToGlobal.LatticeGeometry.DegFlLApply

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.Tam.A

theorem exists_box {ι : Type} [Fintype ι] {X : ι → Type} [∀ i, TopologicalSpace (X i)] [∀ i, MeasurableSpace (X i)]
    [∀ i, BorelSpace (X i)] [∀ i, Group (X i)] [∀ i, IsTopologicalGroup (X i)] [∀ i, LocallyCompactSpace (X i)]
    [∀ i, T2Space (X i)] [∀ i, SecondCountableTopology (X i)] (m : ∀ i, Measure (X i)) [∀ i, (m i).IsHaarMeasure] :
    ∃ B : Set (∀ i, X i), MeasurableSet B ∧ Measure.pi m B ≠ 0 ∧ Measure.pi m B ≠ ⊤ := by
  choose K hK hKn using fun i => exists_compact_mem_nhds (1 : X i)
  refine ⟨Set.univ.pi K, MeasurableSet.univ_pi fun i => (hK i).measurableSet, ?_, ?_⟩
  · rw [Measure.pi_pi]
    exact Finset.prod_ne_zero_iff.2 fun i _ => (Measure.measure_pos_of_mem_nhds (μ := m i) (hKn i)).ne'
  · rw [Measure.pi_pi]
    exact ENNReal.prod_ne_top fun i _ => (hK i).measure_lt_top.ne

theorem le_exp_three : (13 : ℝ) ≤ Real.exp 3 := by
  have e1 := Real.exp_one_gt_d9
  have h : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  calc (13 : ℝ) ≤ 2.7 ^ 3 := by norm_num
    _ ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3

theorem bound (f r d : ℕ) (L n v M rd : ℝ) (hd : (d : ℝ) = 2 * f) (hL : 1 ≤ L)
    (hfr : (f : ℝ) * (r : ℝ) ^ 2 ≤ Real.exp L) (hrd1 : 1 ≤ rd) (hrdL : Real.log rd ≤ 2 * L) (hn1 : 1 ≤ n)
    (hn : Real.log n ≤ 60 * (f * (r : ℝ) ^ 2 * L)) (hv0 : 0 ≤ v) (hv : v ≤ 13 ^ (r ^ 2))
    (hM : M ≤ (3 * ((d : ℝ) ^ 2 * (r : ℝ) ^ 4 * rd ^ 2)) ^ (3 * d * r ^ 2)) :
    n * (v ^ f * M) ≤ Real.exp (117 * (f * (r : ℝ) ^ 2 * L)) := by
  have ha : 0 ≤ (f : ℝ) * (r : ℝ) ^ 2 := by positivity
  have hn' : n ≤ Real.exp (60 * (f * (r : ℝ) ^ 2 * L)) := by
    rw [← Real.exp_log (by linarith : (0 : ℝ) < n)]; exact Real.exp_le_exp.2 hn
  have h13 := le_exp_three
  have hv' : v ^ f ≤ Real.exp (3 * (f * (r : ℝ) ^ 2 * L)) := by
    calc v ^ f ≤ ((13 : ℝ) ^ (r ^ 2)) ^ f := pow_le_pow_left₀ hv0 hv f
      _ = (13 : ℝ) ^ (r ^ 2 * f) := by rw [pow_mul]
      _ ≤ Real.exp 3 ^ (r ^ 2 * f) := pow_le_pow_left₀ (by norm_num) h13 _
      _ = Real.exp (((r ^ 2 * f : ℕ) : ℝ) * 3) := by rw [Real.exp_nat_mul]
      _ ≤ Real.exp (3 * (f * (r : ℝ) ^ 2 * L)) := by
        refine Real.exp_le_exp.2 ?_
        push_cast
        nlinarith
  have hrd : rd ≤ Real.exp (2 * L) := (Real.log_le_iff_le_exp (by linarith)).1 hrdL
  have hX : 3 * ((d : ℝ) ^ 2 * (r : ℝ) ^ 4 * rd ^ 2) ≤ Real.exp (9 * L) := by
    have e1 : ((f : ℝ) * (r : ℝ) ^ 2) ^ 2 ≤ Real.exp L ^ 2 := pow_le_pow_left₀ ha hfr 2
    have e2 : rd ^ 2 ≤ Real.exp (2 * L) ^ 2 := pow_le_pow_left₀ (by linarith) hrd 2
    have e3 : Real.exp (9 * L) = Real.exp 3 * Real.exp L ^ 2 * Real.exp (2 * L) ^ 2 * Real.exp (3 * L - 3) := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; push_cast; ring
    have e4 : 1 ≤ Real.exp (3 * L - 3) := Real.one_le_exp (by linarith)
    have e5 : 3 * ((d : ℝ) ^ 2 * (r : ℝ) ^ 4 * rd ^ 2) = 12 * (((f : ℝ) * (r : ℝ) ^ 2) ^ 2 * rd ^ 2) := by rw [hd]; ring
    rw [e3, e5]
    have p1 : 0 ≤ ((f : ℝ) * (r : ℝ) ^ 2) ^ 2 * rd ^ 2 := by positivity
    have p2 : ((f : ℝ) * (r : ℝ) ^ 2) ^ 2 * rd ^ 2 ≤ Real.exp L ^ 2 * Real.exp (2 * L) ^ 2 :=
      mul_le_mul e1 e2 (by positivity) (by positivity)
    have p3 : 0 ≤ Real.exp L ^ 2 * Real.exp (2 * L) ^ 2 := by positivity
    calc 12 * (((f : ℝ) * (r : ℝ) ^ 2) ^ 2 * rd ^ 2) ≤ Real.exp 3 * (Real.exp L ^ 2 * Real.exp (2 * L) ^ 2) :=
          mul_le_mul (by linarith) p2 p1 (Real.exp_pos _).le
      _ = Real.exp 3 * Real.exp L ^ 2 * Real.exp (2 * L) ^ 2 * 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left e4 (by positivity)
  have hM' : M ≤ Real.exp (54 * (f * (r : ℝ) ^ 2 * L)) := by
    refine hM.trans ?_
    calc (3 * ((d : ℝ) ^ 2 * (r : ℝ) ^ 4 * rd ^ 2)) ^ (3 * d * r ^ 2) ≤ Real.exp (9 * L) ^ (3 * d * r ^ 2) :=
          pow_le_pow_left₀ (by positivity) hX _
      _ = Real.exp (((3 * d * r ^ 2 : ℕ) : ℝ) * (9 * L)) := by rw [Real.exp_nat_mul]
      _ = _ := by congr 1; push_cast; rw [hd]; ring
  rcases le_or_gt M 0 with hM0 | hM0
  · have : n * (v ^ f * M) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hv0 _) hM0)
    exact this.trans (Real.exp_pos _).le
  · calc n * (v ^ f * M) ≤ Real.exp (60 * (f * (r : ℝ) ^ 2 * L)) *
          (Real.exp (3 * (f * (r : ℝ) ^ 2 * L)) * Real.exp (54 * (f * (r : ℝ) ^ 2 * L))) :=
          mul_le_mul hn' (mul_le_mul hv' hM' hM0.le (Real.exp_pos _).le) (by positivity) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

open GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes in

theorem up_core (hV : VolSt) (hS : StabSt) (hN : NumSt) (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0)
    (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i)))
    (hF : IsMeasFD (Wc D i) (levW C i P) μ 𝓕) (L : ℝ) (hL : Sizes D L) (hIB : IndexBound C i P) :
    Real.log (μ 𝓕).toReal ≤ D.R.f * (D.R.r : ℝ) ^ 2 * Real.log ((D.R.r : ℝ) + 3) + (38 + 81) * (D.R.f * (D.R.r : ℝ) ^ 2 * L) := by
  obtain ⟨hn, hnl⟩ := hIB
  have hrk : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hr : 2 ≤ D.R.r := Formalism.L2.Geo.two_le_r D
  have hSig := D.sp.W_sig ((i : ℕ) + 1)
  haveI := hF.1.1
  obtain ⟨⟨θ, hθ⟩, H1⟩ := hF.1.2
  obtain ⟨⟨A, hA⟩, H2⟩ := H1 θ hθ
  obtain ⟨⟨m, hm⟩, -⟩ := H2 A hA
  obtain ⟨rp, hrpc, hrp⟩ := GlobalTheory.T.exists_continuous_realComponentHom_unitaryAdelic D (Wc D i) θ A (D.sp.W_sig _) hθ hA
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  haveI : ∀ ρ, (m ρ).IsHaarMeasure := fun ρ => (hm ρ).1
  obtain ⟨B, hBm, hB0, hBt⟩ := MainStatements.Tam.A.exists_box m
  have hvol := hV D (Wc D i) _ _ (D.sp.W_sig _) (D.sp.W_sigval _ (Nat.le_add_left _ _) i.2) μ 𝓕 hF.2 θ A m rp hθ hA hm
    hrpc hrp B hBm
  set K₀ := levW C i (Formalism.L2.DIV.LevelP.full _ _ _) with hK₀
  set n := (levW C i P).relIndex K₀ with hndef
  have hsub : {h | h ∈ Stab (Wc D i) ∧ rp h ∈ B} ⊆ {h | finE (Wc D i) (1⁻¹ * h) ∈ K₀ ∧ rp h ∈ B} := by
    rintro h ⟨hh, hb⟩
    refine ⟨?_, hb⟩
    rw [inv_one, one_mul]
    have hk : h ∈ KM (Wc D i) 1 := (hS.1 D (Wc D i)).1 ▸ hh
    exact GlobalTheory.T.finitePart_mem_fullLevel_of_keeps_selfDualLattice D (Wc D i) (C.βW i) (C.ΛW i) _ (hC.βW i) hrk.le rfl h hk
  have h44 := GlobalTheory.T.measure_translateLevel_realBox_le_index_mul D (Wc D i) θ A m rp (levW C i P) K₀ μ (D.sp.W_sig _) hθ hA hm hrpc hrp
    (fun k hk => ⟨hk.1, Subgroup.mem_top _⟩) hn (GlobalTheory.ParahoricCompact.isOpen_comap_lev _ _ _) hF.1 1 (GfC _).one_mem B hBm
  set c := ReciprocityTheory.ChartRestriction.DS.volU (Wc D i).rank ^ D.R.f * Formalism.MainNotions.StandardLattice.massI D (Wc D i).rank with hc
  have hkey : μ 𝓕 * Measure.pi m B ≤ ((n : ℝ≥0∞) * ENNReal.ofReal c) * Measure.pi m B := by
    rw [hvol]
    calc μ {h | h ∈ Stab (Wc D i) ∧ rp h ∈ B} * ENNReal.ofReal c ≤ ((n : ℝ≥0∞) * Measure.pi m B) * ENNReal.ofReal c := by
          gcongr; exact (measure_mono hsub).trans h44
      _ = _ := by ring
  have hμ := (ENNReal.mul_le_mul_iff_left hB0 hBt).1 hkey

  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have hfin : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [show Module.finrank ℚ D.host.E = 4 * D.R.ord from D.host.finrank_cmField]
    unfold Ranks.f Ranks.n; ring
  have hu : Formalism.MainNotions.StandardLattice.massI D D.R.r ≤ (3 * ((Module.finrank ℚ D.host.E : ℝ) ^ 2 * (D.R.r : ℝ) ^ 4 * D.host.rdE ^ 2)) ^
      (3 * Module.finrank ℚ D.host.E * D.R.r ^ 2) := GlobalTheory.mass_stdLat_le D.host.E (fun _ => rfl) D.R.r
  obtain ⟨hN1, hN2⟩ := hN D.R.r hr
  have hnV : D.R.r ≤ D.R.nV := Nat.le_add_right _ _
  obtain ⟨h1, -, h3, h4⟩ := hL
  have hfr : (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 ≤ Real.exp L := by
    refine le_trans ?_ h1
    have hnR : (D.R.r : ℝ) ≤ D.R.nV := by exact_mod_cast hnV
    rw [sq, ← mul_assoc]; gcongr
  have hL1 : 1 ≤ L := by
    have hf : 2 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega
    have hfR : (2 : ℝ) ≤ D.R.f := by exact_mod_cast hf
    have hrR : (2 : ℝ) ≤ D.R.r := by exact_mod_cast hr
    have : Real.exp 1 ≤ Real.exp L := by
      have := Real.exp_one_lt_d9
      nlinarith
    exact Real.exp_le_exp.1 this
  have hd1 : (1 : ℝ) ≤ |(discr D.host.E : ℝ)| := by
    have := Int.one_le_abs (discr_ne_zero D.host.E)
    exact_mod_cast this
  have hrd1 : 1 ≤ D.host.rdE := Real.one_le_rpow hd1 (by positivity)
  have hrdL : Real.log D.host.rdE ≤ 2 * L := by linarith [abs_nonneg (dlogL D 1)]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
  have hgL : Real.log (n : ℝ) ≤ 60 * (D.R.f * (D.R.r : ℝ) ^ 2 * L) := by
    have ha : 0 ≤ 2 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 := by positivity
    calc Real.log (n : ℝ) ≤ 2 * D.R.f * (D.R.r : ℝ) ^ 2 * Real.log ((D.host.g 0 : ℝ) * D.host.g 1) := hnl
      _ ≤ 2 * D.R.f * (D.R.r : ℝ) ^ 2 * (30 * L) := mul_le_mul_of_nonneg_left h3 ha
      _ = _ := by ring
  have hv0 : 0 ≤ ReciprocityTheory.ChartRestriction.DS.volU D.R.r := le_trans (by positivity) hN1
  have hb := MainStatements.Tam.A.bound D.R.f D.R.r (Module.finrank ℚ D.host.E) L n _ _ D.host.rdE (by rw [hfin]; push_cast; ring) hL1 hfr
    hrd1 hrdL hn1 hgL hv0 hN2 hu
  have hc' : (n : ℝ) * c ≤ Real.exp (117 * (D.R.f * (D.R.r : ℝ) ^ 2 * L)) := by
    rw [hc, hrk]; exact hb
  have hle : (μ 𝓕).toReal ≤ Real.exp (117 * (D.R.f * (D.R.r : ℝ) ^ 2 * L)) := by
    refine ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le (hμ.trans ?_)
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hc'
  have h0 : 0 ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * Real.log ((D.R.r : ℝ) + 3) :=
    mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
  have h5 : Real.log (μ 𝓕).toReal ≤ 117 * (D.R.f * (D.R.r : ℝ) ^ 2 * L) := by
    rcases (ENNReal.toReal_nonneg (a := μ 𝓕)).eq_or_lt with h | h
    · rw [← h, Real.log_zero]; positivity
    · exact (Real.log_le_iff_le_exp h).2 hle
  have h6 : 0 ≤ D.R.f * (D.R.r : ℝ) ^ 2 * L := by positivity
  linarith

end MainStatements.Tam.A

namespace MainStatements.Tam

theorem up : VolSt → StabSt → NumSt → UpSt := fun hV hS hN hP D Tu C t0 hC i P μ 𝓕 hF L hL =>
  MainStatements.Tam.A.up_core hV hS hN D Tu C t0 hC i P μ 𝓕 hF L hL (GlobalTheory.T.level_index_bound_of_classicalTheorems hP D Tu C t0 hC i P)

end MainStatements.Tam

end
