import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreSizeAndRangeBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentMetricFromSectionStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open AlgebraicGeometry CategoryTheory MeasureTheory Set GlobalTheory.ShFam GlobalTheory.ChernReg GlobalTheory.CxPts GlobalTheory.TrueGeo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ProjVar Formalism.L2.Pj Formalism.L2.Geo GlobalTheory
open ReciprocityTheory.AnForm.M

open Filter Topology ReciprocityTheory.AnForm

namespace GlobalTheory.FundWeightExt

theorem sumNonnegOn_of_pshOff {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ : LocPot X) (ph : X → ℝ) (Z : Set X) (hZ : IsClosed Z) (hΘ : IsPotential A Θ)
    (hph : A.SmoothOn Zᶜ ph) (hpsh : GlobalTheory.Mean4O.PshOff A Z (Θ + LocPot.ofFun ph)) :
    GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.SumNonnegOn A Θ (fun z => 2 * ph z) Zᶜ := by
  intro x j z hz w
  have hzt : z ∈ (A.chart j).target := hz.1
  have hyx : (A.chart j).symm z ∈ Θ.U x := hz.2.1
  have hyZ : (A.chart j).symm z ∉ Z := hz.2.2
  obtain ⟨Wn, hWo, hyW, G, hG, hGe⟩ :=
    hΘ.2 x ((A.chart j).symm z) ((A.chart j).symm z) ⟨hyx, Θ.mem_U _⟩
  have hOo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹'
      (Wn ∩ Θ.U x ∩ Θ.U ((A.chart j).symm z) ∩ Zᶜ)) :=
    (A.chart j).isOpen_inter_preimage_symm
      (((hWo.inter (Θ.isOpen_U x)).inter (Θ.isOpen_U _)).inter hZ.isOpen_compl)
  have hzO : z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹'
      (Wn ∩ Θ.U x ∩ Θ.U ((A.chart j).symm z) ∩ Zᶜ) :=
    ⟨hzt, ⟨⟨⟨hyW, hyx⟩, Θ.mem_U _⟩, hyZ⟩⟩
  have hO : ∀ᶠ z' in 𝓝 z, z' ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹'
      (Wn ∩ Θ.U x ∩ Θ.U ((A.chart j).symm z) ∩ Zᶜ) := hOo.mem_nhds hzO

  have h1 : ContDiffAt ℝ 2 (fun z' => Θ.φ ((A.chart j).symm z) ((A.chart j).symm z')) z := by
    have hU : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Θ.U ((A.chart j).symm z)) :=
      (A.chart j).isOpen_inter_preimage_symm (Θ.isOpen_U _)
    exact ((hΘ.1 ((A.chart j).symm z) j).contDiffAt (hU.mem_nhds ⟨hzt, Θ.mem_U _⟩)).of_le (by norm_cast)
  have h2 : ContDiffAt ℝ 2 (fun z' => ph ((A.chart j).symm z')) z := by
    have hU : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Zᶜ) :=
      (A.chart j).isOpen_inter_preimage_symm hZ.isOpen_compl
    exact ((hph j).contDiffAt (hU.mem_nhds ⟨hzt, hyZ⟩)).of_le (by norm_cast)
  have hGa : AnalyticAt ℂ (G ∘ (A.chart j).symm) z := hG j z ⟨hzt, hyW⟩
  have h3 : ContDiffAt ℝ 2 (fun z' => (G ((A.chart j).symm z')).re) z :=
    Complex.reCLM.contDiff.contDiffAt.comp z (hGa.restrictScalars (𝕜 := ℝ)).contDiffAt
  have h4 : levi (fun z' => ((G ∘ (A.chart j).symm) z').re) z w = 0 := levi_re_analytic hGa w
  have hg0 : 0 ≤ levi (fun z' => Θ.φ ((A.chart j).symm z) ((A.chart j).symm z') +
      ph ((A.chart j).symm z')) z w := hpsh j z hzt hyZ w
  have hev : (fun z' => 2 * Θ.φ x ((A.chart j).symm z') + 2 * ph ((A.chart j).symm z')) =ᶠ[𝓝 z]
      fun z' => (Θ.φ ((A.chart j).symm z) ((A.chart j).symm z') + ph ((A.chart j).symm z')) +
        1 * ((Θ.φ ((A.chart j).symm z) ((A.chart j).symm z') + ph ((A.chart j).symm z')) +
          2 * (G ((A.chart j).symm z')).re) := by
    filter_upwards [hO] with z' hz'
    have := hGe ((A.chart j).symm z') ⟨⟨hz'.2.1.1.1, hz'.2.1.1.2⟩, hz'.2.1.2⟩
    linarith
  show 0 ≤ levi (fun z' => 2 * Θ.φ x ((A.chart j).symm z') + 2 * ph ((A.chart j).symm z')) z w
  rw [levi_congr hev, levi_add_smul 1 (h1.add h2) ((h1.add h2).add (contDiffAt_const.mul h3)),
    levi_add_smul 2 (h1.add h2) h3]
  have h4' : levi (fun z' => (G ((A.chart j).symm z')).re) z w = 0 := h4
  rw [h4']
  linarith

theorem exists_quasiPsh_ext : Hypotheses2 → HypothesesH → OnObj fun D O _ T _ R => ∀ c a τ (i : Fin O.N), (i : ℕ) + 1 < O.N → ∃ v : (T.M c).X a → EReal, GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.IsQuasiPsh ((T.M c).A a) ((T.F c).th (fund τ i) a) v ∧ ∀ z, z ∉ (T.M c).Z a → v z = ((2 * (T.F c).ph (fund τ i) a z : ℝ) : EReal) := by
  intro h2 hH D O hC hf A T H hR c a τ i hi
  obtain ⟨hSize, -⟩ := GlobalTheory.T.fibre_size_and_range_bound h2 hH D O hC hf A T H hR c
  obtain ⟨-, L, s, hB, m, W, hW⟩ := GlobalTheory.T.component_metric_from_section D O hC A T H hR c a
  obtain ⟨hLpot, hsec, hle, hZ, -, hr⟩ := hB
  obtain ⟨-, hsm, hpsh, C, hCb⟩ := hSize
  have hopn : GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.opn s = ((T.M c).Z a)ᶜ := by
    ext y; rw [hZ]; simp [GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.opn, ReciprocityTheory.AnForm.P.bdry]
  have hbd : GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.IsBoundary ((T.M c).A a) L s W := by
    refine ⟨hLpot, hsec, hW, fun y => ?_⟩
    have := hle y
    unfold logNormSec at this
    exact (Real.log_nonpos_iff (by positivity)).1 this
  have hP := hpsh (fund τ i) (by
    intro τ' a' b' hab
    unfold fund
    by_cases hb : τ' = τ ∧ b' ≤ i
    · rw [if_pos hb, if_pos ⟨hb.1, le_trans hab hb.2⟩]
    · rw [if_neg hb]; split_ifs <;> norm_num) a
  have hsmooth : ((T.M c).A a).SmoothOn (GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.opn s)
      (fun z => 2 * (T.F c).ph (fund τ i) a z) := by
    rw [hopn]; intro j
    exact contDiffOn_const.mul (hsm (fund τ i) a j)
  have hsum := GlobalTheory.FundWeightExt.sumNonnegOn_of_pshOff ((T.M c).A a) ((T.F c).th (fund τ i) a)
    ((T.F c).ph (fund τ i) a) ((T.M c).Z a) ((T.M c).bd a).1 (T.th_pot c _ a) (hsm (fund τ i) a)
    hP
  rw [← hopn] at hsum
  have hgrow : ∀ y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.opn s, 2 * (T.F c).ph (fund τ i) a y ≤
      (2 * (C * ‖fund τ i‖)) * Real.log (GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.rad L s y) := by
    intro y hy
    have hy' : y ∉ (T.M c).Z a := by rw [hopn] at hy; exact hy
    have h1 := (hCb (fund τ i) a y hy').1
    rw [hr y hy'] at h1
    have h2 : (T.F c).ph (fund τ i) a y ≤ C * ‖fund τ i‖ * Real.log (GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.rad L s y) :=
      (le_abs_self _).trans h1
    linarith
  obtain ⟨-, hEq, hQ⟩ := GlobalTheory.T.extension_statement _ ((T.M c).X a) ((T.M c).A a) L s m W hbd
    ((T.F c).th (fund τ i) a) (fun z => 2 * (T.F c).ph (fund τ i) a z) (2 * (C * ‖fund τ i‖))
    (T.th_pot c _ a) hsmooth hsum hgrow
  refine ⟨_, hQ, fun z hz => ?_⟩
  exact hEq z (by rw [hopn]; exact hz)

end GlobalTheory.FundWeightExt
