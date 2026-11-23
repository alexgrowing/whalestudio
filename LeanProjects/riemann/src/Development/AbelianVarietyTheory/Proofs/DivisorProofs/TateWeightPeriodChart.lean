import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubicalMetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareIsoIsometryCubicalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicLogOnConvex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetricRatioPeriodicConstantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodChartLatticeInvarianceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodChartContinuousFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLineBundlePeriodFramingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTateMetricPeriodFormulaStatement
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff

namespace GlobalTheory.TateChart
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (IsPeriodMap IsFactor IsBundleIso mulPullFactor transl mulN)

theorem isMetric_of_doubling : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.IsPeriodMap B τ → Convex ℝ B → ∀ (j : Fl g → Pt E g → ℂ) (m : Pt E g → ℝ) (φ : Pt E g → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.IsFactor B τ (stdLat g) j → (∃ ι, GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.IsBundleIso B τ (stdLat g) (GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.mulPullFactor (-1) j) j ι) → InducesPolarisation B τ (stdLat g) j → GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.IsBundleIso B τ (stdLat g) (GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.mulPullFactor 2 j) (fun l P => j l P ^ 4) φ → (∀ P ∈ cov B g, 0 < m P) → (∀ l ∈ stdLat g, ∀ P ∈ cov B g, m (GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.transl τ l P) * ‖j l P‖ ^ 2 = m P) → (∀ b ∈ B, Continuous fun z => m (b, z)) → (∀ P ∈ cov B g, m (GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.mulN 2 P) = m P ^ 4 * ‖φ P‖ ^ 2) → IsMetric B τ (stdLat g) j m ∧ ChernIsFlat B τ m := by
  intro g E _ _ _ B τ hτ hconv j m φ hfac hι hpol hφ hpos hper hcont heq
  have hmem : ∀ {Q : Pt E g}, Q ∈ cov B g ↔ Q.1 ∈ B := fun {Q} =>
    ⟨fun hQ => hQ.1, fun hQ => ⟨hQ, Set.mem_univ _⟩⟩
  have φ0 : DifferentiableOn ℂ (fun b => φ (b, 0)) B :=
    hφ.1.comp (differentiableOn_id.prodMk (differentiableOn_const 0)) (fun b hb => hmem.2 hb)
  have φ0ne : ∀ b ∈ B, φ (b, 0) ≠ 0 := fun b hb => hφ.2.1 _ (hmem.2 hb)
  obtain ⟨large₂, hLd, hLe⟩ := GlobalTheory.ConvexHolLog.exists_differentiableOn_log hconv hτ.1 _ φ0 φ0ne
  set r : E → ℂ := fun b => Complex.exp (large₂ b / 3) with hr
  have hrig : GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.IsRigidification B r :=
    ⟨by
      have h3 : DifferentiableOn ℂ (fun b => large₂ b / 3) B := by
        simpa only [div_eq_mul_inv] using hLd.mul_const ((3 : ℂ)⁻¹)
      exact h3.cexp, fun b _ => Complex.exp_ne_zero _⟩
  have h24 : (2 : ℤ).natAbs ^ 2 = 4 := by norm_num
  have hsq : GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.IsSquareIso B τ j r 2 φ := by
    refine ⟨by rw [h24]; exact hφ, fun b hb => ?_⟩
    rw [h24]
    change φ (b, 0) * r b = r b ^ 4
    rw [hLe b hb, hr]
    simp only
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  obtain ⟨h0, hcub⟩ := GlobalTheory.T.exists_cubical_metric hτ j r hfac hι hrig hpol
  have hiso := GlobalTheory.T.square_iso_isometry_cubical hτ j r hfac hι hrig hpol 2 h0 φ hcub hsq
  rw [h24] at hiso
  have hE : Set.EqOn m h0 (cov B g) :=
    GlobalTheory.T.metric_ratio_periodic_constant hτ j m h0 φ hpos hcub.1.2.1 hper hcub.1.2.2 hcont
      (fun b hb => hcub.1.1.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
        (fun z => hmem.2 hb))
      heq (fun P hP => (hiso P hP).symm)
  have hopen : IsOpen (cov B g) := hτ.1.prod isOpen_univ
  refine ⟨⟨hcub.1.1.congr hE, hpos, hper⟩, fun P hP v w => ?_⟩
  have hev : (fun Q => Real.log (m Q)) =ᶠ[𝓝 P] fun Q => Real.log (h0 Q) := by
    filter_upwards [hopen.mem_nhds hP] with Q hQ
    rw [hE hQ]
  have hd : ∀ x : Pt E g, (fun Q => fderiv ℝ (fun Q => Real.log (m Q)) Q x) =ᶠ[𝓝 P]
      fun Q => fderiv ℝ (fun Q => Real.log (h0 Q)) Q x := fun x => by
    filter_upwards [hev.eventuallyEq_nhds] with Q hQ
    rw [hQ.fderiv_eq]
  have := hcub.2.1 P hP v w
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.ddc at this ⊢
  rw [(hd _).fderiv_eq, (hd _).fderiv_eq]
  exact this

theorem isMetric_chernIsFlat_of_isTate : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k), IsRegSurf p → ∀ (P : PPAS S), IsArithVar (P.A.hom ≫ p) (P.g + 1) → ∀ (h : VMetric p (omega P.A) P.g) (L : HermLB (P.A.hom ≫ p)), IsTheta P L.B → ∀ (w : LB.Iso (L.pull (dbl P) (dbl_comp P p)).B (L.pow 4).B), w.IsGen → ∀ u : ∀ σ : k →+* ℂ, CxPts (P.A.hom ≫ p) σ → ℝ, (∀ σ, Continuous (u σ)) → IsTate (dbl P) (dbl_comp P p) L w u → ∀ (σ : k →+* ℂ) (c : AlgChart p σ 1) (τ : V 1 → Matrix (Fin P.g) (Fin P.g) ℂ) (ex : Pt (V 1) P.g → CxPts (P.A.hom ≫ p) σ) (j : Fl P.g → Pt (V 1) P.g → ℂ) (m : Pt (V 1) P.g → ℝ), IsPeriodChart h c τ ex → IsFramed L c.e.target τ ex j m → IsDatum c.e.target τ (stdLat P.g) j m → InducesPolarisation c.e.target τ (stdLat P.g) j → IsMetric c.e.target τ (stdLat P.g) j (fun Q => m Q * Real.exp (-u σ (ex Q))) ∧ ChernIsFlat c.e.target τ (fun Q => m Q * Real.exp (-u σ (ex Q))) := by
  intro k _ S p hS P hA h L hθ w hw u hu hT σ c τ ex j m hPC hF hD hpol
  have hmem : ∀ {B : Set (V 1)} {Q : Pt (V 1) P.g}, Q ∈ cov B P.g ↔ Q.1 ∈ B := fun {B Q} =>
    ⟨fun hQ => hQ.1, fun hQ => ⟨hQ, Set.mem_univ _⟩⟩
  have covMono : ∀ {B B' : Set (V 1)}, B ⊆ B' → cov B P.g ⊆ cov B' P.g := fun hBB Q hQ =>
    hmem.2 (hBB (hmem.1 hQ))
  obtain ⟨hτ, -, hfac, hcd, hpos, hmper⟩ := id hD
  set m' : Pt (V 1) P.g → ℝ := fun Q => m Q * Real.exp (-u σ (ex Q)) with hm'
  have hper : ∀ l ∈ stdLat P.g, ∀ Q ∈ cov c.e.target P.g, m' (transl τ l Q) * ‖j l Q‖ ^ 2 = m' Q := by
    intro l hl Q hQ
    simp only [hm', GlobalTheory.T.period_chart_lattice_invariance k S p P h σ c τ ex hPC l hl Q hQ]
    rw [← hmper l hl Q hQ]
    ring
  have hloc : ∀ v ∈ c.e.target, ∃ B' ⊆ c.e.target, IsOpen B' ∧ v ∈ B' ∧
      IsMetric B' τ (stdLat P.g) j m' ∧ ChernIsFlat B' τ m' := by
    intro v hv
    obtain ⟨B4, hB4, hB4o, hv4, ι, hι⟩ := GlobalTheory.T.theta_line_bundle_period_framing k S p hS P hA h L hθ σ c τ ex j m hPC hF hD v hv
    obtain ⟨B5, hB5, hB5o, hv5, φ, hφ, hφeq⟩ := GlobalTheory.T.theta_tate_metric_period_formula k S p hS P hA h L hθ w hw u hT σ c τ ex j m hPC hF hD v hv
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hB4o.inter hB5o) v ⟨hv4, hv5⟩
    set B := Metric.ball v ε with hBdef
    have h4 : B ⊆ B4 := fun x hx => (hball hx).1
    have h5 : B ⊆ B5 := fun x hx => (hball hx).2
    have hT' : B ⊆ c.e.target := h4.trans hB4
    have isoMono : ∀ {B₁ B₂ : Set (V 1)} {j₁ j₂ : Fl P.g → Pt (V 1) P.g → ℂ} {f : Pt (V 1) P.g → ℂ},
        B₁ ⊆ B₂ → IsBundleIso B₂ τ (stdLat P.g) j₁ j₂ f → IsBundleIso B₁ τ (stdLat P.g) j₁ j₂ f :=
      fun hs hf => ⟨hf.1.mono (covMono hs), fun Q hQ => hf.2.1 Q (covMono hs hQ),
        fun l hl Q hQ => hf.2.2 l hl Q (covMono hs hQ)⟩
    have hres := isMetric_of_doubling (B := B) (τ := τ) ⟨Metric.isOpen_ball, fun a b => (hτ.2.1 a b).mono hT',
        fun b hb => hτ.2.2 b (hT' hb)⟩ (convex_ball v ε) j m' φ
      ⟨fun l hl => ⟨(hfac.1 l hl).1.mono (covMono hT'), fun Q hQ => (hfac.1 l hl).2 Q (covMono hT' hQ)⟩,
        fun l hl l' hl' Q hQ => hfac.2 l hl l' hl' Q (covMono hT' hQ)⟩
      ⟨ι, isoMono h4 hι⟩ (fun b hb => hpol b (hT' hb)) (isoMono h5 hφ)
      (fun Q hQ => mul_pos (hpos Q (covMono hT' hQ)) (Real.exp_pos _))
      (fun l hl Q hQ => hper l hl Q (covMono hT' hQ))
      (fun b hb => by
        have hb' : b ∈ c.e.target := hT' hb
        have c1 : Continuous fun z : Fin P.g → ℂ => m (b, z) :=
          hcd.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
            (fun z => hmem.2 hb')
        have c2 : Continuous fun z : Fin P.g → ℂ => u σ (ex (b, z)) :=
          (hu σ).comp (GlobalTheory.T.period_chart_continuous_fibre k S p P h σ c τ ex hPC b hb')
        exact c1.mul (c2.neg.rexp))
      (fun Q hQ => hφeq Q (covMono h5 hQ))
    exact ⟨B, hT', Metric.isOpen_ball, Metric.mem_ball_self hε, hres⟩
  refine ⟨⟨?_, fun Q hQ => mul_pos (hpos Q hQ) (Real.exp_pos _), hper⟩, ?_⟩
  · refine contDiffOn_of_locally_contDiffOn fun Q hQ => ?_
    obtain ⟨B', -, hB'o, hv, hM, -⟩ := hloc Q.1 (hmem.1 hQ)
    exact ⟨cov B' P.g, hB'o.prod isOpen_univ, hmem.2 hv, hM.1.mono Set.inter_subset_right⟩
  · intro Q hQ v w
    obtain ⟨B', -, -, hv, -, hC⟩ := hloc Q.1 (hmem.1 hQ)
    exact hC Q (hmem.2 hv) v w

end GlobalTheory.TateChart
