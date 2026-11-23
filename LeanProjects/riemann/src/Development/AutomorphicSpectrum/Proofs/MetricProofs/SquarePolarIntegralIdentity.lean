import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.TsgPolyVolPolyCoeffEven
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereSingularTotalMassDegree
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereIntegralMultilinearExpansion
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticSystemRegularityProperties
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereIntegralParametrizedCover
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogSineMongeAmpereIntegralStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SquareParametrizedDensityFormulaStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticSquareRegularizedConvergenceStatement

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

namespace SqFubini

def eY (d : ℕ) : ((Fin d → ℂ) × ℂ) ≃ᵐ (Fin (d + 1) → ℂ) :=
  MeasurableEquiv.prodComm.trans (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) 0).symm

theorem eY_apply {d : ℕ} (x : (Fin d → ℂ) × ℂ) : eY d x = Fin.cons x.2 x.1 := by
  first | rfl | (simp [eY, MeasurableEquiv.piFinSuccAbove, Fin.consEquiv]; done) | (simp [eY, MeasurableEquiv.piFinSuccAbove]; rfl)

theorem eY_measurePreserving (d : ℕ) : MeasurePreserving (eY d) volume volume :=
  (Measure.measurePreserving_swap).trans
    (volume_preserving_piFinSuccAbove (fun _ => ℂ) 0).symm

def eW (d : ℕ) : ((Fin d → ℂ) × (ℂ × ℂ)) ≃ᵐ (Fin (d + 2) → ℂ) :=
  (MeasurableEquiv.prodComm.trans MeasurableEquiv.prodAssoc).trans
    ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℂ)
      (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) 0).symm).trans
      (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) 0).symm)

theorem eW_apply {d : ℕ} (x : (Fin d → ℂ) × (ℂ × ℂ)) :
    eW d x = Fin.cons x.2.1 (Fin.cons x.2.2 x.1) := by
  first | rfl | (simp [eW, MeasurableEquiv.piFinSuccAbove, Fin.consEquiv]; done) | (simp [eW, MeasurableEquiv.piFinSuccAbove]; rfl)

theorem eW_measurePreserving (d : ℕ) : MeasurePreserving (eW d) volume volume :=
  ((Measure.measurePreserving_swap).trans (measurePreserving_prodAssoc volume volume volume)).trans
    (((MeasurePreserving.id volume).prod
      (volume_preserving_piFinSuccAbove (fun _ => ℂ) 0).symm).trans
      (volume_preserving_piFinSuccAbove (fun _ => ℂ) 0).symm)

theorem fubini_piece {Y P Z : Type*} [MeasurableSpace Y] [MeasurableSpace P] [MeasurableSpace Z]
    (μ : Measure Y) (ν : Measure P) (ρ : Measure Z) [SFinite μ] [SFinite ν]
    (e : (Y × P) ≃ᵐ Z) (he : MeasurePreserving e (μ.prod ν) ρ) (B : Set Y) (S : Set Z)
    (hS : e ⁻¹' S = B ×ˢ Set.univ) (F : Z → ℝ) (hF : IntegrableOn F S ρ) :
    IntegrableOn (fun y => ∫ p, F (e (y, p)) ∂ν) B μ ∧
      ∫ z in S, F z ∂ρ = ∫ y in B, ∫ p, F (e (y, p)) ∂ν ∂μ := by
  have h1 : IntegrableOn (F ∘ e) (B ×ˢ Set.univ) (μ.prod ν) := by
    rw [← hS]
    exact (he.integrableOn_comp_preimage e.measurableEmbedding).2 hF
  have h2 : ∫ z in S, F z ∂ρ = ∫ x in B ×ˢ Set.univ, F (e x) ∂(μ.prod ν) := by
    rw [← hS]
    exact (he.setIntegral_preimage_emb e.measurableEmbedding F S).symm
  constructor
  · have h3 : Integrable (F ∘ e) ((μ.restrict B).prod (ν.restrict Set.univ)) := by
      rw [Measure.prod_restrict]
      exact h1
    simpa [IntegrableOn, Function.comp_def] using h3.integral_prod_left
  · rw [h2]
    simpa [Function.comp_def] using setIntegral_prod (F ∘ e) h1

theorem fibre_sum {d k : ℕ} (B : Set (Fin d → ℂ)) (F : ℕ → (Fin (d + 2) → ℂ) → ℝ)
    (H : (Fin (d + 1) → ℂ) → ℝ) (κ : ℝ)
    (hF : ∀ i < k, IntegrableOn (F i) {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ B})
    (hH : IntegrableOn H {z : Fin (d + 1) → ℂ | Fin.tail z ∈ B})
    (hpt : ∀ y ∈ B, ∑ i ∈ Finset.range k, ∫ p : ℂ × ℂ, F i (Fin.cons p.1 (Fin.cons p.2 y)) =
      κ * ∫ a : ℂ, H (Fin.cons a y))
    (hB : MeasurableSet B) :
    ∑ i ∈ Finset.range k, ∫ z in {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ B}, F i z =
      κ * ∫ z in {z : Fin (d + 1) → ℂ | Fin.tail z ∈ B}, H z := by
  have hSW : (eW d) ⁻¹' {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ B} = B ×ˢ Set.univ := by
    ext x
    simp [eW_apply]
  have hSY : (eY d) ⁻¹' {z : Fin (d + 1) → ℂ | Fin.tail z ∈ B} = B ×ˢ Set.univ := by
    ext x
    simp [eY_apply]
  have hW := fun i (hi : i < k) => fubini_piece volume volume volume (eW d) (eW_measurePreserving d) B _ hSW
    (F i) (hF i hi)
  have hY := fubini_piece volume volume volume (eY d) (eY_measurePreserving d) B _ hSY H hH
  simp only [eW_apply, eY_apply] at hW hY
  rw [hY.2, Finset.sum_congr rfl fun i hi => (hW i (Finset.mem_range.1 hi)).2,
    ← integral_finset_sum _ fun i hi => (hW i (Finset.mem_range.1 hi)).1, ← integral_const_mul]
  exact setIntegral_congr_fun hB fun y hy => hpt y hy

theorem ae_ne (d : ℕ) : ∀ᵐ z : Fin (d + 2) → ℂ, z 0 ≠ z 1 := by
  let L : (Fin (d + 2) → ℂ) →ₗ[ℝ] ℂ :=
    (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 2) => ℂ) 0) -
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 2) => ℂ) 1)
  have hs : LinearMap.ker L ≠ ⊤ := by
    intro h
    have h1 : (Pi.single 0 1 : Fin (d + 2) → ℂ) ∈ LinearMap.ker L := by rw [h]; trivial
    simp [L, LinearMap.mem_ker, Pi.single_apply] at h1
  have h0 := Measure.addHaar_submodule (volume : Measure (Fin (d + 2) → ℂ)) (LinearMap.ker L) hs
  refine measure_mono_null ?_ h0
  intro z hz
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at hz
  simp [L, LinearMap.mem_ker, hz]

theorem isC2At_sumPot {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {σ : Type} [Fintype σ]
    (c : σ → ℝ) (P : σ → LocPot X) (x : X) (h : ∀ a, IsTwiceDifferentiableAt A (P a) x) : IsTwiceDifferentiableAt A (sumPot c P) x := by
  intro j hj
  have : (sumPot c P).φ x ∘ (A.chart j).symm =
      fun y => ∑ a, c a * ((P a).φ x ∘ (A.chart j).symm) y := rfl
  rw [this]
  exact ContDiffAt.sum fun a _ => contDiffAt_const.mul (h a j hj)

end SqFubini

namespace SqFubini

def EW {d : ℕ} (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (α : (Fin d → ℂ) → ℝ) (k i : ℕ) :
    Fin (d + 2) → (Fin (d + 2) → ℂ) → ℝ :=
  let u : ℕ → Fin 2 → ℝ := (fun (i : ℕ) (r : ℕ) (c : Fin 2) => if r = 0 then (![1, -1] : Fin 2 → ℝ) c else if r = 1 then (![0, 1] : Fin 2 → ℝ) c else if r < 2 + 2 * i then (![1, 0] : Fin 2 → ℝ) c else (![0, 1] : Fin 2 → ℝ) c) i
  fun (r : Fin (d + 2)) (z : Fin (d + 2) → ℂ) => if (r : ℕ) < 2 * k then u r 0 * xiPot (G (Fin.tail (Fin.tail z))) (z 0) + u r 1 * xiPot (G (Fin.tail (Fin.tail z))) (z 1) else α (Fin.tail (Fin.tail z))

def EY {d : ℕ} (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (α : (Fin d → ℂ) → ℝ) (k : ℕ) :
    Fin (d + 1) → (Fin (d + 1) → ℂ) → ℝ :=
  fun (r : Fin (d + 1)) (z : Fin (d + 1) → ℂ) => if (r : ℕ) < 2 * k - 1 then xiPot (G (Fin.tail z)) (z 0) else α (Fin.tail z)

end SqFubini

open SqFubini in

theorem AnSq.sum_polar_gH_eq : Inputs → GroundTheory.Heights₂.Heights.Inter.FibreLocal.Statement → ∀ (d : ℕ) (σ : Type) [Fintype σ] (SY : AnSys (d + 1) σ) (a₀ : σ) (ε : σ → ℤ) (Q : AnSq SY a₀ ε) (c : σ → ℝ), c a₀ = 0 → ∀ k : ℕ, 1 ≤ k → 2 * k ≤ d + 2 → ∑ i ∈ Finset.range k, polar (d + 2) (fun w => mInt Q.SW.A (fun r => Q.SW.potH (w r)) Q.gH) (Q.wcoef c k i) = 2 * kappa k * polar (d + 1) SY.degNum (mix (2 * k - 1) (fun a => (ε a : ℝ)) c) := by
  intro hI hF d σ _ SY a₀ ε Q c hc k hk1 hk2
  have hlim := GlobalTheory.T.analytic_square_regularized_convergence hI d σ SY a₀ ε Q
  obtain ⟨-, hnW, hC2W, -, -⟩ := anSys_open_basics (d + 2) (Option σ) Q.SW
  obtain ⟨-, hnY, hC2Y, -, -⟩ := anSys_open_basics (d + 1) σ SY
  have hhom := AnSys.mIntegrable_potH_and_mInt_eq_degNum hI.convergenceSigned (d + 1) σ SY

  have hexW := fun i => mInt_sumPot_expand (d + 2) Q.SW.X Q.SW.A (Option σ) Q.SW.open' Q.SW.potH
    (Q.wcoef c k i) Q.gH hnW hC2W fun w => (hlim w).1
  have hexY := mInt_sumPot_expand (d + 1) SY.X SY.A σ SY.open' SY.potH
    (mix (2 * k - 1) (fun a => (ε a : ℝ)) c) (fun _ => 1) hnY hC2Y fun w => (hhom w).1
  have hpolW : ∀ i, polar (d + 2) (fun w => mInt Q.SW.A (fun r => Q.SW.potH (w r)) Q.gH) (Q.wcoef c k i) =
      mInt Q.SW.A (fun r => sumPot (Q.wcoef c k i r) Q.SW.potH) Q.gH := fun i => (hexW i).2.symm
  have hpolY : polar (d + 1) SY.degNum (mix (2 * k - 1) (fun a => (ε a : ℝ)) c) =
      mInt SY.A (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) c r) SY.potH) (fun _ => 1) := by
    rw [hexY.2]
    exact Finset.sum_congr rfl fun w _ => by rw [(hhom w).2]

  have hoW : ∀ n (z : Fin (d + 2) → ℂ), Fin.tail (Fin.tail z) ∈ Q.U n → Q.ΦW n z ∈ Q.SW.open' := by
    intro n z hz
    rw [Q.bdry_eq 0, Set.mem_preimage, Q.first_projection_chart_compat n z hz]
    exact Q.ΦY_open n _ (by simpa using hz)

  have hcW := fun i => integrableOn_hasSum_paramCover (d + 2) Q.SW.X Q.SW.A _ _ Q.ΦW
    (fun r => sumPot (Q.wcoef c k i r) Q.SW.potH) Q.gH Q.coverW
    (fun n z hz r => isC2At_sumPot _ _ _ _ fun a => hC2W a _ (hoW n z (Q.B_meas n |>.2 hz)))
    (hexW i).1
  have hcY := integrableOn_hasSum_paramCover (d + 1) SY.X SY.A _ _ Q.ΦY
    (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) c r) SY.potH) (fun _ => 1) Q.coverY
    (fun n z hz r => isC2At_sumPot _ _ _ _ fun a => hC2Y a _ (Q.ΦY_open n z (Q.B_meas n |>.2 hz)))
    hexY.1

  have key : ∀ n, ∑ i ∈ Finset.range k, ∫ z in {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ Q.B n},
      Q.gH (Q.ΦW n z) * paramDens (fun r => sumPot (Q.wcoef c k i r) Q.SW.potH) (Q.ΦW n) z =
      2 * kappa k * ∫ z in {z : Fin (d + 1) → ℂ | Fin.tail z ∈ Q.B n},
        (fun _ => (1 : ℝ)) (Q.ΦY n z) * paramDens
          (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) c r) SY.potH) (Q.ΦY n) z := by
    intro n
    let α : (Fin d → ℂ) → ℝ := fun y => ∑ a, c a * Q.α n a y
    have hd := GlobalTheory.T.square_parametrized_density_formula d σ SY a₀ ε Q c hc n k hk1 hk2
    have hmW : MeasurableSet {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ Q.B n} := (Q.coverW.2.1 n).1
    have hmY : MeasurableSet {z : Fin (d + 1) → ℂ | Fin.tail z ∈ Q.B n} := (Q.coverY.2.1 n).1
    let F : ℕ → (Fin (d + 2) → ℂ) → ℝ := fun i z =>
      logSin (Q.G n (Fin.tail (Fin.tail z))) (z 0) (z 1) * maDens (EW (Q.G n) α k i) z
    have hae : ∀ i < k, ∀ᵐ z ∂(volume.restrict {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ Q.B n}),
        Q.gH (Q.ΦW n z) * paramDens (fun r => sumPot (Q.wcoef c k i r) Q.SW.potH) (Q.ΦW n) z = F i z := by
      intro i hi
      filter_upwards [ae_restrict_of_ae (ae_ne d), ae_restrict_mem hmW] with z hne hz
      have hU : Fin.tail (Fin.tail z) ∈ Q.U n := (Q.B_meas n).2 hz
      have h1 : Q.gH (Q.ΦW n z) = logSin (Q.G n (Fin.tail (Fin.tail z))) (z 0) (z 1) :=
        Q.norm_hom n z hU hne
      have h2 : paramDens (fun r => sumPot (Q.wcoef c k i r) Q.SW.potH) (Q.ΦW n) z =
          maDens (EW (Q.G n) α k i) z := hd.2 i hi z hU
      rw [h1, h2]
    have hH : ∀ z ∈ {z : Fin (d + 1) → ℂ | Fin.tail z ∈ Q.B n},
        (fun _ => (1 : ℝ)) (Q.ΦY n z) * paramDens
          (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) c r) SY.potH) (Q.ΦY n) z =
        maDens (EY (Q.G n) α k) z := by
      intro z hz
      have h2 : paramDens (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) c r) SY.potH) (Q.ΦY n) z =
          maDens (EY (Q.G n) α k) z := hd.1 z ((Q.B_meas n).2 hz)
      rw [h2, one_mul]
    have hFint : ∀ i < k, IntegrableOn (F i) {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ Q.B n} :=
      fun i hi => ((hcW i).1 n).congr (hae i hi)
    have hHint : IntegrableOn (maDens (EY (Q.G n) α k)) {z : Fin (d + 1) → ℂ | Fin.tail z ∈ Q.B n} :=
      (integrableOn_congr_fun hH hmY).1 (hcY.1 n)
    have hpt : ∀ y ∈ Q.B n, ∑ i ∈ Finset.range k, ∫ p : ℂ × ℂ, F i (Fin.cons p.1 (Fin.cons p.2 y)) =
        (2 * kappa k) * ∫ a : ℂ, maDens (EY (Q.G n) α k) (Fin.cons a y) := by
      intro y hy
      have hyU : y ∈ Q.U n := (Q.B_meas n).2 hy
      have hnh : Q.U n ∈ 𝓝 y := (Q.U_open n).mem_nhds hyU
      have h2 : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := ENat.LEInfty.out
      exact GlobalTheory.T.log_sine_monge_ampere_integral hF d k hk1 hk2 (Q.G n) α y
        (by filter_upwards [hnh] with y' hy' using Q.G_pos n y' hy')
        (fun p q => ((Q.G_smooth n p q).contDiffAt hnh).of_le h2)
        (ContDiffAt.sum fun a _ => contDiffAt_const.mul (((Q.α_smooth n a).contDiffAt hnh).of_le h2))
    rw [Finset.sum_congr rfl fun i hi => integral_congr_ae (hae i (Finset.mem_range.1 hi)),
      setIntegral_congr_fun hmY hH]
    exact fibre_sum (Q.B n) F _ _ hFint hHint hpt (Q.B_meas n).1
  have hsW : HasSum (fun n => ∑ i ∈ Finset.range k, ∫ z in {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ Q.B n},
      Q.gH (Q.ΦW n z) * paramDens (fun r => sumPot (Q.wcoef c k i r) Q.SW.potH) (Q.ΦW n) z)
      (∑ i ∈ Finset.range k, mInt Q.SW.A (fun r => sumPot (Q.wcoef c k i r) Q.SW.potH) Q.gH) :=
    hasSum_sum fun i _ => (hcW i).2
  rw [funext key] at hsW
  rw [Finset.sum_congr rfl fun i _ => hpolW i, hpolY]
  exact hsW.unique (hcY.2.mul_left _)

end GlobalTheory.CompanionTheory.Ar.PB
