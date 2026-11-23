import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MIntEqOfLeviEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialChartContDiffAtTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlurisubharmonicOffBoundaryStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical

namespace GlobalTheory.DetLineFlat

section Gen

open Filter Topology

variable {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}

theorem leviAt_eq_zero_of_null {P : LocPot X} (hP : IsPotential A P) {Z : Set X}
    (hZ : ∀ j, MeasureTheory.volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Z) = 0)
    (h : ∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∉ Z → ∀ w, leviAt A P j y w = 0)
    (j : Fin A.n) {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) (w : Fin e → ℂ) : leviAt A P j y w = 0 := by
  set x := (A.chart j).symm y with hx
  have ho : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) :=
    (A.chart j).isOpen_inter_preimage_symm (P.isOpen_U x)
  have hc : ContinuousOn (fun v => levi (P.φ x ∘ (A.chart j).symm) v w)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) :=
    (continuousOn_levi ho ((hP.1 x j).of_le (by norm_cast))).comp (f := fun v => (v, w))
      (continuous_id.prodMk continuous_const).continuousOn fun v hv => ⟨hv, Set.mem_univ _⟩
  have hae : (fun v => levi (P.φ x ∘ (A.chart j).symm) v w) =ᵐ[MeasureTheory.volume.restrict
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x)] fun _ => (0 : ℝ) := by
    refine (MeasureTheory.ae_restrict_iff' ho.measurableSet).2 ?_
    filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.1 (hZ j)] with v hv hvU
    rw [GlobalTheory.LeviOnly.levi_base hP x j hvU.1 hvU.2]
    exact h j v hvU.1 (fun hz => hv ⟨hvU.1, hz⟩) w
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq hae ho hc continuousOn_const ⟨hy, P.mem_U _⟩

theorem leviAt_add_congr (P : LocPot X) {Z : Set X} (hZ : IsClosed Z) {u v : X → ℝ} (h : ∀ x, x ∉ Z → u x = v x)
    (j : Fin A.n) {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) (hyZ : (A.chart j).symm y ∉ Z) (w : Fin e → ℂ) :
    leviAt A (P + LocPot.ofFun u) j y w = leviAt A (P + LocPot.ofFun v) j y w := by
  refine levi_congr ?_ w
  filter_upwards [((A.chart j).isOpen_inter_preimage_symm hZ.isOpen_compl).mem_nhds ⟨hy, hyZ⟩] with z hz
  exact congrArg (P.φ _ ((A.chart j).symm z) + ·) (h _ hz.2)

theorem isPotential_ofFun {u : X → ℝ} (hu : A.Smooth u) : IsPotential A (LocPot.ofFun u) :=
  ⟨fun _ => hu, fun _ _ _ _ => ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun _ => 0,
    fun _ => analyticOnNhd_const, fun _ _ => by simp [LocPot.ofFun]⟩⟩

end Gen

theorem leviEq_zero_of_pshOff {D : D7} {Y : DV.ShimX D.what₂.Tau} (T : Real0 Y) (B : ℝ) (c : Y.Comp) (u : Wt Y)
    (g : (T.M c).Fun) (hg : (T.M c).Smooth g) (σ : Fin ((T.M c).n + 1))
    (h₁ : ∀ x, x ∉ (T.M c).Z σ → g σ x = (T.F c).ph u σ x)
    (h₂ : ∀ x, x ∉ (T.M c).Z σ → (T.F c).ph (-u) σ x = -(T.F c).ph u σ x)
    (p₁ : PshOff ((T.M c).A σ) ((T.M c).Z σ) ((T.F c).th u σ + LocPot.ofFun ((T.F c).ph u σ)))
    (p₂ : PshOff ((T.M c).A σ) ((T.M c).Z σ) ((T.F c).th (-u) σ + LocPot.ofFun ((T.F c).ph (-u) σ))) :
    LeviEq ((T.M c).A σ) ((T.K B c).c1 (T.L B c u + (T.K B c).ar g) σ) (LocPot.ofFun fun _ => 0) := by
  intro j y hy w
  rw [Deg.leviAt_const]
  have hZ := ((T.M c).bd σ).1
  refine leviAt_eq_zero_of_null ((T.K B c).firstChern_isPotential _ σ) ((T.M c).bd σ).2.1 (fun j y hy hyZ w => ?_) j hy w
  have hgp : IsPotential ((T.M c).A σ) (LocPot.ofFun (g σ)) := isPotential_ofFun (hg σ)
  have hgn : IsPotential ((T.M c).A σ) ((LocPot.ofFun (g σ)).rsmul (-1)) := isPotentialRsmul _ _ _ hgp
  have a₁ := p₁ j y hy hyZ w
  have a₂ := p₂ j y hy hyZ w
  rw [← leviAt_add_congr _ hZ h₁ j hy hyZ, Deg.leviAt_add _ (T.th_pot c _ σ) hgp j hy] at a₁
  rw [leviAt_add_congr _ hZ (v := fun x => -1 * g σ x) (fun x hx => by rw [h₂ x hx, h₁ x hx, neg_one_mul]) j hy hyZ] at a₂
  change 0 ≤ leviAt _ ((T.F c).th (-u) σ + (LocPot.ofFun (g σ)).rsmul (-1)) j y w at a₂
  rw [Deg.leviAt_add _ (T.th_pot c _ σ) hgn j hy, Deg.leviAt_rsmul, ← T.c1_L B c (-u) σ j y hy w,
    ← neg_one_smul ℝ u, map_smul, (T.K B c).firstChern_smul_leviEq _ _ σ j y hy w, Deg.leviAt_rsmul, T.c1_L B c u σ j y hy w] at a₂
  rw [(T.K B c).isOneCochain_add _ _ σ j y hy w, Deg.leviAt_add _ ((T.K B c).firstChern_isPotential _ σ) ((T.K B c).firstChern_isPotential _ σ) j hy,
    T.c1_L B c u σ j y hy w, (T.K B c).c1_ar g hg σ j y hy w]
  linarith

theorem first_chern_form_determinant_line_eq_zero : Hypotheses2 → HypothesesH → OnObj fun D O _ T _ _ => ∀ (B : ℝ) (τ : D.what₂.Tau) c (g : (T.M c).Fun),
    (T.M c).Smooth g →
    (∀ σ x, x ∉ (T.M c).Z σ → g σ x = (T.F c).ph (fun σ' _ => if σ' = τ then (-1 : ℝ) else 0) σ x) →
    ∀ σ, LeviEq ((T.M c).A σ)
      ((T.K B c).c1 (T.L B c (fun σ' _ => if σ' = τ then (-1 : ℝ) else 0) + (T.K B c).ar g) σ)
      (LocPot.ofFun fun _ => 0) := by
  intro h1 h2 D O hC hf A T H h B τ c g hg hgZ σ
  refine leviEq_zero_of_pshOff T B c _ g hg σ (hgZ σ) (fun x hx => ?_)
    (GlobalTheory.T.plurisubharmonic_off_boundary h1 h2 D O hC hf A T H h c _ (fun _ _ _ _ => le_rfl) σ)
    (GlobalTheory.T.plurisubharmonic_off_boundary h1 h2 D O hC hf A T H h c _ (fun _ _ _ _ => le_rfl) σ)
  refine ((h.an c).ph _ σ x hx).trans (Eq.trans ?_ (congrArg Neg.neg ((h.an c).ph _ σ x hx).symm))
  simp only [Setup.chg]
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => neg_mul _ _

end GlobalTheory.DetLineFlat
