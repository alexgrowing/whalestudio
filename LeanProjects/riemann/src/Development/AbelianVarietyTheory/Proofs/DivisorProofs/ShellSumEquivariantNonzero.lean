import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIntegralShellsVanishBeyondPeriodRamifiedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIntegralEquivariantNonzeroStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CartanAntitone
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableZetaIntegrand
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulLeftInvariantVolGL

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

noncomputable section
namespace GlobalTheory.ShellSumEqv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_unique_shell {ϖ : kˣ} (hϖ : IsUnif ϖ) {a : ℕ} (g : GL (Fin a) k) :
    ∃! m : {m : Fin a → ℤ // Antitone m}, g ∈ shellSet ϖ m.1 := by
  obtain ⟨m, hm, x, hx, y, hy, e⟩ := GlobalTheory.SortedCartan.cartan_antitone k a ϖ hϖ g
  have ht : ∀ m : Fin a → ℤ, GlobalTheory.GLDoubling.torusElt k (Fin a) ϖ m = diagGL fun i => ϖ ^ m i :=
    fun m => Units.ext (by rw [GlobalTheory.GLDoubling.val_torusElt, diagGL_val]; simp [Units.val_zpow_eq_zpow_val])
  refine ⟨⟨m, hm⟩, mem_shellSet.2 ⟨x, hx, y, hy, by rw [e, ht]⟩, ?_⟩
  rintro ⟨m', hm'⟩ hmem
  obtain ⟨x', hx', y', hy', e'⟩ := mem_shellSet.1 hmem
  have E : (x'⁻¹ * x) * diagGL (fun i => ϖ ^ m i) * (y * y'⁻¹) = diagGL fun i => ϖ ^ m' i := by
    have h1 : x * diagGL (fun i => ϖ ^ m i) * y = x' * diagGL (fun i => ϖ ^ m' i) * y' := by
      rw [← ht, ← e]; exact e'
    calc _ = x'⁻¹ * (x * diagGL (fun i => ϖ ^ m i) * y) * y'⁻¹ := by group
      _ = _ := by rw [h1]; group
  have E' := congrArg Units.val E
  simp only [Units.val_mul, diagGL_val, Units.val_zpow_eq_zpow_val] at E'
  exact Subtype.ext (Formalism.UG.P.cartan_unique_gen 𝒪[k] (valuation k) (fun _ => Iff.rfl) (ϖ : k) ϖ.ne_zero
    (hϖ ▸ uniformizer_lt_one) m m' hm hm' (x'⁻¹ * x) (mul_mem (inv_mem hx') hx) (y * y'⁻¹)
    (mul_mem hy (inv_mem hy')) (by simpa only [Units.val_mul] using E')).symm

theorem isOpen_shellSet (ϖ : kˣ) {a : ℕ} (m : Fin a → ℤ) : IsOpen (shellSet ϖ m : Set (GL (Fin a) k)) := by
  have : shellSet ϖ m = ⋃ x ∈ (KO k (Fin a) : Set (GL (Fin a) k)),
      (fun g => (x * diagGL (fun i => ϖ ^ m i))⁻¹ * g) ⁻¹' (KO k (Fin a) : Set _) := by
    ext g
    simp only [mem_shellSet, Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe, exists_prop]
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      exact ⟨x, hx, by simpa [mul_assoc] using hy⟩
    · rintro ⟨x, hx, hy⟩
      exact ⟨x, hx, _, hy, by group⟩
  rw [this]
  exact isOpen_biUnion fun x _ => isOpen_KO.preimage (continuous_const.mul continuous_id)

theorem apow_of_mem_shellSet {ϖ : kˣ} {a : ℕ} {m : Fin a → ℤ} {g : GL (Fin a) k} (hg : g ∈ shellSet ϖ m)
    (w : ℂ) : apow (gdet g) w = apow (gdet (diagGL fun i => ϖ ^ m i)) w := by
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_shellSet.1 hg
  rw [gdet_mul, gdet_mul, apow_mul, apow_mul, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hx),
    apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hy)]
  ring

theorem continuous_char_det {a : ℕ} {ν : kˣ →* ℂˣ} (hν : IsSmU ν) :
    Continuous fun g : GL (Fin a) k => ((ν (gdet g) : ℂˣ) : ℂ) := by
  set χ : GL (Fin a) k →* ℂˣ := ν.comp Matrix.GeneralLinearGroup.det with hχd
  have hcd : Continuous (Matrix.GeneralLinearGroup.det : GL (Fin a) k → kˣ) :=
    Units.continuous_iff.2 ⟨Units.continuous_val.matrix_det, Units.continuous_coe_inv.matrix_det⟩
  have hχ : IsOpen (χ.ker : Set (GL (Fin a) k)) := hν.1.preimage hcd
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_eventually_eq _).mpr fun g0 => ?_)
  have hn : (fun g => g0⁻¹ * g) ⁻¹' (χ.ker : Set (GL (Fin a) k)) ∈ nhds g0 :=
    (hχ.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp)
  filter_upwards [hn] with g hg
  have hg' : χ (g0⁻¹ * g) = 1 := hg
  have e : χ g = χ g0 := by
    have := congrArg (χ g0 * ·) hg'
    simp only [← map_mul, mul_inv_cancel_left, mul_one] at this
    exact this
  exact congrArg (fun u : ℂˣ => (u : ℂ)) e

variable [MeasurableSpace k] [BorelSpace k]

theorem exists_integrable {a : ℕ} {ν : kˣ →* ℂˣ} (hν : IsSmU ν) {φ : Matrix (Fin a) (Fin a) k → ℂ}
    (hφ : φ ∈ SB (Matrix (Fin a) (Fin a) k)) : ∃ B : ℝ, ∀ w : ℂ, B < w.re →
      Integrable (fun g : GL (Fin a) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) w)
        (haarVol (KO k (Fin a))) := by
  obtain ⟨b, hb⟩ := GlobalTheory.ZetaConvergence.integrable_zetaIntegrand k Measure.addHaar (Fin a)
    (fun g => ((ν (gdet g) : ℂˣ) : ℂ)) 0 (continuous_char_det hν)
    (fun N => ⟨1, fun g _ => by simp [hν.2]⟩) φ hφ
  refine ⟨b + ((a : ℝ) - 1) / 2, fun w hw => ?_⟩
  have h1 := hb (w - ((a : ℂ) - 1) / 2) (by
    have : (((a : ℂ) - 1) / 2).re = ((a : ℝ) - 1) / 2 := by simp
    rw [Complex.sub_re, this]; linarith)
  have hfun : GlobalTheory.InertSupp.zetaIntegrand φ (fun g => ((ν (gdet g) : ℂˣ) : ℂ)) (w - ((a : ℂ) - 1) / 2) =
      fun g : GL (Fin a) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) w := by
    funext g
    simp [GlobalTheory.InertSupp.zetaIntegrand, GlobalTheory.SmGL.val_absPow, apow]
  rw [hfun] at h1
  haveI := isHaarMeasure_volGL (k := k) (n := Fin a) Measure.addHaar
  rw [Measure.isMulLeftInvariant_eq_smul (haarVol (KO k (Fin a))) (volGL Measure.addHaar (Fin a))]
  exact h1.smul_measure_nnreal

section Shells
variable {ϖ : kˣ} {ν : kˣ →* ℂˣ} {e : ℕ}

theorem finite_shells (hϖ : IsUnif ϖ) (hram : ¬ IsUnram ν) (hcond : CondLE ϖ e ν) {a : ℕ}
    {φ : Matrix (Fin a) (Fin a) k → ℂ} (hφ : φ ∈ SB (Matrix (Fin a) (Fin a) k)) :
    {m : {m : Fin a → ℤ // Antitone m} | ∃ z : ℂ, shell (haarVol (KO k (Fin a))) ϖ ν z φ m.1 ≠ 0}.Finite :=
  (GlobalTheory.T.zetaIntegralShells_vanish_beyondPeriod_ramified k ϖ hϖ ν e hram hcond a (haarVol (KO k (Fin a))) φ hφ).2.2.2

theorem integrableOn_shell (hϖ : IsUnif ϖ) (hram : ¬ IsUnram ν) (hcond : CondLE ϖ e ν) {a : ℕ}
    {φ : Matrix (Fin a) (Fin a) k → ℂ} (hφ : φ ∈ SB (Matrix (Fin a) (Fin a) k)) (m : Fin a → ℤ) (w : ℂ) :
    IntegrableOn (fun g : GL (Fin a) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) w) (shellSet ϖ m)
      (haarVol (KO k (Fin a))) :=
  (GlobalTheory.T.zetaIntegralShells_vanish_beyondPeriod_ramified k ϖ hϖ ν e hram hcond a (haarVol (KO k (Fin a))) φ hφ).1 m w

theorem support_finite (hϖ : IsUnif ϖ) (hram : ¬ IsUnram ν) (hcond : CondLE ϖ e ν) {a : ℕ}
    {φ : Matrix (Fin a) (Fin a) k → ℂ} (hφ : φ ∈ SB (Matrix (Fin a) (Fin a) k)) (w : ℂ) :
    (Function.support fun m : {m : Fin a → ℤ // Antitone m} =>
      shell (haarVol (KO k (Fin a))) ϖ ν w φ m.1).Finite :=
  (finite_shells hϖ hram hcond hφ).subset fun m hm => ⟨w, hm⟩

theorem integral_eq_shellSum (hϖ : IsUnif ϖ) (hram : ¬ IsUnram ν) (hcond : CondLE ϖ e ν) {a : ℕ}
    {φ : Matrix (Fin a) (Fin a) k → ℂ} (hφ : φ ∈ SB (Matrix (Fin a) (Fin a) k)) {w : ℂ}
    (hint : Integrable (fun g : GL (Fin a) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) w)
      (haarVol (KO k (Fin a)))) :
    ∫ g, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) w ∂(haarVol (KO k (Fin a))) =
      shellSum (haarVol (KO k (Fin a))) ϖ ν w φ := by
  set S : {m : Fin a → ℤ // Antitone m} → Set (GL (Fin a) k) := fun m => shellSet ϖ m.1 with hS
  have hU : ⋃ m, S m = Set.univ :=
    Set.eq_univ_of_forall fun g => Set.mem_iUnion.2 (exists_unique_shell hϖ g).exists
  have hd : Pairwise (Function.onFun Disjoint S) := fun m m' hne =>
    Set.disjoint_left.2 fun g h1 h2 => hne ((exists_unique_shell hϖ g).unique h1 h2)
  haveI : BorelSpace (GL (Fin a) k) := borel_GL
  have hm : ∀ m, MeasurableSet (S m) := fun m => (isOpen_shellSet ϖ m.1).measurableSet
  calc _ = ∫ g in ⋃ m, S m, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) w ∂(haarVol (KO k (Fin a))) := by
        rw [hU, Measure.restrict_univ]
    _ = ∑' m, ∫ g in S m, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) w ∂(haarVol (KO k (Fin a))) :=
        integral_iUnion hm hd hint.integrableOn
    _ = ∑ᶠ m, ∫ g in S m, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) w ∂(haarVol (KO k (Fin a))) :=
        tsum_eq_finsum (support_finite hϖ hram hcond hφ w)
    _ = _ := rfl

theorem shell_eq_mul [BorelSpace k] {a : ℕ} (μ : Measure (GL (Fin a) k)) (φ : Matrix (Fin a) (Fin a) k → ℂ) (m : Fin a → ℤ)
    (w : ℂ) : shell μ ϖ ν w φ m = (∫ g in shellSet ϖ m, φ g.val * (ν (gdet g) : ℂ) ∂μ) *
      apow (gdet (diagGL fun i => ϖ ^ m i)) w := by
  unfold shell
  rw [← integral_mul_const]
  haveI : BorelSpace (GL (Fin a) k) := borel_GL
  exact setIntegral_congr_fun (isOpen_shellSet ϖ m).measurableSet fun g hg => by
    simp only [apow_of_mem_shellSet hg]

theorem differentiable_shellSum (hϖ : IsUnif ϖ) (hram : ¬ IsUnram ν) (hcond : CondLE ϖ e ν) {a : ℕ}
    {φ : Matrix (Fin a) (Fin a) k → ℂ} (hφ : φ ∈ SB (Matrix (Fin a) (Fin a) k)) :
    Differentiable ℂ fun w => shellSum (haarVol (KO k (Fin a))) ϖ ν w φ := by
  set F := (finite_shells hϖ hram hcond hφ).toFinset
  have h : (fun w => shellSum (haarVol (KO k (Fin a))) ϖ ν w φ) =
      fun w => ∑ m ∈ F, shell (haarVol (KO k (Fin a))) ϖ ν w φ m.1 := by
    funext w
    refine finsum_eq_sum_of_support_subset _ fun m hm => ?_
    simpa [F] using (⟨w, hm⟩ : ∃ z : ℂ, shell (haarVol (KO k (Fin a))) ϖ ν z φ m.1 ≠ 0)
  rw [h]
  refine Differentiable.fun_sum fun m _ => ?_
  show Differentiable ℂ fun w => shell (haarVol (KO k (Fin a))) ϖ ν w φ m.1
  rw [funext fun w => shell_eq_mul (ϖ := ϖ) (ν := ν) (haarVol (KO k (Fin a))) φ m.1 w]
  refine Differentiable.const_mul ?_ _
  have hp := nabs_pos' (gdet (diagGL fun i => ϖ ^ m.1 i))
  exact differentiable_id.const_cpow (Or.inl (by exact_mod_cast hp.ne'))

end Shells

section Main
variable {ϖ : kˣ} {ν : kˣ →* ℂˣ} {e : ℕ}

theorem differentiable_apow (x : kˣ) : Differentiable ℂ fun w => apow x w := by
  have hp := nabs_pos' x
  unfold apow
  exact differentiable_id.const_cpow (Or.inl (by exact_mod_cast hp.ne'))

theorem shellSum_add (hϖ : IsUnif ϖ) (hram : ¬ IsUnram ν) (hcond : CondLE ϖ e ν) {a : ℕ}
    {φ φ' : Matrix (Fin a) (Fin a) k → ℂ} (hφ : φ ∈ SB (Matrix (Fin a) (Fin a) k))
    (hφ' : φ' ∈ SB (Matrix (Fin a) (Fin a) k)) (w : ℂ) :
    shellSum (haarVol (KO k (Fin a))) ϖ ν w (φ + φ') =
      shellSum (haarVol (KO k (Fin a))) ϖ ν w φ + shellSum (haarVol (KO k (Fin a))) ϖ ν w φ' := by
  unfold shellSum
  rw [← finsum_add_distrib (support_finite hϖ hram hcond hφ w) (support_finite hϖ hram hcond hφ' w)]
  refine finsum_congr fun m => ?_
  unfold shell
  rw [← integral_add (integrableOn_shell hϖ hram hcond hφ m.1 w) (integrableOn_shell hϖ hram hcond hφ' m.1 w)]
  congr 1
  funext g
  simp only [Pi.add_apply]
  ring

theorem shellSum_eqv (hϖ : IsUnif ϖ) (hν : IsSmU ν) (hram : ¬ IsUnram ν) (hcond : CondLE ϖ e ν) {a : ℕ}
    (g₁ g₂ : GL (Fin a) k) {φ : Matrix (Fin a) (Fin a) k → ℂ} (hφ : φ ∈ SB (Matrix (Fin a) (Fin a) k)) (z : ℂ) :
    (ν (gdet g₁ * gdet g₂) : ℂ) * apow (gdet g₁ * gdet g₂) z *
      shellSum (haarVol (KO k (Fin a))) ϖ ν z (fun X => φ (g₁.val * X * g₂.val)) =
      shellSum (haarVol (KO k (Fin a))) ϖ ν z φ := by
  have hφ' := comp_mul_mem_SB g₁ g₂ hφ
  obtain ⟨B₁, h₁⟩ := exists_integrable hν hφ
  obtain ⟨B₂, h₂⟩ := exists_integrable hν hφ'
  set B := max (max B₁ B₂) ((a : ℝ) - 1) with hB
  have hL : Differentiable ℂ fun w => (ν (gdet g₁ * gdet g₂) : ℂ) * apow (gdet g₁ * gdet g₂) w *
      shellSum (haarVol (KO k (Fin a))) ϖ ν w (fun X => φ (g₁.val * X * g₂.val)) :=
    ((differentiable_apow _).const_mul _).mul (differentiable_shellSum hϖ hram hcond hφ')
  have hR := differentiable_shellSum hϖ hram hcond hφ
  have ho : IsOpen {w : ℂ | B < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hE := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (fun w _ => hL.analyticAt w)
    (fun w _ => hR.analyticAt w) isPreconnected_univ (Set.mem_univ (((B + 1 : ℝ)) : ℂ)) (by
      filter_upwards [ho.mem_nhds (show B < (((B + 1 : ℝ)) : ℂ).re by simp)] with w hw
      have hw : B < w.re := hw
      have hB1 : B₁ < w.re := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hw
      have hB2 : B₂ < w.re := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hw
      have hB3 : (a : ℝ) - 1 < w.re := lt_of_le_of_lt (le_max_right _ _) hw
      rw [← integral_eq_shellSum hϖ hram hcond hφ (h₁ w hB1),
        ← integral_eq_shellSum hϖ hram hcond hφ' (h₂ w hB2)]
      exact (GlobalTheory.T.zeta_integral_equivariant_nonzero k a ν w hν hB3).1.2.2 g₁ g₂ φ hφ)
  exact hE (Set.mem_univ z)

theorem exists_ne_zero (hϖ : IsUnif ϖ) (hcond : CondLE ϖ e ν) {a : ℕ} (z : ℂ) :
    ∃ φ ∈ SB (Matrix (Fin a) (Fin a) k), shellSum (haarVol (KO k (Fin a))) ϖ ν z φ ≠ 0 := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  haveI : BorelSpace (GL (Fin a) k) := borel_GL
  set D := detCong (ϖ ^ e) (Fin a) with hDdef
  have hDo : IsOpen (D : Set (GL (Fin a) k)) := isOpen_detCong _ _
  have hDc : IsClosed (D : Set (GL (Fin a) k)) := D.isClosed_of_isOpen hDo
  have hDK : (D : Set (GL (Fin a) k)) ⊆ KO k (Fin a) := fun g hg => hg.1
  have hDk : IsCompact (D : Set (GL (Fin a) k)) := isCompact_KO.of_isClosed_subset hDc hDK
  have hoe : Topology.IsOpenEmbedding (fun g : GL (Fin a) k => g.val) := by
    refine ⟨isEmbedding_val_GL, ?_⟩
    have : Set.range (fun g : GL (Fin a) k => g.val) = {x : Matrix (Fin a) (Fin a) k | x.det ≠ 0} := by
      ext x
      simp only [Set.mem_range, Set.mem_setOf_eq]
      rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det]
      rfl
    rw [this]
    exact isOpen_ne_fun (continuous_id.matrix_det) continuous_const
  set T : Set (Matrix (Fin a) (Fin a) k) := (fun g : GL (Fin a) k => g.val) '' D with hTdef
  have hTk : IsCompact T := hDk.image hoe.continuous
  have hTo : IsOpen T := hoe.isOpenMap _ hDo
  have hT : ∀ g : GL (Fin a) k, g.val ∈ T ↔ g ∈ D := fun g =>
    ⟨by rintro ⟨g', hg', h⟩; exact (Units.ext h : g' = g) ▸ hg', fun h => ⟨g, h, rfl⟩⟩
  have hSB : T.indicator (1 : Matrix (Fin a) (Fin a) k → ℂ) ∈ SB (Matrix (Fin a) (Fin a) k) :=
    ⟨(LocallyConstant.indicator (1 : LocallyConstant _ ℂ) ⟨hTk.isClosed, hTo⟩).isLocallyConstant,
      HasCompactSupport.intro hTk fun x hx => Set.indicator_of_notMem hx _⟩
  refine ⟨_, hSB, ?_⟩
  have h0 : ∀ m : {m : Fin a → ℤ // Antitone m}, m ≠ ⟨0, antitone_const⟩ →
      shell (haarVol (KO k (Fin a))) ϖ ν z (T.indicator 1) m.1 = 0 := by
    intro m hm
    unfold shell
    refine setIntegral_eq_zero_of_forall_eq_zero fun g hg => ?_
    have hgT : g.val ∉ T := fun h => hm ((exists_unique_shell hϖ g).unique hg
      (show g ∈ shellSet ϖ (0 : Fin a → ℤ) by rw [shellSet_zero]; exact hDK ((hT g).1 h)))
    simp [Set.indicator_of_notMem hgT]
  rw [shellSum, finsum_eq_single _ ⟨0, antitone_const⟩ h0]
  show shell (haarVol (KO k (Fin a))) ϖ ν z (T.indicator 1) (0 : Fin a → ℤ) ≠ 0
  unfold shell
  rw [shellSet_zero]
  have hval : ∫ g in (KO k (Fin a) : Set (GL (Fin a) k)),
      T.indicator 1 g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂(haarVol (KO k (Fin a))) =
      ∫ g in (KO k (Fin a) : Set (GL (Fin a) k)), (D : Set (GL (Fin a) k)).indicator (fun _ => (1 : ℂ)) g
        ∂(haarVol (KO k (Fin a))) := by
    refine setIntegral_congr_fun isOpen_KO.measurableSet fun g hg => ?_
    by_cases hgD : g ∈ D
    · rw [Set.indicator_of_mem ((hT g).2 hgD), Set.indicator_of_mem hgD,
        apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hg), hcond (gdet g) hgD.2]
      simp
    · rw [Set.indicator_of_notMem (fun h => hgD ((hT g).1 h)), Set.indicator_of_notMem hgD]
      simp
  rw [hval]
  have hmD : MeasurableSet (D : Set (GL (Fin a) k)) := hDo.measurableSet
  erw [integral_indicator hmD, Measure.restrict_restrict hmD, setIntegral_const, Set.inter_eq_left.2 hDK]
  have hpos : haarVol (KO k (Fin a)) (D : Set (GL (Fin a) k)) ≠ 0 := (hDo.measure_pos _ ⟨1, one_mem D⟩).ne'
  have hfin : haarVol (KO k (Fin a)) (D : Set (GL (Fin a) k)) ≠ ⊤ := hDk.measure_lt_top.ne
  simp only [Measure.real]
  rw [Complex.real_smul, mul_one, Complex.ofReal_ne_zero]
  exact (ENNReal.toReal_pos hpos hfin).ne'

theorem shellSum_isEqv_and_ne_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ϖ : kˣ) (n e : ℕ) (ν : kˣ →* ℂˣ) (z : ℂ),
    IsUnif ϖ → IsSmU ν → ¬ IsUnram ν → CondLE ϖ e ν →
    IsEqv ν z (shellSum (haarVol (KO k (Fin n))) ϖ ν z) ∧
    ∃ φ ∈ SB (Matrix (Fin n) (Fin n) k), shellSum (haarVol (KO k (Fin n))) ϖ ν z φ ≠ 0 := by
  intro k _ _ _ _ _ _ ϖ n e ν z hϖ hν hram hcond
  refine ⟨⟨fun φ hφ φ' hφ' => shellSum_add hϖ hram hcond hφ hφ' z, fun c φ _ => ?_,
    fun g₁ g₂ φ hφ => shellSum_eqv hϖ hν hram hcond g₁ g₂ hφ z⟩, exists_ne_zero hϖ hcond z⟩
  exact shellSum_smul _ ϖ ν z c φ

end Main

end GlobalTheory.ShellSumEqv
