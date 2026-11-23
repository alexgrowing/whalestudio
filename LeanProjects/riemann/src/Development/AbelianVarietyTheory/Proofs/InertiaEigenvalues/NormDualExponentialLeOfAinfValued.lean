import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import ReciprocityTheory.DualLattices.AinfFacts
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOrbitPadicComplex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPrimitiveRootPrimePowSubOnePadicComplex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormUnitPowSubOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateInvariantsCyclotomicTwistStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTwistCocycleCoboundary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTwistCocycleCoboundaryStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1BallCocycleLogCyclotomicStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyThetaOnBdRPlusPeriodData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFilQuotientXiPowerAinf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariantStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

noncomputable section

open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.TwistKill GlobalTheory.BdRQuot
open scoped Formalism.Per

namespace GlobalTheory.Cyc.ExpBound

variable {l : ℕ} [Fact l.Prime]

theorem norm_le_of_twist {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} {χ : GQ l →* ℚ_[l]ˣ}
    (ha : IsActC act) (hχ : IsCyc χ) (K : FinExt l) {s : ℕ} (hs : Lev l s) {j : ℤ} (hj : j ≠ 0)
    (β : PadicComplex l) (h : ∀ σ ∈ Gj K s, ‖chiC χ j σ * act σ β - β‖ ≤ 1) :
    ‖(l : PadicComplex l) ^ (1 + s + padicValInt l j) * β‖ ≤ 1 := by
  obtain ⟨γ, hγ, e⟩ := GlobalTheory.T.cyclotomic_twist_cocycle_coboundary l act χ ha hχ K s hs j hj
    (fun σ => chiC χ j σ * act σ β - β)
    ⟨(((continuous_chiC hχ j).mul (GlobalTheory.Cyc.IsActC.continuous_orbit l act ha β)).sub
      continuous_const).continuousOn, h, fun g _ g' _ => by
        have h2 : act g (chiC χ j g') = chiC χ j g' := act_algebraMap ha g _
        simp only [chiC_mul, map_mul, map_sub, h2, RingAut.mul_apply]
        ring⟩
  have h0 := (GlobalTheory.T.tate_invariants_cyclotomic_twist l act χ ha hχ K s hs j
    ((l : PadicComplex l) ^ (1 + s + padicValInt l j) * β - γ) (fun g hg => by
      have := e g hg
      simp only [map_sub, map_mul, map_pow, map_natCast] at this ⊢
      linear_combination this)).1 hj
  rw [sub_eq_zero.1 h0]
  exact hγ

theorem norm_le_of_log {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} {χ : GQ l →* ℚ_[l]ˣ}
    (ha : IsActC act) (hχ : IsCyc χ) (K : FinExt l) {s : ℕ} (hs : Lev l s)
    (α : Om l) (hα : α ∈ Ks K s) (β : PadicComplex l)
    (h : ∀ σ ∈ Gj K s, ‖algebraMap ℚ_[l] (PadicComplex l) (logZl l (χ σ : ℚ_[l])) *
      (α : PadicComplex l) + (act σ β - β)‖ ≤ 1) :
    ‖α‖ ≤ (l : ℝ) ^ (1 + s) := by
  obtain ⟨hn, hc, -⟩ := GlobalTheory.Cyc.cyc_basic l χ hχ
  obtain ⟨H1, H2⟩ := GlobalTheory.T.cocycle_eq_log_cyclotomic_smul_add_coboundary l act χ ha hχ K s hs
  obtain ⟨_, ⟨α', hα', rfl⟩, hn', b, e⟩ := H1 (fun σ =>
    algebraMap ℚ_[l] (PadicComplex l) (logZl l (χ σ : ℚ_[l])) * (α : PadicComplex l) + (act σ β - β))
    ⟨(((continuous_algMap.comp ((GlobalTheory.PadicLogUnits.logZl_hom l).2.1.comp_continuous hc hn)).mul
      continuous_const).add ((GlobalTheory.Cyc.IsActC.continuous_orbit l act ha β).sub
        continuous_const)).continuousOn, h, fun g hg g' _ => by
        have h2 := act_algebraMap ha g (logZl l (χ g' : ℚ_[l]))
        have h3 := act_inC ha hg (y := (α : PadicComplex l)) ⟨α, hα, rfl⟩
        simp only [map_mul χ, Units.val_mul, (GlobalTheory.PadicLogUnits.logZl_hom l).1 _ _ (hn g) (hn g'),
          map_add, map_mul, map_sub, h2, h3, RingAut.mul_apply]
        ring⟩
  have h0 := H2 ((α - α' : Om l) : PadicComplex l) ⟨α - α', sub_mem hα hα', rfl⟩ (b - β)
    (fun σ hσ => by
      have := e σ hσ
      simp only [map_sub, UniformSpace.Completion.coe_sub] at this ⊢
      linear_combination this)
  rw [UniformSpace.Completion.coe_sub, sub_eq_zero] at h0
  rw [← PadicComplex.norm_extends, h0]
  exact hn'

theorem sum_val (e : ℕ) : ∑ i ∈ Finset.range e, (padicValInt l ((i : ℤ) - e)) =
    padicValNat l e.factorial := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Finset.sum_range_succ', Nat.factorial_succ,
      padicValNat.mul (Nat.succ_ne_zero e) e.factorial_ne_zero, ← ih,
      add_comm (padicValNat l (e + 1))]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => ?_) ?_
    · congr 1
      push_cast
      ring
    · simp only [padicValInt]
      congr 1

variable {P : LocPrime l} {AI : LocAinf l P}

theorem om_mem (x : Om l) : algebraMap (Om l) P.R.BdR x ∈ (P.PD (botExt l)).Fil 0 := by
  obtain ⟨K, hK⟩ : ∃ K : FinExt l, x ∈ K.1 := ⟨⟨IntermediateField.adjoin ℚ_[l] {x},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)⟩,
    IntermediateField.mem_adjoin_simple_self _ _⟩
  have h2 := ((P.PD K).Fil 0).smul_mem (⟨x, hK⟩ : ↥K.1) (P.PD K).one_mem
  rw [Algebra.smul_def, mul_one] at h2
  rw [← SetLike.mem_coe, P.PD_Fil (botExt l) K 0]
  exact h2

theorem q_mem (x : ℚ_[l]) : algebraMap ℚ_[l] P.R.BdR x ∈ (P.PD (botExt l)).Fil 0 := by
  rw [IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR]
  exact om_mem _

theorem theta_q (J : ThetaL P AI) (x : ℚ_[l]) :
    J.θ (algebraMap ℚ_[l] P.R.BdR x) = algebraMap ℚ_[l] (PadicComplex l) x := by
  rw [IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR, J.θ_Om, algebraMap_eq]

theorem theta_sub (J : ThetaL P AI) {x y : P.R.BdR} (hx : x ∈ (P.PD (botExt l)).Fil 0)
    (hy : y ∈ (P.PD (botExt l)).Fil 0) : J.θ (x - y) = J.θ x - J.θ y := by
  rw [eq_sub_iff_add_eq, ← J.θ_add _ (sub_mem hx hy) _ hy, sub_add_cancel]

theorem pow_mem_bottomFiltration_zero {x : P.R.BdR} (hx : x ∈ (P.PD (botExt l)).Fil 0) (n : ℕ) :
    x ^ n ∈ (P.PD (botExt l)).Fil 0 := by simpa using pow_mem_Fil hx n

theorem theta_pow' (J : ThetaL P AI) {x : P.R.BdR} (hx : x ∈ (P.PD (botExt l)).Fil 0) (n : ℕ) :
    J.θ (x ^ n) = J.θ x ^ n := by
  induction n with
  | zero => simpa using J.θ_one
  | succ k ih => rw [pow_succ, J.θ_mul _ (pow_mem_bottomFiltration_zero hx k) _ hx, ih, pow_succ]

theorem act_mem (σ : GQ l) {a : ℤ} {x : P.R.BdR} (hx : x ∈ (P.PD (botExt l)).Fil a) :
    P.actQdR σ x ∈ (P.PD (botExt l)).Fil a := by
  rw [← P.PD_actdR (botExt l) ⟨σ, mem_GK_bot σ⟩]
  exact (P.PD (botExt l)).Fil_G _ _ _ hx

theorem act_ι (σ : GQ l) (b : P.R.B) : P.actQdR σ (P.ιB b) = P.ιB (P.actQ σ b) := by
  have h3 := (P.PD (botExt l)).ι_comm ⟨σ, mem_GK_bot σ⟩ b
  rw [P.PD_ι, P.PD_ι, P.PD_actB, P.PD_actdR] at h3
  exact h3.symm

theorem actQdR_periodT_eq_cyclotomic_bottom (σ : GQ l) :
    P.actQdR σ (P.ιB P.tB) = algebraMap ℚ_[l] P.R.BdR (P.χQ σ : ℚ_[l]) * P.ιB P.tB := by
  have h := (P.PD (botExt l)).t_act ⟨σ, mem_GK_bot σ⟩
  rw [P.PD_actB, P.PD_χ, P.period_datum_t_eq] at h
  rw [act_ι, h, map_smul, Algebra.smul_def]

theorem fil_mono {a : ℤ} (n : ℕ) : (P.PD (botExt l)).Fil (a + n) ≤ (P.PD (botExt l)).Fil a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, ← add_assoc]
    exact ((P.PD (botExt l)).Fil_anti _).trans ih

theorem fil_mono' {a b : ℤ} (h : a ≤ b) : (P.PD (botExt l)).Fil b ≤ (P.PD (botExt l)).Fil a := by
  obtain ⟨n, rfl⟩ := Int.le.dest h
  exact fil_mono n

theorem t_mem : P.ιB P.tB ∈ (P.PD (botExt l)).Fil 1 := by
  have t1 := (P.PD (botExt l)).mem_filtration_one
  rwa [P.PD_ι, P.period_datum_t_eq] at t1

theorem inclusion_ainf_padicInteger_eq_algebraMap (T : LocTied l P AI) (z : ℤ_[l]) :
    P.ιB (AI.ιA (Per.zA l z)) = algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l]) := by
  have : AI.ιA (Per.zA l z) = algebraMap ℚ_[l] P.R.B (z : ℚ_[l]) := by
    apply T.eB.injective
    rw [T.ιA, T.zB]; exact (GlobalTheory.RingIface.zB_eq_aB_zA l z).symm
  rw [this, AlgHom.commutes]

theorem theta_onto (T : LocTied l P AI) (y : PadicComplex l) (hy : ‖y‖ ≤ 1) :
    ∃ a : Ainf l, (GlobalTheory.ThetaTie.thetaL T).θ (P.ιB (AI.ιA a)) = y := by
  obtain ⟨a, ha⟩ := ReciprocityTheory.PGsh.Ainf.theta_surj l (OC l) (PadicComplexInt.integers l)
    ⟨y, (GlobalTheory.RingBasics.mem_OC _).2 hy⟩
  refine ⟨a, ?_⟩
  change GlobalTheory.ThetaTie.th T _ = _
  rw [GlobalTheory.ThetaTie.th_eq T (GlobalTheory.ThetaTie.eD_ιA T a).symm, (GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l).2.2.2.1]
  exact congrArg Subtype.val ha

theorem graded (T : LocTied l P AI) (J : ThetaL P AI) (i : ℕ) {u : P.R.BdR}
    (hu : u ∈ (P.PD (botExt l)).Fil 0) (a : Ainf l)
    (h : P.ιB P.tB ^ i * u - P.ιB (AI.ιA a) ∈ (P.PD (botExt l)).Fil ((i : ℤ) + 1)) :
    ‖(((AI.ζ 1 : OC l) : PadicComplex l) - 1) ^ i * J.θ u‖ ≤ 1 := by
  obtain ⟨w, hw, ht, hθ⟩ := exists_t_eq T J
  have h1 : P.ιB P.tB ^ i * u ∈ (P.PD (botExt l)).Fil i := by
    rw [mul_comm]
    exact mul_mem_zero hu (by simpa using pow_mem_Fil (t_mem (P := P)) i)
  have h2 : P.ιB (AI.ιA a) ∈ (P.PD (botExt l)).Fil i := by
    simpa using sub_mem h1 ((P.PD (botExt l)).Fil_anti _ h)
  obtain ⟨a', rfl⟩ := (mem_Fil_iff T J i a).1 h2
  have h3 := mul_mem_zero (pow_mem_bottomFiltration_zero hw i) h
  rw [add_comm] at h3
  obtain ⟨y, hy, e⟩ := exists_t_pow J 1 i _ h3
  have hunit : IsUnit (P.ιB P.tB) := by
    have := (P.PD (botExt l)).t_unit.map P.ιB
    rwa [P.period_datum_t_eq] at this
  have e' : w ^ i * u - P.ιB (AI.ιA a') = y := by
    refine (hunit.pow i).mul_left_cancel ?_
    rw [← e, map_mul, map_mul, map_pow, map_pow, ht]
    ring
  have hm := mul_mem_zero (pow_mem_bottomFiltration_zero hw i) hu
  have h4 := (J.θ_ker _ (sub_mem hm (AI.ainf_image_mem_filtration_zero _ a'))).2 (e' ▸ hy)
  rw [theta_sub J hm (AI.ainf_image_mem_filtration_zero _ a'), J.θ_mul _ (pow_mem_bottomFiltration_zero hw i) _ hu, theta_pow' J hw, hθ,
    sub_eq_zero] at h4
  rw [h4]
  exact J.θ_int _

def cob (P : LocPrime l) (e : ℕ) (b : P.R.BdR) (σ : GQ l) : P.R.BdR :=
  algebraMap ℚ_[l] P.R.BdR ((P.χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * P.actQdR σ b - b

theorem twistedCoboundary_t_pow_mul (e i : ℕ) (y : P.R.BdR) (σ : GQ l) : cob P e (P.ιB P.tB ^ i * y) σ =
    P.ιB P.tB ^ i * (algebraMap ℚ_[l] P.R.BdR ((P.χQ σ ^ ((i : ℤ) - e) : ℚ_[l]ˣ) : ℚ_[l]) *
      P.actQdR σ y - y) := by
  rw [cob, map_mul, map_pow, actQdR_periodT_eq_cyclotomic_bottom, sub_eq_add_neg (i : ℤ), zpow_add, zpow_natCast, Units.val_mul,
    Units.val_pow_eq_pow_val, map_mul, map_pow]
  ring

theorem cob_ι (T : LocTied l P AI) (e : ℕ) (a : Ainf l) (σ : GQ l) :
    ∃ a', cob P e (P.ιB (AI.ιA a)) σ = P.ιB (AI.ιA a') := by
  have hn : ‖((P.χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l])‖ ≤ 1 := by
    rw [Units.val_zpow_eq_zpow_val, norm_zpow, (GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc).1, one_zpow]
  obtain ⟨z, hz⟩ : ∃ z : ℤ_[l], (z : ℚ_[l]) = ((P.χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) :=
    ⟨⟨_, hn⟩, rfl⟩
  refine ⟨Per.zA l z * AI.actW σ a - a, ?_⟩
  rw [map_sub, map_sub, map_mul, map_mul, inclusion_ainf_padicInteger_eq_algebraMap T, hz, cob, act_ι, ← AI.ιA_act]
  rfl

theorem zeta_mem (K : FinExt l) {s : ℕ} (hs : 1 ≤ s) : P.ζQ 1 ∈ Ks K s := by
  apply (show _ ≤ Ks K s from le_sup_right)
  apply IntermediateField.subset_adjoin
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hs
  have : P.ζQ 1 ^ l = 1 := by rw [← P.ζQ_zero]; exact P.ζQ_succ 0
  simp [pow_add, pow_mul, this]

theorem act_zeta (K : FinExt l) {s : ℕ} (hs : 1 ≤ s) {σ : GQ l} (hσ : σ ∈ Gj K s) :
    AI.actC σ ((AI.ζ 1 : OC l) : PadicComplex l) = ((AI.ζ 1 : OC l) : PadicComplex l) :=
  act_inC ⟨AI.actC_ext, AI.actC_norm⟩ hσ ⟨_, zeta_mem K hs, (AI.ζ_eq 1).symm⟩

def IntMod (AI : LocAinf l P) (G : Subgroup (GQ l)) (e i : ℕ) (R : GQ l → P.R.BdR) : Prop :=
  ∃ b ∈ (P.PD (botExt l)).Fil (i : ℤ), ∀ σ ∈ G, ∃ a : Ainf l,
    R σ + cob P e b σ - P.ιB (AI.ιA a) ∈ (P.PD (botExt l)).Fil ((e : ℤ) + 1)

theorem step (T : LocTied l P AI) (K : FinExt l) {s : ℕ} (hs : Lev l s) {e i : ℕ} (hi : i < e)
    (R : GQ l → P.R.BdR) (hR : ∀ σ, R σ ∈ (P.PD (botExt l)).Fil (e : ℤ))
    (h : IntMod AI (Gj K s) e i R) :
    IntMod AI (Gj K s) e (i + 1)
      (fun σ => (l : P.R.BdR) ^ (1 + s + padicValInt l ((i : ℤ) - e)) * R σ) := by
  set J := GlobalTheory.ThetaTie.thetaL T
  set n := 1 + s + padicValInt l ((i : ℤ) - e) with hn
  obtain ⟨b, hb, H⟩ := h
  obtain ⟨y, hy, rfl⟩ := exists_t_pow J 0 i b (by rwa [zero_add])
  have hl : (l : P.R.BdR) ^ n = P.ιB (AI.ιA ((l : Ainf l) ^ n)) := by simp
  have hl0 : (l : P.R.BdR) ^ n ∈ (P.PD (botExt l)).Fil 0 := hl ▸ AI.ainf_image_mem_filtration_zero _ _
  have hlθ : J.θ ((l : P.R.BdR) ^ n) = (l : PadicComplex l) ^ n := by
    have := theta_q J ((l : ℚ_[l]) ^ n)
    simpa using this
  have key := norm_le_of_twist (act := AI.actC) ⟨AI.actC_ext, AI.actC_norm⟩ P.χQ_cyc K hs
    (j := (i : ℤ) - e) (by omega) ((((AI.ζ 1 : OC l) : PadicComplex l) - 1) ^ i * J.θ y)
    (fun σ hσ => by
      obtain ⟨a, ha⟩ := H σ hσ
      have h1 := sub_mem (fil_mono' (show (i : ℤ) + 1 ≤ e + 1 by omega) ha)
        (fil_mono' (show (i : ℤ) + 1 ≤ e by omega) (hR σ))
      have hm := mul_mem_zero (q_mem ((P.χQ σ ^ ((i : ℤ) - e) : ℚ_[l]ˣ) : ℚ_[l])) (act_mem σ hy)
      have h2 := graded T J i (sub_mem hm hy) a (by
        rw [← twistedCoboundary_t_pow_mul]; convert h1 using 1; ring)
      rw [theta_sub J hm hy, J.θ_mul _ (q_mem _) _ (act_mem σ hy), theta_q, J.θ_act _ _ hy] at h2
      rw [map_mul, map_pow, map_sub, map_one, act_zeta K hs.1 hσ, chiC]
      convert h2 using 2
      ring)
  obtain ⟨a0, ha0⟩ := theta_onto T _ key
  obtain ⟨w, hw, ht, hθ⟩ := exists_t_eq T J
  refine ⟨(l : P.R.BdR) ^ n * (P.ιB P.tB ^ i * y) - P.ιB (AI.ιA (AI.ξ ^ i * a0)), ?_, fun σ hσ => ?_⟩
  · have hm := mul_mem_zero hl0 (mul_mem_zero (pow_mem_bottomFiltration_zero hw i) hy)
    have h1 := (J.θ_ker _ (sub_mem hm (AI.ainf_image_mem_filtration_zero _ a0))).1 (by
      rw [theta_sub J hm (AI.ainf_image_mem_filtration_zero _ a0), J.θ_mul _ hl0 _ (mul_mem_zero (pow_mem_bottomFiltration_zero hw i) hy),
        J.θ_mul _ (pow_mem_bottomFiltration_zero hw i) _ hy, theta_pow' J hw, hθ, hlθ, ha0, sub_self])
    have h2 := (P.PD (botExt l)).Fil_mul _ _ _ _ ((mem_Fil_iff T J i _).2 dvd_rfl) h1
    rw [Nat.cast_succ]
    convert h2 using 1
    rw [ht, map_mul, map_mul, map_pow, map_pow]
    ring
  · obtain ⟨a, ha⟩ := H σ hσ
    obtain ⟨a', ha'⟩ := cob_ι T e (AI.ξ ^ i * a0) σ
    refine ⟨(l : Ainf l) ^ n * a - a', ?_⟩
    convert mul_mem_zero hl0 ha using 1
    rw [map_sub, map_sub, ← ha', map_mul _ ((l : Ainf l) ^ n), map_mul P.ιB (AI.ιA _), ← hl]
    simp only [cob, map_sub, map_mul (P.actQdR σ) ((l : P.R.BdR) ^ n), map_pow, map_natCast]
    ring

theorem iterate (T : LocTied l P AI) (K : FinExt l) {s : ℕ} (hs : Lev l s) {e : ℕ}
    (R : GQ l → P.R.BdR) (hR : ∀ σ, R σ ∈ (P.PD (botExt l)).Fil (e : ℤ))
    (h : IntMod AI (Gj K s) e 0 R) (i : ℕ) (hi : i ≤ e) :
    IntMod AI (Gj K s) e i (fun σ => (l : P.R.BdR) ^
      (∑ k ∈ Finset.range i, (1 + s + padicValInt l ((k : ℤ) - e))) * R σ) := by
  induction i with
  | zero => simpa using h
  | succ i ih =>
    have := step T K hs (show i < e from hi) _ (fun σ => mul_mem_zero (pow_mem_bottomFiltration_zero (by
      simpa using q_mem (P := P) (l : ℚ_[l])) _) (hR σ)) (ih (by omega))
    convert this using 2
    rw [Finset.sum_range_succ, pow_add]
    ring

theorem logChi_coe (LT : LocTheory) (g : GQ l) :
    ((logChi LT g : ℤ_[l]) : ℚ_[l]) = logZl l ((LT l).χQ g : ℚ_[l]) := by
  have h := (GlobalTheory.PadicLogUnits.logZl_hom l).2.2.1 _ ((cyc_basic l _ (LT l).χQ_cyc).1 g)
  exact congrArg Subtype.val (dif_pos h : logChi LT g = ⟨_, h⟩)

theorem norm_zeta : ‖P.ζQ 1 - 1‖ = (l : ℝ) ^ (-(1 : ℝ) / ((l : ℝ) - 1)) := by
  have h2 : P.ζQ 1 ^ l = 1 := by rw [← P.ζQ_zero]; exact P.ζQ_succ 0
  have h3 : IsPrimitiveRoot (P.ζQ 1) l := isPrimitiveRoot_of_mem_nthRootsFinset Fact.out
    ((Polynomial.mem_nthRootsFinset (Fact.out : l.Prime).pos _).2 h2) P.ζQ_one
  have h4 : IsPrimitiveRoot ((P.ζQ 1 : Om l) : PadicComplex l) l :=
    h3.map_of_injective (f := algebraMap (Om l) (PadicComplex l)) (RingHom.injective _)
  have := GlobalTheory.Cyc.norm_primitiveRoot_sub_one l 1 le_rfl _ (by rwa [pow_one])
  rw [← PadicComplex.norm_extends, UniformSpace.Completion.coe_sub, UniformSpace.Completion.coe_one,
    this]
  simp

theorem norm_le_of_intMod (T : LocTied l P AI) (K : FinExt l) {s : ℕ} (hs : Lev l s) (e : ℕ)
    (α : Om l) (hα : α ∈ Ks K s)
    (H : IntMod AI (Gj K s) e 0 (fun σ => algebraMap ℚ_[l] P.R.BdR (logZl l (P.χQ σ : ℚ_[l])) *
      (algebraMap (Om l) P.R.BdR α * P.ιB P.tB ^ e))) :
    ‖α‖ ≤ (l : ℝ) ^ (((e * (s + 1) + padicValNat l e.factorial + 1 + s : ℕ) : ℝ) +
      (e : ℝ) / ((l : ℝ) - 1)) := by
  set J := GlobalTheory.ThetaTie.thetaL T
  have hG := iterate T K hs (e := e) (fun σ => algebraMap ℚ_[l] P.R.BdR (logZl l (P.χQ σ : ℚ_[l])) *
    (algebraMap (Om l) P.R.BdR α * P.ιB P.tB ^ e))
    (fun σ => mul_mem_zero (q_mem _) (mul_mem_zero (om_mem _)
      (by simpa using pow_mem_Fil (t_mem (P := P)) e)))
    H e le_rfl
  have hsum : ∑ k ∈ Finset.range e, (1 + s + padicValInt l ((k : ℤ) - e)) =
      e * (s + 1) + padicValNat l e.factorial := by
    rw [Finset.sum_add_distrib, sum_val, Finset.sum_const, Finset.card_range, smul_eq_mul,
      add_comm 1 s]
  rw [hsum] at hG
  generalize e * (s + 1) + padicValNat l e.factorial = n at hG ⊢
  obtain ⟨c, hc, H2⟩ := hG
  obtain ⟨y, hy, rfl⟩ := exists_t_pow J 0 e c (by rwa [zero_add])
  have key := norm_le_of_log (act := AI.actC) ⟨AI.actC_ext, AI.actC_norm⟩ P.χQ_cyc K hs
    ((P.ζQ 1 - 1) ^ e * ((l : Om l) ^ n * α))
    (mul_mem (pow_mem (sub_mem (zeta_mem K hs.1) (one_mem _)) _)
      (mul_mem (pow_mem (natCast_mem _ l) _) hα))
    ((((AI.ζ 1 : OC l) : PadicComplex l) - 1) ^ e * J.θ y)
    (fun σ hσ => by
      obtain ⟨a, ha⟩ := H2 σ hσ
      have hm := mul_mem_zero (q_mem (P := P) (logZl l (P.χQ σ : ℚ_[l])))
        (om_mem ((l : Om l) ^ n * α))
      have hm2 := sub_mem (act_mem σ hy) hy
      have h2 := graded T J e (add_mem hm hm2) a (by
        rw [twistedCoboundary_t_pow_mul] at ha
        convert ha using 1
        simp only [sub_self, zpow_zero, Units.val_one, map_one, map_mul, map_pow, map_natCast]
        ring)
      rw [J.θ_add _ hm _ hm2, theta_sub J (act_mem σ hy) hy, J.θ_mul _ (q_mem _) _ (om_mem _),
        theta_q, J.θ_Om, J.θ_act _ _ hy] at h2
      rw [map_mul, map_pow, map_sub, map_one, act_zeta K hs.1 hσ]
      convert h2 using 2
      rw [AI.ζ_eq]
      have e1 : (((P.ζQ 1 - 1) ^ e * ((l : Om l) ^ n * α) : Om l) : PadicComplex l) =
          (((P.ζQ 1 : Om l) : PadicComplex l) - 1) ^ e *
            (((l : Om l) ^ n * α : Om l) : PadicComplex l) := by
        have e0 : ∀ x : Om l, (x : PadicComplex l) = algebraMap (Om l) (PadicComplex l) x :=
          fun _ => rfl
        rw [e0, e0, e0, map_mul, map_pow, map_sub, map_one]
      rw [e1]
      ring)
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hnl : ‖(l : Om l) ^ n‖ = (l : ℝ) ^ (-(n : ℝ)) := by
    rw [← map_natCast (algebraMap ℚ_[l] (Om l)), ← map_pow, PadicAlgCl.norm_extends,
      Padic.norm_p_pow, ← Real.rpow_intCast]
    simp
  rw [norm_mul, norm_mul, norm_pow, norm_zeta, hnl, ← Real.rpow_natCast, ← Real.rpow_mul hl.le,
    ← mul_assoc, ← Real.rpow_add hl, ← le_div_iff₀' (Real.rpow_pos_of_pos hl _),
    ← Real.rpow_natCast, ← Real.rpow_sub hl] at key
  refine key.trans (le_of_eq ?_)
  congr 1
  push_cast
  ring

theorem norm_expStar_le : ∀ (D : Formalism.BasicNotions.D7) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ), Lev l s → ∀ e : ℕ, ∀ (z : GQ l → ℚ_[l]) (α : Om l), α ∈ Ks K s → ExpStar D.loc (Gj K s) e z α → (∃ b ∈ ((D.loc l).PD (botExt l)).Fil 0, ∀ σ ∈ Gj K s, ∃ a : Ainf l, algebraMap ℚ_[l] (D.loc l).R.BdR (z σ) - (algebraMap ℚ_[l] (D.loc l).R.BdR (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * (D.loc l).actQdR σ b - b) - (D.loc l).ιB ((D.locA l).ιA a) ∈ ((D.loc l).PD (botExt l)).Fil ((e : ℤ) + 1)) → ‖α‖ ≤ (l : ℝ) ^ (((e * (s + 1) + padicValNat l e.factorial + 1 + s : ℕ) : ℝ) + (e : ℝ) / ((l : ℝ) - 1)) := by
  rintro D l _ K s hs e z α hα ⟨-, b1, hb1, H1⟩ ⟨b, hb, H⟩
  simp only [logChi_coe] at H1
  refine norm_le_of_intMod (D.locT l) K hs e α hα ⟨b1 - b, sub_mem hb1 hb, fun σ hσ => ?_⟩
  obtain ⟨a, ha⟩ := H σ hσ
  refine ⟨a, ?_⟩
  convert sub_mem ha (H1 σ hσ) using 1
  simp only [cob, map_sub]
  ring

end GlobalTheory.Cyc.ExpBound
