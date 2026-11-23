import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOrbitPadicComplex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormUnitPowSubOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFontaineThetaOnAinfStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFilQuotientXiPowerAinfStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateInvariantsCyclotomicTwistStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTwistCocycleCoboundaryStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1BallCocycleLogCyclotomicStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyThetaOnBdRPlusPeriodDataStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

noncomputable section

namespace GlobalTheory.ExpDef

open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc Filter Topology

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l}

section Orbit
variable (AI : LocAinf l P)

theorem orbit_one (a : Ainf l) : ∀ᶠ g in 𝓝 (1 : GQ l),
    AI.actW g a - a ∈ Ideal.span {((l : ℕ) : Ainf l)} ⊔ Ideal.span {AI.ξ} := by
  obtain ⟨θ, -, hs, he, hk, -⟩ := GlobalTheory.T.exists_fontaineTheta_on_Ainf l P AI
  have hc := GlobalTheory.Cyc.IsActC.continuous_orbit l AI.actC ⟨AI.actC_ext, AI.actC_norm⟩ (θ a : OC l)
  have hl : 0 < ‖(l : PadicComplex l)‖ := norm_pos_iff.2 GlobalTheory.RingBasics.p_ne_zero
  have h1 := Metric.tendsto_nhds.1 (hc.tendsto 1) _ hl
  filter_upwards [h1] with g hg
  rw [dist_eq_norm, map_one, RingAut.one_apply, ← he] at hg
  have h2 := (GlobalTheory.RingBasics.mem_span_pow_OC 1 (θ (AI.actW g a) - θ a)).2 (by
    rw [pow_one]
    exact_mod_cast hg.le)
  rw [pow_one, Ideal.mem_span_singleton'] at h2
  obtain ⟨c, hc⟩ := h2
  obtain ⟨b, rfl⟩ := hs c
  obtain ⟨d, hd⟩ := (hk (AI.actW g a - a - b * l)).1 (by
    rw [map_sub, map_sub, map_mul, map_natCast, hc, sub_self])
  have : AI.actW g a - a = b * l + AI.ξ * d := by rw [← hd]; ring
  rw [this]
  exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
    (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))

theorem orbit_teich (n k : ℕ) (x : OCb l) : ∀ᶠ g in 𝓝 (1 : GQ l),
    AI.actW g (WittVector.teichmuller l x) - WittVector.teichmuller l x ∈
      Ideal.span {((l : ℕ) : Ainf l) ^ k} ⊔ Ideal.span {AI.ξ ^ n} := by
  obtain ⟨y, rfl⟩ : ∃ y, y ^ l ^ (k + n) = x := (bijective_iterateFrobenius (OCb l) l (k + n)).2 x
  filter_upwards [orbit_one AI (WittVector.teichmuller l y)] with g hg
  have h := SModEq.sub_mem.1 ((SModEq.sub_mem.2 hg).pow_pow_add_one
    (Ideal.mem_sup_left (Ideal.mem_span_singleton_self ((l : ℕ) : Ainf l))) (k + n))
  rw [map_pow, map_pow, ← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow]
  exact Ideal.sup_pow_add_le_pow_sup_pow (Ideal.pow_le_pow_right (Nat.le_succ _) h)

theorem orbit (n k : ℕ) (a : Ainf l) : ∀ᶠ g in 𝓝 (1 : GQ l),
    ∃ b c : Ainf l, AI.actW g a - a = (l : Ainf l) ^ k * b + AI.ξ ^ n * c := by
  induction k generalizing a with
  | zero => exact Eventually.of_forall fun g => ⟨AI.actW g a - a, 0, by simp⟩
  | succ k ih =>
    have h := (WittVector.mem_span_p_iff_coeff_zero_eq_zero
      (a - WittVector.teichmuller l (a.coeff 0))).2 (by
        rw [← WittVector.constantCoeff_apply, map_sub]
        simp)
    obtain ⟨a', ha⟩ := Ideal.mem_span_singleton'.1 h
    filter_upwards [ih a', orbit_teich AI n (k + 1) (a.coeff 0)] with g ⟨b, c, h1⟩ h2
    obtain ⟨_, hu, _, hv, h3⟩ := Submodule.mem_sup.1 h2
    obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 hu
    obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton'.1 hv
    have h4 := congrArg (AI.actW g) ha
    rw [map_mul, map_natCast, map_sub] at h4
    exact ⟨b + u, l * c + v, by linear_combination ha - h4 + (l : Ainf l) * h1 - h3⟩

end Orbit

section Filt

abbrev Fl (P : LocPrime l) (a : ℤ) := (P.PD (botExt l)).Fil a

abbrev tt (P : LocPrime l) : P.R.BdR := P.ιB P.tB

abbrev qB (P : LocPrime l) : ℚ_[l] →+* P.R.BdR := algebraMap ℚ_[l] P.R.BdR

abbrev qC (l : ℕ) [Fact l.Prime] : ℚ_[l] →+* PadicComplex l := algebraMap ℚ_[l] (PadicComplex l)

theorem om_mem (x : Om l) : algebraMap (Om l) P.R.BdR x ∈ Fl P 0 := by
  obtain ⟨K, hK⟩ : ∃ K : FinExt l, x ∈ K.1 := ⟨⟨IntermediateField.adjoin ℚ_[l] {x},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)⟩,
    IntermediateField.mem_adjoin_simple_self _ x⟩
  have h := ((P.PD K).Fil 0).smul_mem ⟨x, hK⟩ (P.PD K).one_mem
  rw [Algebra.smul_def, mul_one] at h
  have h2 := P.PD_Fil K (botExt l) 0
  change _ ∈ ((Fl P 0 : Submodule _ _) : Set P.R.BdR)
  rw [← h2]
  exact h

theorem q_eq (c : ℚ_[l]) : qB P c = algebraMap (Om l) P.R.BdR (algebraMap ℚ_[l] (Om l) c) :=
  IsScalarTower.algebraMap_apply _ _ _ _

theorem q_mem (c : ℚ_[l]) : qB P c ∈ Fl P 0 := q_eq (P := P) c ▸ om_mem _

theorem mul_mem_deRhamPeriodFiltration_of_mem_zero {a : ℤ} {x y : P.R.BdR} (hx : x ∈ Fl P 0) (hy : y ∈ Fl P a) : x * y ∈ Fl P a := by
  simpa using (P.PD (botExt l)).Fil_mul _ _ _ _ hx hy

theorem pow_mem_bottomFiltration_zero {x : P.R.BdR} (hx : x ∈ Fl P 0) (n : ℕ) : x ^ n ∈ Fl P 0 := by
  induction n with
  | zero => simpa using (P.PD (botExt l)).one_mem
  | succ n ih => rw [pow_succ]; exact mul_mem_deRhamPeriodFiltration_of_mem_zero ih hx

theorem act_mem {a : ℤ} (g : GQ l) {x : P.R.BdR} (hx : x ∈ Fl P a) : P.actQdR g x ∈ Fl P a := by
  have := (P.PD (botExt l)).Fil_G ⟨g, mem_GK_bot g⟩ a x hx
  rwa [P.PD_actdR] at this

theorem act_ι (g : GQ l) (b : P.R.B) : P.actQdR g (P.ιB b) = P.ιB (P.actQ g b) := by
  have h3 := (P.PD (botExt l)).ι_comm ⟨g, mem_GK_bot g⟩ b
  rw [P.PD_ι, P.PD_ι, P.PD_actB, P.PD_actdR] at h3
  exact h3.symm

theorem actQdR_periodT_eq_cyclotomic_bottom (g : GQ l) : P.actQdR g (tt P) = qB P (P.χQ g) * tt P := by
  have h := (P.PD (botExt l)).t_act ⟨g, mem_GK_bot g⟩
  rw [P.PD_actB, P.period_datum_t_eq, P.PD_χ] at h
  rw [act_ι, h, map_smul, Algebra.smul_def]

theorem t_unit : IsUnit (tt P) := by
  have hu := (P.PD (botExt l)).t_unit
  rw [P.period_datum_t_eq] at hu
  exact hu.map P.ιB

theorem fl_anti {a : ℤ} (n : ℕ) {x : P.R.BdR} (hx : x ∈ Fl P (a + n)) : x ∈ Fl P a := by
  induction n with
  | zero => simpa using hx
  | succ n ih => exact ih ((P.PD (botExt l)).Fil_anti _ (by simpa [add_assoc] using hx))

variable {AI : LocAinf l P} (J : ThetaL P AI)
include J

theorem fl_pow (a : ℤ) (n : ℕ) (x : P.R.BdR) :
    x ∈ Fl P (a + n) ↔ ∃ y ∈ Fl P a, x = tt P ^ n * y := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, ← add_assoc, J.fil_succ_iff_mul_t]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, hz, rfl⟩ := (ih y).1 hy
      exact ⟨z, hz, by ring⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨_, (ih _).2 ⟨y, hy, rfl⟩, by ring⟩

theorem fl_succ (n : ℕ) {y : P.R.BdR} (hy : y ∈ Fl P 0) :
    tt P ^ n * y ∈ Fl P ((n : ℤ) + 1) ↔ J.θ y = 0 := by
  rw [add_comm, fl_pow J, J.θ_ker y hy]
  constructor
  · rintro ⟨z, hz, e⟩
    rwa [(t_unit.pow n).mul_left_cancel e]
  · exact fun h => ⟨y, h, rfl⟩

theorem th_sub {x y : P.R.BdR} (hx : x ∈ Fl P 0) (hy : y ∈ Fl P 0) : J.θ (x - y) = J.θ x - J.θ y := by
  have := J.θ_add _ (sub_mem hx hy) _ hy
  rw [sub_add_cancel] at this
  rw [this, add_sub_cancel_right]

theorem th_q (c : ℚ_[l]) {x : P.R.BdR} (hx : x ∈ Fl P 0) : J.θ (qB P c * x) = qC l c * J.θ x := by
  rw [J.θ_mul _ (q_mem c) _ hx, q_eq, J.θ_Om]
  congr 1

theorem th_pow {x : P.R.BdR} (hx : x ∈ Fl P 0) (n : ℕ) : J.θ (x ^ n) = J.θ x ^ n := by
  induction n with
  | zero => simpa using J.θ_one
  | succ n ih => rw [pow_succ, pow_succ, J.θ_mul _ (pow_mem_bottomFiltration_zero hx n) _ hx, ih]

end Filt

section Small
variable (AI : LocAinf l P)

def Small (n k : ℕ) (x : P.R.BdR) : Prop :=
  ∃ a : Ainf l, x - (l : P.R.BdR) ^ k * P.ιB (AI.ιA a) ∈ Fl P n

variable {AI}

theorem Small.add {n k : ℕ} {x y : P.R.BdR} (hx : Small AI n k x) (hy : Small AI n k y) :
    Small AI n k (x + y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  refine ⟨a + b, ?_⟩
  convert add_mem ha hb using 1
  rw [map_add, map_add]; ring

theorem Small.sub {n k : ℕ} {x y : P.R.BdR} (hx : Small AI n k x) (hy : Small AI n k y) :
    Small AI n k (x - y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  refine ⟨a - b, ?_⟩
  convert sub_mem ha hb using 1
  rw [map_sub, map_sub]; ring

theorem Small.mul {n k : ℕ} {x : P.R.BdR} (hx : Small AI n k x) (c : Ainf l) :
    Small AI n k (x * P.ιB (AI.ιA c)) := by
  obtain ⟨a, ha⟩ := hx
  refine ⟨a * c, ?_⟩
  convert mul_mem_deRhamPeriodFiltration_of_mem_zero (AI.ainf_image_mem_filtration_zero _ c) ha using 1
  rw [map_mul, map_mul]; ring

theorem div_l {a : ℤ} (m : ℕ) {x : P.R.BdR} (h : (l : P.R.BdR) ^ m * x ∈ Fl P a) : x ∈ Fl P a := by
  have hl : ((l : ℕ) : ℚ_[l]) ^ m ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  convert mul_mem_deRhamPeriodFiltration_of_mem_zero (q_mem (((l : ℕ) : ℚ_[l]) ^ m)⁻¹) h using 1
  rw [← mul_assoc, ← map_natCast (qB P), ← map_pow, ← map_mul, inv_mul_cancel₀ hl, map_one, one_mul]

theorem Small.div {n k : ℕ} (m : ℕ) {x : P.R.BdR} (hx : Small AI n (m + k) ((l : P.R.BdR) ^ m * x)) :
    Small AI n k x := by
  obtain ⟨a, ha⟩ := hx
  refine ⟨a, div_l m ?_⟩
  convert ha using 1
  ring

variable (T : LocTied l P AI)
include T

open scoped Formalism.Per in
theorem q_int {c : ℚ_[l]} (hc : ‖c‖ ≤ 1) : ∃ a, P.ιB (AI.ιA a) = qB P c := by
  have h : algebraMap ℚ_[l] P.R.B ((⟨c, hc⟩ : ℤ_[l]) : ℚ_[l]) = AI.ιA (Per.zA l ⟨c, hc⟩) :=
    T.eB.injective (((T.zB _).trans (GlobalTheory.RingIface.zB_eq_aB_zA l _)).trans (T.ιA _).symm)
  exact ⟨_, by rw [← h, AlgHom.commutes]⟩

theorem small_q (n k : ℕ) {c : ℚ_[l]} (hc : ‖c‖ ≤ ‖(l : ℚ_[l]) ^ k‖) : Small AI n k (qB P c) := by
  have hl : ((l : ℕ) : ℚ_[l]) ^ k ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have h : ‖c / (l : ℚ_[l]) ^ k‖ ≤ 1 := by
    rw [norm_div]; exact div_le_one_of_le₀ hc (norm_nonneg _)
  obtain ⟨a, ha⟩ := q_int T h
  refine ⟨a, ?_⟩
  rw [ha, ← map_natCast (qB P), ← map_pow, ← map_mul, mul_div_cancel₀ _ hl, sub_self]
  exact zero_mem _

theorem small_tendsto {X : Type} {F : Filter X} {c : X → ℚ_[l]} (hc : Tendsto c F (𝓝 0)) (n k : ℕ) :
    ∀ᶠ x in F, Small AI n k (qB P (c x)) := by
  have hl : ((l : ℕ) : ℚ_[l]) ^ k ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  filter_upwards [Metric.tendsto_nhds.1 hc _ (norm_pos_iff.2 hl)] with x hx
  exact small_q T n k (by simpa using hx.le)

variable (J : ThetaL P AI)
include J

theorem small_cob (u : GQ l → ℚ_[l]) (hu : Tendsto u (𝓝 1) (𝓝 1)) (hu1 : ∀ g, ‖u g‖ ≤ 1) (n k : ℕ)
    {b : P.R.BdR} (hb : b ∈ Fl P 0) :
    ∀ᶠ g in 𝓝 (1 : GQ l), Small AI n k (qB P (u g) * P.actQdR g b - b) := by
  obtain ⟨h1, h2, -⟩ := GlobalTheory.T.deRham_fil_quotient_xi_power_ainf l P AI T J n
  obtain ⟨m, a, ha⟩ := h1 b hb
  have hu' : Tendsto (fun g => u g - 1) (𝓝 1) (𝓝 0) := by simpa using hu.sub_const 1
  filter_upwards [small_tendsto T hu' n (m + k), orbit AI n (m + k) a] with g h3 ⟨x, y, h4⟩
  refine Small.div m ?_
  have h5 : Small AI n (m + k) (P.actQdR g (P.ιB (AI.ιA a)) - P.ιB (AI.ιA a)) := by
    refine ⟨x, ?_⟩
    have h6 := congrArg (fun w => P.ιB (AI.ιA w)) h4
    simp only [map_sub, map_add, map_mul, map_pow, map_natCast] at h6
    rw [act_ι, ← AI.ιA_act]
    have h7 := (h2 (AI.ξ ^ n * y)).2 (dvd_mul_right _ _)
    simp only [map_mul, map_pow] at h7
    convert h7 using 1
    exact sub_eq_of_eq_add' h6
  obtain ⟨a', ha'⟩ := q_int T (hu1 g)
  have h6 := h5.mul a'
  rw [ha'] at h6
  obtain ⟨w, hw⟩ := h6.add (h3.mul a)
  refine ⟨w, ?_⟩
  convert add_mem hw (sub_mem (mul_mem_deRhamPeriodFiltration_of_mem_zero (q_mem (u g)) (act_mem g ha)) ha) using 1
  simp only [map_sub, map_mul, map_pow, map_natCast, map_one]
  ring

theorem norm_of_small (i k : ℕ) {y : P.R.BdR} (hy : y ∈ Fl P 0)
    (h : Small AI (i + 1) k (tt P ^ i * y)) :
    ‖J.θ y‖ * ‖((AI.ζ 1 : OC l) : PadicComplex l) - 1‖ ^ i ≤ ‖(l : PadicComplex l)‖ ^ k := by
  obtain ⟨-, h2, w, hw, e, hθ⟩ := GlobalTheory.T.deRham_fil_quotient_xi_power_ainf l P AI T J i
  obtain ⟨a, ha⟩ := h
  have h3 : tt P ^ i * y ∈ Fl P i := by simpa using (fl_pow J 0 i _).2 ⟨y, hy, rfl⟩
  have h4 : (l : P.R.BdR) ^ k * P.ιB (AI.ιA a) ∈ Fl P i := by
    have := sub_mem h3 (fl_anti 1 (by simpa using ha))
    rwa [sub_sub_cancel] at this
  obtain ⟨a, rfl⟩ := (h2 a).1 (div_l k h4)
  have hA := AI.ainf_image_mem_filtration_zero (botExt l) a
  have h5 := (fl_succ J i (sub_mem (mul_mem_deRhamPeriodFiltration_of_mem_zero hy (pow_mem_bottomFiltration_zero hw i))
      (mul_mem_deRhamPeriodFiltration_of_mem_zero (q_mem ((l : ℚ_[l]) ^ k)) hA))).1 (by
    have h6 := mul_mem_deRhamPeriodFiltration_of_mem_zero (pow_mem_bottomFiltration_zero hw i) ha
    rw [Nat.cast_succ] at h6
    convert h6 using 1
    simp only [map_mul, map_pow, map_natCast, tt]
    rw [e]; ring)
  rw [th_sub J (mul_mem_deRhamPeriodFiltration_of_mem_zero hy (pow_mem_bottomFiltration_zero hw i)) (mul_mem_deRhamPeriodFiltration_of_mem_zero (q_mem _) hA), th_q J _ hA,
    J.θ_mul _ hy _ (pow_mem_bottomFiltration_zero hw i), th_pow J hw, hθ, sub_eq_zero, map_pow, map_natCast] at h5
  rw [← norm_pow, ← norm_mul, h5, norm_mul, norm_pow]
  exact mul_le_of_le_one_right (by positivity) (J.θ_int a)

end Small

section Coh

theorem cont_of_one {G : Subgroup (GQ l)} {A : GQ l → PadicComplex l → PadicComplex l}
    (hA : ∀ g x, ‖A g x‖ = ‖x‖) {f : GQ l → PadicComplex l}
    (hf : ∀ g ∈ G, ∀ h ∈ G, f (g * h) = f g + A g (f h)) (h1 : Tendsto f (𝓝[G] 1) (𝓝 0)) :
    ContinuousOn f G := by
  intro g hg
  have h2 : Tendsto (fun σ => g⁻¹ * σ) (𝓝[G] g) (𝓝[G] 1) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := (continuous_const_mul g⁻¹).tendsto g
      rw [inv_mul_cancel] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ hσ using G.mul_mem (G.inv_mem hg) hσ
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  refine (tendsto_zero_iff_norm_tendsto_zero.1 (h1.comp h2)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  have := hf g hg _ (G.mul_mem (G.inv_mem hg) hσ)
  rw [mul_inv_cancel_left] at this
  rw [this, add_sub_cancel_left, hA]
  rfl

theorem exists_scale (K : FinExt l) (s : ℕ) {f : GQ l → PadicComplex l} (hf : ContinuousOn f (Gj K s)) :
    ∃ m : ℕ, ∀ g ∈ Gj K s, ‖(l : PadicComplex l) ^ m * f g‖ ≤ 1 := by
  have hc : IsCompact (Gj K s : Set (GQ l)) := (InfiniteGalois.fixingSubgroup_isClosed _).isCompact
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn hf
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (GlobalTheory.RingBasics.norm_p_lt (p := l))).mul_const C
  rw [zero_mul] at ht
  obtain ⟨m, hm⟩ := (ht.eventually (gt_mem_nhds one_pos)).exists
  refine ⟨m, fun g hg => ?_⟩
  rw [norm_mul, norm_pow]
  exact (mul_le_mul_of_nonneg_left (hC g hg) (by positivity)).trans hm.le

variable {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} {χ : GQ l →* ℚ_[l]ˣ}
  (ha : IsActC act) (hχ : IsCyc χ) (K : FinExt l) {s : ℕ} (hs : Lev l s)
include ha hχ hs

theorem H1_twist_vanishes {j : ℤ} (hj : j ≠ 0) {f : GQ l → PadicComplex l}
    (hf : CocOn (Gj K s) (fun g y => chiC χ j g * act g y) Set.univ f) :
    ∃ b, ∀ g ∈ Gj K s, f g = chiC χ j g * act g b - b := by
  obtain ⟨m, hm⟩ := exists_scale K s hf.1
  obtain ⟨x, -, hx⟩ := GlobalTheory.T.cyclotomic_twist_cocycle_coboundary l act χ ha hχ K s hs j hj (fun g => (l : PadicComplex l) ^ m * f g)
    ⟨continuousOn_const.mul hf.1, hm, fun g hg h hh => by
      simp only [hf.2.2 g hg h hh, map_mul, map_pow, map_natCast]; ring⟩
  have hl : (l : PadicComplex l) ≠ 0 := GlobalTheory.RingBasics.p_ne_zero
  refine ⟨x / l ^ (1 + s + padicValInt l j + m), fun g hg => ?_⟩
  have := hx g hg
  simp only [map_div₀, map_pow, map_natCast] at this ⊢
  rw [← mul_div_assoc, ← sub_div, ← this]
  field_simp
  ring

theorem H1_spanned_by_log_cyclotomic {f : GQ l → PadicComplex l} (hf : CocOn (Gj K s) (fun g y => act g y) Set.univ f) :
    ∃ α ∈ Ks K s, ∃ b, ∀ g ∈ Gj K s,
      f g = qC l (logZl l (χ g : ℚ_[l])) * ((α : Om l) : PadicComplex l) + (act g b - b) := by
  obtain ⟨m, hm⟩ := exists_scale K s hf.1
  obtain ⟨_, ⟨α, hα, rfl⟩, -, x, hx⟩ := (GlobalTheory.T.cocycle_eq_log_cyclotomic_smul_add_coboundary l act χ ha hχ K s hs).1
    (fun g => (l : PadicComplex l) ^ m * f g)
    ⟨continuousOn_const.mul hf.1, hm, fun g hg h hh => by
      simp only [hf.2.2 g hg h hh, map_mul, map_pow, map_natCast]; ring⟩
  have hl : (l : PadicComplex l) ^ m ≠ 0 := pow_ne_zero _ GlobalTheory.RingBasics.p_ne_zero
  refine ⟨α / l ^ m, div_mem hα (pow_mem (natCast_mem _ _) _), x / l ^ m, fun g hg => ?_⟩
  have := hx g hg
  have e : ((α / l ^ m : Om l) : PadicComplex l) = (α : PadicComplex l) / l ^ m := by
    change algebraMap (Om l) (PadicComplex l) (α / l ^ m) = algebraMap (Om l) (PadicComplex l) _ / _
    rw [map_div₀, map_pow, map_natCast (algebraMap (Om l) (PadicComplex l))]
  simp only [map_div₀, map_pow, map_natCast, e] at this ⊢
  rw [← mul_div_assoc, ← sub_div, ← add_div, ← this, mul_div_cancel_left₀ _ hl]

end Coh

section Main

variable {AI : LocAinf l P} (T : LocTied l P AI) (J : ThetaL P AI) (K : FinExt l) {s : ℕ} (hs : Lev l s)

abbrev cB (P : LocPrime l) (j : ℤ) (σ : GQ l) : P.R.BdR := qB P ((P.χQ σ ^ j : ℚ_[l]ˣ) : ℚ_[l])

theorem tw_act (e i : ℕ) (σ : GQ l) (y : P.R.BdR) :
    cB P (-(e : ℤ)) σ * P.actQdR σ (tt P ^ i * y) = tt P ^ i * (cB P (i - e) σ * P.actQdR σ y) := by
  rw [map_mul, map_pow, actQdR_periodT_eq_cyclotomic_bottom, cB, cB, sub_eq_add_neg, zpow_add, zpow_natCast, Units.val_mul,
    Units.val_pow_eq_pow_val, map_mul, map_pow]
  ring

include J in
theorem th_tw (j : ℤ) (σ : GQ l) {y : P.R.BdR} (hy : y ∈ Fl P 0) :
    J.θ (cB P j σ * P.actQdR σ y) = chiC P.χQ j σ * AI.actC σ (J.θ y) := by
  rw [th_q J _ (act_mem σ hy), J.θ_act σ y hy]
  rfl

include T in

theorem graded {e : ℕ} {z : GQ l → ℚ_[l]}
    (hz : CocOn (Gj K s) (fun σ y => ((P.χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * y) Set.univ z)
    (i : ℕ) {b : P.R.BdR} (hb : b ∈ Fl P 0)
    (h : ∀ σ ∈ Gj K s, qB P (z σ) - (cB P (-(e : ℤ)) σ * P.actQdR σ b - b) ∈ Fl P i) :
    ∃ y : GQ l → P.R.BdR, (∀ σ ∈ Gj K s, y σ ∈ Fl P 0 ∧
      qB P (z σ) - (cB P (-(e : ℤ)) σ * P.actQdR σ b - b) = tt P ^ i * y σ) ∧
      CocOn (Gj K s) (fun g x => chiC P.χQ (i - e) g * AI.actC g x) Set.univ (fun σ => J.θ (y σ)) := by
  obtain ⟨hn, hc, -⟩ := GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc
  have h0 := fun σ hσ => (fl_pow J 0 i _).1 (by simpa using h σ hσ)
  choose! y hy hy' using h0
  have hcoc : ∀ g ∈ Gj K s, ∀ h ∈ Gj K s,
      J.θ (y (g * h)) = J.θ (y g) + chiC P.χQ (i - e) g * AI.actC g (J.θ (y h)) := by
    intro g hg h hh
    rw [← th_tw J _ _ (hy h hh), ← J.θ_add _ (hy g hg) _ (mul_mem_deRhamPeriodFiltration_of_mem_zero (q_mem _) (act_mem g (hy h hh)))]
    congr 1
    refine (t_unit.pow i).mul_left_cancel ?_
    rw [mul_add, ← tw_act, ← hy' _ hg, ← hy' _ hh, ← hy' _ (mul_mem hg hh), hz.2.2 g hg h hh]
    simp only [cB, map_mul, map_add, map_sub, mul_zpow, Units.val_mul, AlgEquiv.commutes,
      AlgEquiv.mul_apply]
    ring
  refine ⟨y, fun σ hσ => ⟨hy σ hσ, hy' σ hσ⟩, cont_of_one
    (A := fun g x => chiC P.χQ (i - e) g * AI.actC g x) (fun g x => ?_) hcoc ?_, fun _ _ => trivial, hcoc⟩
  · rw [norm_mul, AI.actC_norm, chiC, Units.val_zpow_eq_zpow_val, map_zpow₀, norm_zpow, norm_algebraMap',
      hn, one_zpow, one_mul]
  · have hz1 : z 1 = 0 := by simpa using hz.2.2 1 (one_mem _) 1 (one_mem _)
    have hz0 : Tendsto z (𝓝[Gj K s] 1) (𝓝 0) := hz1 ▸ hz.1 1 (one_mem _)
    have hu : Tendsto (fun σ => ((P.χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l])) (𝓝 1) (𝓝 1) := by
      simp only [Units.val_zpow_eq_zpow_val]
      simpa using (hc.zpow₀ (-(e : ℤ)) fun g => Or.inl (Units.ne_zero _)).tendsto 1
    have hρ : 0 < ‖((AI.ζ 1 : OC l) : PadicComplex l) - 1‖ ^ i :=
      pow_pos (norm_pos_iff.2 (sub_ne_zero.2 fun h => AI.ζ_one (Subtype.ext h))) i
    refine Metric.tendsto_nhds.2 fun ε hε => ?_
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (mul_pos hε hρ) (GlobalTheory.RingBasics.norm_p_lt (p := l))
    filter_upwards [self_mem_nhdsWithin, small_tendsto T hz0 (i + 1) k, nhdsWithin_le_nhds
      (small_cob T J _ hu (fun g => by rw [Units.val_zpow_eq_zpow_val, norm_zpow, hn, one_zpow])
        (i + 1) k hb)] with σ hσ h1 h2
    have h3 := h1.sub h2
    rw [hy' σ hσ] at h3
    rw [dist_zero_right]
    exact lt_of_mul_lt_mul_right ((norm_of_small T J i k (hy σ hσ) h3).trans_lt hk) hρ.le

include T J hs in
theorem descend {e : ℕ} {z : GQ l → ℚ_[l]}
    (hz : CocOn (Gj K s) (fun σ y => ((P.χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * y) Set.univ z)
    (i : ℕ) (hi : i ≤ e) : ∃ b ∈ Fl P 0,
      ∀ σ ∈ Gj K s, qB P (z σ) - (cB P (-(e : ℤ)) σ * P.actQdR σ b - b) ∈ Fl P i := by
  induction i with
  | zero => exact ⟨0, zero_mem _, fun σ _ => by simpa using q_mem _⟩
  | succ i ih =>
    obtain ⟨b, hb, h⟩ := ih (by omega)
    obtain ⟨y, hy, hc⟩ := graded T J K hz i hb h
    obtain ⟨β, hβ⟩ := H1_twist_vanishes ⟨AI.actC_ext, AI.actC_norm⟩ P.χQ_cyc K hs (by omega) hc
    obtain ⟨x, hx, rfl⟩ := J.θ_onto β
    refine ⟨b + tt P ^ i * x, add_mem hb (fl_anti i ((fl_pow J 0 i _).2 ⟨x, hx, rfl⟩)), fun σ hσ => ?_⟩
    have h1 := mul_mem_deRhamPeriodFiltration_of_mem_zero (q_mem ((P.χQ σ ^ ((i : ℤ) - e) : ℚ_[l]ˣ) : ℚ_[l])) (act_mem σ hx)
    have h2 := (fl_succ J i (sub_mem (hy σ hσ).1 (sub_mem h1 hx))).2 (by
      rw [th_sub J (hy σ hσ).1 (sub_mem h1 hx), th_sub J h1 hx, th_tw J _ _ hx, sub_eq_zero]
      exact hβ σ hσ)
    rw [Nat.cast_succ]
    convert h2 using 1
    rw [map_add, mul_add, tw_act, mul_sub, ← (hy σ hσ).2]
    ring

include T J hs in
theorem exists_exp {e : ℕ} {z : GQ l → ℚ_[l]}
    (hz : CocOn (Gj K s) (fun σ y => ((P.χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * y) Set.univ z) :
    ∃ α ∈ Ks K s, ∃ b ∈ Fl P 0, ∀ σ ∈ Gj K s,
      qB P (z σ) - qB P (logZl l (P.χQ σ)) * (algebraMap (Om l) P.R.BdR α * tt P ^ e) -
        (cB P (-(e : ℤ)) σ * P.actQdR σ b - b) ∈ Fl P ((e : ℤ) + 1) := by
  obtain ⟨b, hb, h⟩ := descend T J K hs hz e le_rfl
  obtain ⟨y, hy, hc⟩ := graded T J K hz e hb h
  obtain ⟨α, hα, β, hβ⟩ := H1_spanned_by_log_cyclotomic ⟨AI.actC_ext, AI.actC_norm⟩ P.χQ_cyc K hs (by simpa [chiC] using hc)
  obtain ⟨x, hx, rfl⟩ := J.θ_onto β
  refine ⟨α, hα, b + tt P ^ e * x, add_mem hb (fl_anti e ((fl_pow J 0 e _).2 ⟨x, hx, rfl⟩)),
    fun σ hσ => ?_⟩
  have h1 := act_mem σ hx
  have h3 := mul_mem_deRhamPeriodFiltration_of_mem_zero (q_mem (logZl l (P.χQ σ))) (om_mem (P := P) α)
  have h2 := (fl_succ J e (sub_mem (sub_mem (hy σ hσ).1 h3) (sub_mem h1 hx))).2 (by
    rw [th_sub J (sub_mem (hy σ hσ).1 h3) (sub_mem h1 hx), th_sub J h1 hx, th_sub J (hy σ hσ).1 h3,
      th_q J _ (om_mem α), J.θ_Om, J.θ_act σ x hx, hβ σ hσ]
    ring)
  convert h2 using 1
  rw [map_add, mul_add, tw_act, mul_sub, mul_sub, ← (hy σ hσ).2, sub_self]
  simp only [cB, zpow_zero, Units.val_one, map_one]
  ring

include J hs in
theorem eq_zero_of_cob {e : ℕ} {α : Om l} (hα : α ∈ Ks K s) {b : P.R.BdR} (hb : b ∈ Fl P 0)
    (h : ∀ σ ∈ Gj K s, qB P (logZl l (P.χQ σ)) * (algebraMap (Om l) P.R.BdR α * tt P ^ e) -
        (cB P (-(e : ℤ)) σ * P.actQdR σ b - b) ∈ Fl P ((e : ℤ) + 1)) : α = 0 := by
  have h3 := fun σ => mul_mem_deRhamPeriodFiltration_of_mem_zero (q_mem (logZl l (P.χQ σ))) (om_mem (P := P) α)
  have key : ∀ i : ℕ, i ≤ e → ∃ y ∈ Fl P 0, b = tt P ^ i * y := by
    intro i hi
    induction i with
    | zero => exact ⟨b, hb, by simp⟩
    | succ i ih =>
      obtain ⟨y, hy, rfl⟩ := ih (by omega)
      obtain ⟨d, rfl⟩ : ∃ d, e = i + 1 + d := Nat.exists_eq_add_of_le hi
      have h0 : J.θ y = 0 := by
        refine (GlobalTheory.T.tate_invariants_cyclotomic_twist l AI.actC P.χQ ⟨AI.actC_ext, AI.actC_norm⟩ P.χQ_cyc K s hs
          ((i : ℤ) - (i + 1 + d : ℕ)) _ fun σ hσ => ?_).1 (by omega)
        have h1 := mul_mem_deRhamPeriodFiltration_of_mem_zero (q_mem ((P.χQ σ ^ ((i : ℤ) - (i + 1 + d : ℕ)) : ℚ_[l]ˣ) : ℚ_[l])) (act_mem σ hy)
        rw [← th_tw J _ _ hy, ← sub_eq_zero, ← th_sub J h1 hy, ← fl_succ J i (sub_mem h1 hy)]
        have h4 := (fl_pow J 0 (i + 1 + d) _).2 ⟨_, h3 σ, rfl⟩
        have h5 := sub_mem (fl_anti (a := i + 1) d (by simpa using h4))
          (fl_anti (a := i + 1) (d + 1) (by convert h σ hσ using 2; push_cast; ring))
        convert h5 using 1
        rw [mul_sub, ← tw_act]
        ring
      have := (fl_succ J i hy).2 h0
      exact (fl_pow J 0 (i + 1) _).1 (by simpa using this)
  obtain ⟨y, hy, rfl⟩ := key e le_rfl
  have := (GlobalTheory.T.cocycle_eq_log_cyclotomic_smul_add_coboundary l AI.actC P.χQ ⟨AI.actC_ext, AI.actC_norm⟩ P.χQ_cyc K s hs).2 α ⟨α, hα, rfl⟩
    (J.θ y) fun σ hσ => by
      have h1 := act_mem σ hy
      rw [← J.θ_Om, ← th_q J _ (om_mem α), ← J.θ_act σ y hy, ← th_sub J h1 hy, ← sub_eq_zero,
        ← th_sub J (h3 σ) (sub_mem h1 hy), ← fl_succ J e (sub_mem (h3 σ) (sub_mem h1 hy))]
      convert h σ hσ using 1
      rw [tw_act, sub_self]
      simp only [cB, zpow_zero, Units.val_one, map_one]
      ring
  exact (algebraMap (Om l) (PadicComplex l)).injective (this.trans (map_zero _).symm)

end Main

theorem logChi_eq (LT : LocTheory) (σ : GQ l) :
    ((logChi LT σ : ℤ_[l]) : ℚ_[l]) = logZl l ((LT l).χQ σ) := by
  exact congrArg Subtype.val (dif_pos ((GlobalTheory.PadicLogUnits.logZl_hom l).2.2.1 _
    ((GlobalTheory.Cyc.cyc_basic l _ (LT l).χQ_cyc).1 σ)))

theorem expStar_existsUnique : ∀ (D : Formalism.BasicNotions.D7) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ), Lev l s → ∀ e : ℕ, (∀ z : GQ l → ℚ_[l], CocOn (Gj K s) (fun σ y => (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * y) Set.univ z → ∃ α ∈ Ks K s, ExpStar D.loc (Gj K s) e z α) ∧ ∀ (z : GQ l → ℚ_[l]) (α α' : Om l), α ∈ Ks K s → α' ∈ Ks K s → ExpStar D.loc (Gj K s) e z α → ExpStar D.loc (Gj K s) e z α' → α = α' := by
  intro D l _ K s hs e
  obtain ⟨J⟩ := GlobalTheory.T.nonempty_thetaOnBdRPlus_periodData D l
  constructor
  · intro z hz
    obtain ⟨α, hα, b, hb, h⟩ := exists_exp (D.locT l) J K hs hz
    exact ⟨α, hα, hz, b, hb, fun σ hσ => by rw [logChi_eq]; exact h σ hσ⟩
  · rintro z α α' hα hα' ⟨-, b, hb, h⟩ ⟨-, b', hb', h'⟩
    refine sub_eq_zero.1 (eq_zero_of_cob (e := e) J K hs (sub_mem hα hα') (sub_mem hb' hb) fun σ hσ => ?_)
    convert sub_mem (h' σ hσ) (h σ hσ) using 1
    simp only [logChi_eq, map_sub, cB, qB, tt]
    ring

end GlobalTheory.ExpDef
