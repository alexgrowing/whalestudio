import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CyclotomicFrobeniusPowerSeriesXEqMulQuotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersCompleteDVR
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocPrimeVNormalised
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueEv

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL.Ser

open PowerSeries

section Algebra

theorem one_add_X_mul_derivative_binomial {l : ℕ} [Fact l.Prime] (L : Type) [Field L] [CharZero L]
    [Algebra ℤ_[l] L] (c : ℤ_[l]) :
    (1 + X) * d⁄dX L (binomialSeries L c) = C (algebraMap ℤ_[l] L c) * binomialSeries L c := by
  have hc : ∀ (f : L⟦X⟧) (n : ℕ),
      coeff n ((1 + X) * d⁄dX L f) = coeff (n + 1) f * (n + 1) + coeff n f * n := by
    intro f n
    rw [add_mul, one_mul, map_add, coeff_derivative]
    cases n with
    | zero => simp
    | succ n => rw [coeff_succ_X_mul, coeff_derivative]; simp
  ext n
  rw [hc, coeff_C_mul]
  simp only [binomialSeries_coeff, ← Algebra.algebraMap_eq_smul_one]
  have h1 := Ring.descPochhammer_eq_factorial_smul_choose c (n + 1)
  rw [descPochhammer_succ_right, Polynomial.smeval_mul, Ring.descPochhammer_eq_factorial_smul_choose] at h1
  simp only [Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_natCast, pow_one, pow_zero,
    nsmul_eq_mul, mul_one, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h1
  have h2 := congrArg (algebraMap ℤ_[l] L) h1
  simp only [map_mul, map_sub, map_add, map_natCast, map_one] at h2
  have h0 : (n.factorial : L) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  apply mul_left_cancel₀ h0
  linear_combination -h2

theorem derivative_rescale_exp (L : Type) [Field L] [Algebra ℚ L] (a : L) :
    d⁄dX L (rescale a (exp L)) = C a * rescale a (exp L) := by
  ext n
  have h := congrArg (coeff n) (derivative_exp L)
  rw [coeff_derivative] at h
  rw [coeff_derivative, coeff_C_mul, coeff_rescale, coeff_rescale, ← h]
  ring

theorem ode_unique {L : Type} [Field L] [CharZero L] (a : L) {f g : L⟦X⟧} (hf : d⁄dX L f = C a * f)
    (hg : d⁄dX L g = C a * g) (h0 : constantCoeff f = constantCoeff g) : f = g := by
  ext n
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    have h1 := congrArg (coeff n) hf
    have h2 := congrArg (coeff n) hg
    rw [coeff_derivative, coeff_C_mul] at h1 h2
    have h3 : ((n : L) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    apply mul_right_cancel₀ h3
    rw [h1, h2, ih]

theorem constantCoeff_rescale_exp (L : Type) [Field L] [Algebra ℚ L] (a : L) :
    constantCoeff (rescale a (exp L)) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale]; simp

variable {l : ℕ} [Fact l.Prime] {O L : Type} [CommRing O] [Field L] [CharZero L] [Algebra ℚ L] [Algebra ℤ_[l] O]
  [Algebra ℤ_[l] L] [Algebra O L] [IsScalarTower ℤ_[l] O L]

theorem map_binomial_of_exp (f : O⟦X⟧ →ₐ[O] L⟦X⟧) (m : L) (hf : f X = rescale m (exp L) - 1) (w : ℤ_[l]) :
    f (binomialSeries O w) = rescale (m * algebraMap ℤ_[l] L w) (exp L) := by
  have h0 : constantCoeff (rescale m (exp L) - 1) = 0 := by
    rw [map_sub, constantCoeff_rescale_exp, map_one, sub_self]
  have hs : HasSubst (rescale m (exp L) - 1) := HasSubst.of_constantCoeff_zero' h0
  let g : L⟦X⟧ →ₐ[L] L⟦X⟧ := substAlgHom hs
  have gX : g X = rescale m (exp L) - 1 := substAlgHom_X hs
  have gC : ∀ r : L, g (C r) = C r := fun r => g.commutes r
  have e : ∀ a, g a = subst (rescale m (exp L) - 1) a := fun a => congrFun (coe_substAlgHom hs) a
  have hfg : (f : O⟦X⟧ →+* L⟦X⟧) = (g : L⟦X⟧ →+* L⟦X⟧).comp (PowerSeries.map (algebraMap O L)) := by
    refine GlobalTheory.Fon.ps_hom_ext (fun r => ?_) ?_ ?_
    · change f (C r) = g (PowerSeries.map (algebraMap O L) (C r))
      rw [map_C, gC]
      rw [← PowerSeries.algebraMap_apply, ← f.commutes]
      rfl
    · change f X = g (PowerSeries.map (algebraMap O L) X)
      rw [map_X, gX, hf]
    · refine GlobalTheory.Fon.eq_zero_of_pow_dvd ?_
      change constantCoeff (f X) = 0
      rw [hf, h0]
  have h1 : f (binomialSeries O w) = g (binomialSeries L w) := by
    have := RingHom.congr_fun hfg (binomialSeries O w)
    rw [← GlobalTheory.Fon.map_binomialSeries (algebraMap O L)
      (fun z => (IsScalarTower.algebraMap_apply ℤ_[l] O L z).symm) w]
    exact this
  rw [h1]
  refine ode_unique _ ?_ (derivative_rescale_exp L _) ?_
  · have h2 := congrArg g (one_add_X_mul_derivative_binomial L w)
    rw [map_mul, map_mul, map_add, map_one, gX, gC] at h2
    have h3 : d⁄dX L (g (binomialSeries L w)) =
        g (d⁄dX L (binomialSeries L w)) * (C m * rescale m (exp L)) := by
      rw [e, e, derivative_subst hs, map_sub, derivative_rescale_exp]; simp
    rw [h3, map_mul]
    linear_combination (C m) * h2
  · obtain ⟨b, hb⟩ : (X : L⟦X⟧) ∣ binomialSeries L w - 1 := X_dvd_iff.2 (by simp)
    rw [sub_eq_iff_eq_add.1 hb, map_add, map_mul, map_one, gX, map_add, map_mul, h0,
      constantCoeff_rescale_exp]
    simp

theorem map_gam_X (f : O⟦X⟧ →ₐ[O] L⟦X⟧) (ζ : L) (hf : f X = C ζ * exp L - 1) (j a : ℕ)
    (hζ : ζ ^ l ^ j = 1) (c : ℤ_[l]) (hc : (l : ℤ_[l]) ^ j ∣ c - a) :
    f (GlobalTheory.Fon.gam O c X) = C (ζ ^ a) * rescale (algebraMap ℤ_[l] L c) (exp L) - 1 := by
  obtain ⟨w, hw⟩ := hc
  have hnat : ∀ k : ℕ, f (binomialSeries O (k : ℤ_[l])) = C (ζ ^ k) * rescale (k : L) (exp L) := by
    intro k
    rw [binomialSeries_nat, map_pow, map_add, map_one, hf, add_sub_cancel, mul_pow, exp_pow_eq_rescale_exp,
      map_pow]
  have h1 := map_binomial_of_exp (f.comp (GlobalTheory.Fon.gam O ((l ^ j : ℕ) : ℤ_[l]))) ((l ^ j : ℕ) : L) (by
    rw [AlgHom.comp_apply, GlobalTheory.Fon.gam_X, map_sub, hnat, hζ, map_one, map_one, one_mul]) w
  rw [AlgHom.comp_apply, GlobalTheory.Fon.gam_binomialSeries] at h1
  have h2 : c = (a : ℤ_[l]) + ((l ^ j : ℕ) : ℤ_[l]) * w := by
    push_cast; linear_combination hw
  rw [GlobalTheory.Fon.gam_X, map_sub, map_one, h2, binomialSeries_add, map_mul, h1, hnat, mul_assoc,
    exp_mul_exp_eq_exp_add, map_add, map_mul, map_natCast, map_natCast]

end Algebra

section Generic

def EvLaw (l : ℕ) {O L : Type} [CommRing O] [Field L] (v : AddValuation L (WithTop ℚ))
    (_ : Algebra O L⟦X⟧) : Prop :=
  ∀ x : L⟦X⟧, (∃ j : ℕ, (constantCoeff x + 1) ^ l ^ j = 1) → (∃! ev : O⟦X⟧ →ₐ[O] L⟦X⟧, ev X = x) ∧
    ∀ ev : O⟦X⟧ →ₐ[O] L⟦X⟧, ev X = x → ∀ (a : O⟦X⟧) (k r : ℕ), ∃ m₀ : ℕ, ∀ m ≥ m₀, (r : WithTop ℚ) ≤
      v (coeff k (ev a) - coeff k (ev ((trunc m a : Polynomial O) : O⟦X⟧)))

variable {l : ℕ} [Fact l.Prime] {O L : Type} [CommRing O] [Field L] [CharZero L] [Algebra ℚ L] [Algebra ℤ_[l] O]
  [Algebra ℤ_[l] L] [Algebra O L] [IsScalarTower ℤ_[l] O L] {v : AddValuation L (WithTop ℚ)}

theorem ev_gam (H : EvLaw l (O := O) v inferInstance) {ζ : L} {j a : ℕ} (h : ζ ^ l ^ j = 1) (c : ℤ_[l])
    (hc : (l : ℤ_[l]) ^ j ∣ c - a) {f g : O⟦X⟧ →ₐ[O] L⟦X⟧} (hf : f X = C ζ * exp L - 1)
    (hg : g X = C (ζ ^ a) * exp L - 1) (b : O⟦X⟧) :
    f (GlobalTheory.Fon.gam O c b) = rescale (algebraMap ℤ_[l] L c) (g b) := by
  have h' : (ζ ^ a) ^ l ^ j = 1 := by rw [← pow_mul, mul_comm, pow_mul, h, one_pow]
  have hr : ∀ y : L⟦X⟧, rescaleAlgHom (algebraMap ℤ_[l] L c) y = rescale (algebraMap ℤ_[l] L c) y :=
    fun y => by simp [rescaleAlgHom, rescale_eq, MvPowerSeries.rescaleAlgHom_apply]
  have := (H (C (ζ ^ a) * rescale (algebraMap ℤ_[l] L c) (exp L) - 1) ⟨j, by
      rw [map_sub, map_mul, constantCoeff_rescale_exp, constantCoeff_C, mul_one, map_one, sub_add_cancel,
        h']⟩).1.unique (y₁ := f.comp (GlobalTheory.Fon.gam O c))
    (y₂ := ((rescaleAlgHom (algebraMap ℤ_[l] L c)).restrictScalars O).comp g)
    (map_gam_X f ζ hf j a h c hc) (by
      change rescaleAlgHom _ (g X) = _
      rw [hg, map_sub, map_mul, map_one, hr (exp L)]
      congr 2
      exact (rescaleAlgHom _).commutes _)
  exact (AlgHom.congr_fun this b).trans (hr _)

omit [Fact l.Prime] [CharZero L] [Algebra ℤ_[l] O] [Algebra ℤ_[l] L] [IsScalarTower ℤ_[l] O L] in

theorem exists_ev (H : EvLaw l (O := O) v inferInstance) : ∃ ev : L → (O⟦X⟧ →ₐ[O] L⟦X⟧),
    (∀ ζ, (∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) → ev ζ X = C ζ * exp L - 1) ∧
    (∀ ζ, ¬ (∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) → ev ζ = ev 1) ∧
    ∀ ζ, ∃ j : ℕ, (constantCoeff (ev ζ X) + 1) ^ l ^ j = 1 := by
  classical
  let z : L → L := fun ζ => if ∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j) then ζ else 1
  have hz : ∀ ζ, ∃ j : ℕ, (constantCoeff (C (z ζ) * exp L - 1) + 1) ^ l ^ j = 1 := by
    intro ζ
    rw [map_sub, map_mul, constantCoeff_exp, constantCoeff_C, mul_one, map_one, sub_add_cancel]
    by_cases h : ∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)
    · simp only [z, if_pos h]
      exact h.imp fun j hj => hj.pow_eq_one
    · simp [z, if_neg h]
  have hex : ∀ ζ : Set.range z, ∃ ev : O⟦X⟧ →ₐ[O] L⟦X⟧, ev X = C (ζ : L) * exp L - 1 := by
    rintro ⟨_, ζ, rfl⟩
    exact (H _ (hz ζ)).1.exists
  choose ev hev using hex
  refine ⟨fun ζ => ev ⟨z ζ, ζ, rfl⟩, fun ζ h => ?_, fun ζ h => ?_, fun ζ => ?_⟩
  · simp only [hev, z, if_pos h]
  · refine congrArg ev (Subtype.ext ?_)
    simp only [z, if_neg h, ite_self]
  · simp only [hev]; exact hz ζ

omit [CharZero L] [Algebra ℚ L] [Algebra ℤ_[l] L] in

theorem exists_primitive_pow {ζ : L} {j : ℕ} (h : IsPrimitiveRoot ζ (l ^ j)) (a : ℕ) :
    ∃ k : ℕ, IsPrimitiveRoot (ζ ^ a) (l ^ k) := by
  have h' : (ζ ^ a) ^ l ^ j = 1 := by rw [← pow_mul, mul_comm, pow_mul, h.pow_eq_one, one_pow]
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow (Fact.out : l.Prime)).1 (orderOf_dvd_of_pow_eq_one h')
  exact ⟨k, hk ▸ IsPrimitiveRoot.orderOf _⟩

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR}
    [Algebra Qp L] [TopologicalSpace L] {n s : ℕ}

theorem nonempty_wSer_of_evLaw [NeZero n] [IsHausdorff (Ideal.span {(l : O)}) O] (Γ : WGam PD L O v n s)
    (hp : PD.p = l) (c : Γ.Gam →* ℤ_[l]ˣ) (hc : ∀ g, algebraMap ℤ_[l] O (c g : ℤ_[l]) = (Γ.χΓ g : O))
    (hv : ∀ (c : ℤ_[l]) (j a : ℕ), (j : WithTop ℚ) ≤ v (algebraMap ℤ_[l] L c - (a : L)) →
      (l : ℤ_[l]) ^ j ∣ c - a) (H : EvLaw l (O := O) v inferInstance) : Nonempty (WSer Γ) := by
  have hc' : ∀ g, algebraMap O L (Γ.χΓ g : O) = algebraMap ℤ_[l] L (c g : ℤ_[l]) :=
    fun g => by rw [← hc, ← IsScalarTower.algebraMap_apply]
  obtain ⟨ev, hX, hjunk, hnorm⟩ := exists_ev H
  refine ⟨{
    φ₀ := GlobalTheory.Fon.phi0 l O
    q₀ := GlobalTheory.Fon.qq l O
    q₀_def := by rw [hp]; exact GlobalTheory.Fon.X_mul_qq _ _
    φ₀_X := GlobalTheory.Fon.cyclotomicFrobeniusPowerSeries_X_eq_mul_quotient _ _
    γ₀ := (GlobalTheory.Fon.gamHom O).comp ((Units.coeHom ℤ_[l]).comp c)
    γ₀_comm := fun g a => GlobalTheory.Fon.cyclotomicFrobenius_comm_gammaAction _ _ a
    γ₀_X := fun g => ⟨GlobalTheory.Fon.constantCoeff_gam_X _ _, (GlobalTheory.Fon.coeff_one_gam_X _ _).trans (hc g)⟩
    EE := GlobalTheory.Fon.EE l O n
    eeAlgA := GlobalTheory.Fon.algEE l O n
    eeTow := GlobalTheory.Fon.towEE l O n
    EE_inj := GlobalTheory.Fon.EE_inj _ _ _
    EE_π := GlobalTheory.Fon.EE_isUnit_π _ _ _
    EE_complete := by rw [hp]; exact GlobalTheory.Fon.lComplete_EE _ _ _
    EE_dense := by rw [hp]; exact GlobalTheory.Fon.EE_dense _ _ _
    EE_sat := by rw [hp]; exact GlobalTheory.Fon.EE_sat _ _ _
    φE := GlobalTheory.Fon.phiEE _ _ _
    φE_ext := GlobalTheory.Fon.phiEE_ext _ _ _
    γE := (GlobalTheory.Fon.gamEE _ _).comp c
    γE_ext := fun g a => GlobalTheory.Fon.gamEE_ext _ _ (c g) a
    lev := fun i ζ => (ev ζ).comp (Pi.evalAlgHom O (fun _ => O⟦X⟧) i)
    lev_letter := fun i ζ a h => ?_
    lev_π := ?_
    lev_cont := fun i ζ a k r => (H _ (hnorm ζ)).2 (ev ζ) rfl (a i) k r
    lev_Γ := ?_
    lev_φ := ?_
    lev_junk := ?_ }⟩
  · change ev ζ (a i) = 0
    rw [h, map_zero]
  · rw [hp]
    intro i ζ h
    refine ⟨exp L, constantCoeff_exp, derivative_exp _, ?_⟩
    change 1 + ev ζ X = _
    rw [hX ζ h, add_sub_cancel]
  · rw [hp]
    rintro g i ζ _ j a h hj rfl f
    rw [hc'] at hj ⊢
    exact ev_gam H h.pow_eq_one _ (hv _ j a hj) (hX ζ ⟨j, h⟩) (hX _ (exists_primitive_pow h a)) (f i)
  · rw [hp]
    rintro i ζ ⟨j, h⟩ f
    have := ev_gam H h.pow_eq_one (l : ℤ_[l]) (a := l) (by simp) (hX ζ ⟨j, h⟩) (hX _ (exists_primitive_pow h l))
      (f (i - 1))
    rw [GlobalTheory.Fon.gam_l, map_natCast] at this
    exact this
  · rw [hp]
    intro i ζ h
    rw [hjunk ζ h]

end Generic

section Local

variable {l : ℕ} [Fact l.Prime] (LL : FinExt l)

theorem norm_sub_one_lt {ζ : Om l} {j : ℕ} (h : ζ ^ l ^ j = 1) : ‖ζ - 1‖ < 1 := by
  have hp : l.Prime := Fact.out
  have hn : l ^ j ≠ 0 := pow_ne_zero _ hp.ne_zero
  have h1 : ‖ζ‖ = 1 := by
    have := congrArg norm h
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 this
  let S : Subring (Om l) := (Valued.v : Valuation (Om l) NNReal).integer
  have hS : ∀ x : Om l, x ∈ S ↔ ‖x‖ ≤ 1 := fun x => by
    rw [Valuation.mem_integer_iff, PadicAlgCl.valuation_def, ← NNReal.coe_le_coe]; rfl
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp ((⟨ζ, (hS _).2 h1.le⟩ : S) - 1) 1 j
  have h2 := congrArg S.subtype hr
  simp only [map_add, map_mul, map_pow, map_sub, map_one, map_natCast, sub_add_cancel, one_pow, mul_one] at h2
  change ζ ^ l ^ j = (ζ - 1) ^ l ^ j + 1 + l * (ζ - 1) * (r : Om l) at h2
  have h3 : (ζ - 1) ^ l ^ j = -(l * (ζ - 1) * (r : Om l)) := by linear_combination h - h2
  have hl : ‖(l : Om l)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  have h4 : ‖ζ - 1‖ ≤ 1 := (hS _).1 (S.sub_mem ((hS _).2 h1.le) S.one_mem)
  have h5 : ‖ζ - 1‖ ^ l ^ j < 1 := by
    rw [← norm_pow, h3, norm_neg, norm_mul, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (by positivity)
      (mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hl h4) ((hS _).1 r.2)
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hn).1 h5

variable {LL}

theorem dvd_of_le_v (P : LocPrime l) (c : ℤ_[l]) (j a : ℕ)
    (h : (j : WithTop ℚ) ≤ P.v LL (algebraMap ℤ_[l] ↥LL.1 c - (a : ↥LL.1))) : (l : ℤ_[l]) ^ j ∣ c - a := by
  rw [← WithTop.coe_natCast, (NormVal.locPrime_v_normalised l P LL).2.1, ← map_natCast (algebraMap ℤ_[l] ↥LL.1),
    ← map_sub] at h
  change ‖algebraMap ℚ_[l] (Om l) ((c - a : ℤ_[l]) : ℚ_[l])‖ ≤ _ at h
  rw [PadicAlgCl.norm_extends] at h
  rw [← Ideal.mem_span_singleton, ← PadicInt.norm_le_pow_iff_mem_span_pow, PadicInt.norm_def]
  refine h.trans (le_of_eq ?_)
  rw [← Real.rpow_intCast]; simp

private theorem exists_integral_chi (P : LocPrime l) :
    ∃ χ : GQ l →* ℤ_[l]ˣ, ∀ g, (((χ g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) = (P.χQ g : ℚ_[l]) := by
  obtain ⟨hn, -, -⟩ := GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc
  let f : GQ l →* ℤ_[l] :=
    { toFun := fun g => ⟨(P.χQ g : ℚ_[l]), (hn g).le⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        change (P.χQ (a * b) : ℚ_[l]) = (P.χQ a : ℚ_[l]) * (P.χQ b : ℚ_[l])
        rw [map_mul, Units.val_mul]) }
  exact ⟨f.toHomUnits, fun g => rfl⟩

theorem exists_padic_char {P : LocPrime l} {K : FinExt l} {s : ℕ} (Γ : GamS P K s LL) :
    ∃ c : Γ.Gam →* ℤ_[l]ˣ, ∀ g, algebraMap ℤ_[l] ↥(OL LL) (c g : ℤ_[l]) = (Γ.χΓ g : ↥(OL LL)) := by
  obtain ⟨χ, hχ⟩ := exists_integral_chi P
  have hO : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  have hZ : Function.Injective (algebraMap ℤ_[l] ↥(OL LL)) := by
    intro x y h
    have h1 := congrArg (algebraMap ↥(OL LL) ↥LL.1) h
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l], IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] _ y] at h1
    exact Subtype.ext ((algebraMap ℚ_[l] ↥LL.1).injective h1)
  have hex : ∀ g : Γ.Gam, ∃ c : ℤ_[l]ˣ, algebraMap ℤ_[l] ↥(OL LL) (c : ℤ_[l]) = (Γ.χΓ g : ↥(OL LL)) := by
    intro g
    obtain ⟨σ, rfl⟩ := Γ.resΓ_onto g
    refine ⟨χ σ, hO ?_⟩
    rw [Γ.χΓ_res, P.PD_χ, ← hχ, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l]]
    rfl
  choose c hc using hex
  exact ⟨MonoidHom.mk' c fun g h => Units.ext (hZ (by
    rw [Units.val_mul, map_mul, hc, hc, hc, map_mul, Units.val_mul])), hc⟩

end Local

theorem evLaw_integers {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l) :
    EvLaw l (O := ↥(OL LL)) (P.v LL) (OL LL).toAlgebra := by
  rintro x ⟨j, hj⟩
  have h1 : (((constantCoeff x + 1 : ↥LL.1)) : Om l) ^ l ^ j = 1 := by
    exact_mod_cast congrArg (fun x : ↥LL.1 => (x : Om l)) hj
  have h2 := norm_sub_one_lt h1
  have h3 : (((constantCoeff x + 1 : ↥LL.1)) : Om l) - 1 = ((constantCoeff x : ↥LL.1) : Om l) := by
    push_cast; ring
  rw [h3] at h2
  refine ⟨(GlobalTheory.HWL.SeriesEval.existsUnique_ev l LL x h2).1, fun ev hev a k r => ?_⟩
  have h := (GlobalTheory.HWL.SeriesEval.existsUnique_ev l LL x h2).2 ev hev a k
  have hl : (0 : ℝ) < (l : ℝ) ^ (-((r : ℚ) : ℝ)) :=
    Real.rpow_pos_of_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
  obtain ⟨m₀, hm⟩ := Metric.tendsto_atTop.1 h _ hl
  refine ⟨m₀, fun m hm' => ?_⟩
  rw [← WithTop.coe_natCast, (NormVal.locPrime_v_normalised l P LL).2.1]
  have := (hm m hm').le
  rw [dist_comm, dist_eq_norm] at this
  exact this

theorem nonempty_wSer : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ Γ : GamS P K s LL, Nonempty (WSer Γ) := by
  intro l _ P K s LL _ Γ
  obtain ⟨_, hcomp, -, hu, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  have : IsHausdorff (Ideal.span {(l : ↥(OL LL))}) ↥(OL LL) :=
    ⟨fun x hx => IsHausdorff.haus (I := IsLocalRing.maximalIdeal ↥(OL LL)) inferInstance x fun k =>
      (hx k).mono (Submodule.smul_mono_left (Ideal.pow_right_mono
        ((Ideal.span_singleton_le_iff_mem _).2 hu) k))⟩
  have : FiniteDimensional ℚ_[l] ↥(K0 K) := (P.PD K).finK₀
  have : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨c, hc⟩ := exists_padic_char Γ
  refine nonempty_wSer_of_evLaw Γ (P.PD_p K) c hc (dvd_of_le_v P) ?_
  convert evLaw_integers P LL using 1
  exact Algebra.algebra_ext _ _ fun r => PowerSeries.algebraMap_apply

end GlobalTheory.HWL.Ser
