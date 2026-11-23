import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsCMTypeEmbedding
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ContinuousIdeleCircle
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HeckeCharacterConductorExponentStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CmHeckeCharacterInfinityTypeStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CmHeckeCharacterNotNormPowerStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HeckeLFunctionEulerProductStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocalAdditiveCharacterEqAdelicStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteEpsilonFactorDependenceOnSStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HaarIntegralIntegersFiniteSumStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HeckeGaussSumLocalTermStatement

noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

namespace GlobalTheory.CompanionTheory.HeckeFE
variable {E : Type} [Field E] [NumberField E]

theorem L_cond (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) (m : ℕ) (h : ExpAt χ v m) :
    multiplicity v.asIdeal (toHecke χ hu).conductor = m := GlobalTheory.T.hecke_character_conductor_exponent E χ hu v m h

theorem L_inf {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hφ : IsCMType φ) [IsTotallyComplex E] (χ : HChar E) (hu : IsUnitary χ)
    (n : I → ℤ) (hi : Formalism.L2.Host.HChar.HasInf χ φ n) (i : I) :
    (toHecke χ hu).infiniteTau (InfinitePlace.mk (φ i)) = 0 ∧
      ((toHecke χ hu).infiniteWeight (InfinitePlace.mk (φ i))).natAbs = (n i).natAbs :=
  GlobalTheory.T.cm_hecke_character_infinity_type E I φ hφ χ hu n hi i

theorem L_notPow {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hφ : IsCMType φ) [IsTotallyComplex E] (χ : HChar E) (hu : IsUnitary χ)
    (n : I → ℤ) (hi : Formalism.L2.Host.HChar.HasInf χ φ n) (hn : ∃ i, n i ≠ 0) :
    ¬ ∃ τ : ℝ, ∀ x : IdeleGroup E,
      ((toHecke χ hu).toIdele x : ℂ) = ((ideleModule E x : ℝ) : ℂ) ^ ((τ : ℂ) * Complex.I) :=
  GlobalTheory.T.cm_hecke_character_not_norm_power E I φ hφ χ hu n hi hn

theorem L_euler (χ : HChar E) (hu : IsUnitary χ) {s : ℂ} (hs : 1 < s.re) :
    HasProd (eulerFactor χ s) ((toHecke χ hu).LFunction s) := GlobalTheory.T.hecke_L_function_euler_product E χ hu s hs

theorem L_shift (χ : HChar E) (a : HeightOneSpectrum (𝓞 E) →₀ ℕ) (s : ℂ) :
    finEps χ a s = finEps χ a (1 / 2) *
      (((discr E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k : ℕ) : ℂ) ^ (1 / 2 - s) := GlobalTheory.T.finite_epsilon_factor_dependence_on_s E χ a s

theorem ord_unif (v : HeightOneSpectrum (𝓞 E)) (k : ℕ) :
    ord ((atFin v (unif v ^ k) : (v.adicCompletion E)ˣ) : v.adicCompletion E) = k := by
  have h := valued_eq_exp_neg_ord (v := v) (Units.ne_zero (atFin v (unif v ^ k)))
  have h2 : Valued.v ((atFin v (unif v ^ k) : (v.adicCompletion E)ˣ) : v.adicCompletion E) = WithZero.exp (-(k : ℤ)) := by
    have h3 : Valued.v ((atFin v (unif v) : (v.adicCompletion E)ˣ) : v.adicCompletion E) = WithZero.exp (-1 : ℤ) := unif_spec v
    rw [map_pow, Units.val_pow_eq_pow_val, map_pow, h3, ← WithZero.exp_nsmul]
    simp
  rw [h2, WithZero.exp_inj] at h
  omega

theorem differentExp_eq (v : HeightOneSpectrum (𝓞 E)) : differentExp v = (diffExp v : ℤ) :=
  count_coeIdeal_eq_multiplicity v _root_.differentIdeal_ne_bot

theorem L_ramInt (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) {m : ℕ} (hm : m ≠ 0) (h : ExpAt χ v m) :
    ∫ y, (toHecke χ hu).finiteTest v y *
        (localAdelicChar E v (((atFin v (unif v ^ (m + diffExp v)) : (v.adicCompletion E)ˣ) : v.adicCompletion E)⁻¹ * y) : ℂ)
        ∂haarIntegers (v.adicCompletion E) =
      (((Ideal.absNorm v.asIdeal ^ m : ℕ) : ℂ))⁻¹ * gaussSumAt χ v m (unif v ^ (m + diffExp v)) := by
  have hc : multiplicity v.asIdeal (toHecke χ hu).conductor = m := L_cond χ hu v m h
  have hG := GlobalTheory.T.hecke_gauss_sum_local_term E χ hu v m hm h
  simp only [GlobalTheory.T.local_additive_character_eq_adelic] at hG
  rw [GlobalTheory.T.haar_integral_integers_finite_sum E v m _ (fun y hy => by rw [(toHecke χ hu).finiteTest_eq_zero hy, zero_mul]) (fun y k hk => ?_), hG]
  set c : v.adicCompletion E := ((atFin v (unif v ^ (m + diffExp v)) : (v.adicCompletion E)ˣ) : v.adicCompletion E) with hcdef
  have hcv : Valued.v c = WithZero.exp (-((m + diffExp v : ℕ) : ℤ)) := by
    have h3 : Valued.v ((atFin v (unif v) : (v.adicCompletion E)ˣ) : v.adicCompletion E) = WithZero.exp (-1 : ℤ) := unif_spec v
    rw [hcdef, map_pow, Units.val_pow_eq_pow_val, map_pow, h3, ← WithZero.exp_nsmul]
    simp
  have hψ : localAdelicChar E v (c⁻¹ * k) = 1 := by
    refine localAdelicChar_eq_one_of_mem ((mem_localInvDifferent_iff_valued v _).2 ?_)
    show _ ≤ WithZero.exp (differentExp v)
    rw [map_mul, map_inv₀, hcv, ← WithZero.exp_neg, differentExp_eq]
    calc _ ≤ WithZero.exp (- -((m + diffExp v : ℕ) : ℤ)) * WithZero.exp (-(m : ℤ)) := mul_le_mul' le_rfl hk
      _ = _ := by
        rw [← WithZero.exp_add]
        congr 1
        push_cast
        ring
  rw [(toHecke χ hu).finiteTest_add y (by rw [hc]; exact hk), mul_add, AddChar.map_add_eq_mul, hψ, mul_one]

theorem L_locUnr (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) (h : ExpAt χ v 0) :
    localEpsilon (localChar (toHecke χ hu) v) (localAdelicChar E v) (1 / 2) = locEps χ v 0 (1 / 2) := by
  have hv : ¬ v.asIdeal ∣ (toHecke χ hu).conductor := fun hd =>
    (multiplicity_pos_of_dvd hd).ne' (L_cond χ hu v 0 h)
  have hN : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  rw [(toHecke χ hu).localEpsilon_half_of_not_dvd v hv (atFin v (unif v ^ (0 + diffExp v)))
    (by rw [ord_unif, differentExp_eq, zero_add]), coe_localComponent, locEps, if_pos rfl, mul_one, mul_assoc,
    ← Complex.cpow_add _ _ hN]
  have : -(1 / 2 : ℂ) * ((0 + diffExp v : ℕ) : ℂ) + (diffExp v : ℂ) / 2 = 0 := by
    push_cast
    ring
  rw [this, Complex.cpow_zero, mul_one]
  rfl

theorem L_locRam (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) {m : ℕ} (hm : m ≠ 0) (h : ExpAt χ v m) :
    localEpsilon (localChar (toHecke χ hu) v) (localAdelicChar E v) (1 / 2) = locEps χ v m (1 / 2) := by
  have hc := L_cond χ hu v m h
  have hv : v.asIdeal ∣ (toHecke χ hu).conductor := by
    by_contra hd
    exact hm (hc ▸ multiplicity_eq_zero.2 hd)
  have hN : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  rw [(toHecke χ hu).localEpsilon_half_of_dvd v hv (atFin v (unif v ^ (m + diffExp v)))
    (by rw [ord_unif, differentExp_eq, HeckeCharacter.condExp_eq, hc]; push_cast; rfl),
    L_ramInt χ hu v hm h, coe_localComponent, locEps, if_neg hm, hc]
  set c : ℂ := ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ ((m : ℂ) / 2) with hcdef
  have hc0 : c ≠ 0 := by
    rw [hcdef, Ne, Complex.cpow_eq_zero_iff]
    tauto
  have h1 : (Real.sqrt ((Ideal.absNorm v.asIdeal ^ m : ℕ) : ℝ) : ℂ) = c := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg _), hcdef]
    push_cast
    rw [← Complex.natCast_cpow_natCast_mul]
    congr 1
    ring
  have h2 : (((Ideal.absNorm v.asIdeal ^ m : ℕ) : ℂ)) = c * c := by
    rw [hcdef, ← Complex.cpow_add _ _ hN]
    push_cast
    rw [add_halves, Complex.cpow_natCast]
  have h3 : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(1 / 2 : ℂ) * ((m + diffExp v : ℕ) : ℂ)) *
      ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ ((diffExp v : ℂ) / 2) = c⁻¹ := by
    rw [← Complex.cpow_add _ _ hN, hcdef, ← Complex.cpow_neg]
    congr 1
    push_cast
    ring
  rw [h1, h2]
  have h4 : ((χ.locK v (unif v ^ (m + diffExp v)) : ℂˣ) : ℂ) = ((χ.loc v (atFin v (unif v ^ (m + diffExp v))) : ℂˣ) : ℂ) := rfl
  rw [h4]
  have h5 : c * (c * c)⁻¹ = c⁻¹ := by
    field_simp
  linear_combination (((χ.loc v (atFin v (unif v ^ (m + diffExp v))) : ℂˣ) : ℂ) * gaussSumAt χ v m (unif v ^ (m + diffExp v))) * (h5 - h3)

theorem bijective_mk {I : Type} {φ : I → E →+* ℂ} (hφ : IsCMType φ) :
    Function.Bijective fun i => InfinitePlace.mk (φ i) := by
  constructor
  · intro i j h
    have h' : InfinitePlace.mk (φ i) = InfinitePlace.mk (φ j) := h
    obtain ⟨k, -, hk⟩ := hφ (φ i)
    have h1 := hk i (Or.inl rfl)
    rcases InfinitePlace.mk_eq_iff.1 h' with e | e
    · exact h1.trans (hk j (Or.inl e)).symm
    · exact h1.trans (hk j (Or.inr (by rw [← e]; ext x; simp))).symm
  · intro w
    obtain ⟨i, hi, -⟩ := hφ w.embedding
    refine ⟨i, ?_⟩
    rcases hi with e | e
    · show InfinitePlace.mk (φ i) = w
      rw [← e, InfinitePlace.mk_embedding]
    · show InfinitePlace.mk (φ i) = w
      rw [← InfinitePlace.mk_conjugate_eq, ← e, InfinitePlace.mk_embedding]

section
variable {I : Type} [Fintype I] {φ : I → E →+* ℂ} [IsTotallyComplex E] {χ : HChar E} {n : I → ℤ}

theorem gammaFactor_toHecke (hφ : IsCMType φ) (hu : IsUnitary χ) (hi : Formalism.L2.Host.HChar.HasInf χ φ n) (s : ℂ) :
    (toHecke χ hu).gammaFactor s = archFactor n s := by
  rw [HeckeCharacter.gammaFactor, archFactor, ← (Equiv.ofBijective _ (bijective_mk hφ)).prod_comp]
  refine Finset.prod_congr rfl fun i _ => ?_
  obtain ⟨h1, h2⟩ := L_inf φ hφ χ hu n hi i
  have hc : ¬ (InfinitePlace.mk (φ i)).IsReal := InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex _)
  have e : (((n i).natAbs : ℕ) : ℂ) = ((|n i| : ℤ) : ℂ) := by
    rw [← Int.cast_natCast, Int.natCast_natAbs]
  show (toHecke χ hu).infiniteGamma (InfinitePlace.mk (φ i)) s = _
  rw [HeckeCharacter.infiniteGamma, if_neg hc, h1, h2, e, Complex.Gammaℂ_def]
  simp

theorem prod_weight_toHecke (hφ : IsCMType φ) (hu : IsUnitary χ) (hi : Formalism.L2.Host.HChar.HasInf χ φ n) :
    (∏ w, (-Complex.I) ^ ((toHecke χ hu).infiniteWeight w).natAbs) = archEps n := by
  rw [archEps, ← Finset.prod_pow_eq_pow_sum, ← (Equiv.ofBijective _ (bijective_mk hφ)).prod_comp]
  refine Finset.prod_congr rfl fun i _ => ?_
  show (-Complex.I) ^ ((toHecke χ hu).infiniteWeight (InfinitePlace.mk (φ i))).natAbs = _
  rw [(L_inf φ hφ χ hu n hi i).2]

theorem rootNumber_toHecke (hφ : IsCMType φ) (hu : IsUnitary χ) (hi : Formalism.L2.Host.HChar.HasInf χ φ n)
    {a : HeightOneSpectrum (𝓞 E) →₀ ℕ} (ha : ∀ w, ExpAt χ w (a w)) :
    (toHecke χ hu).rootNumber = archEps n * finEps χ a (1 / 2) := by
  have h1 := (toHecke χ hu).finiteFourier_mul_eq_finprod_localEpsilon
    (toHecke χ hu).toFractionalIdeal_conductorDifferentIdele
  have h2 : (∏ᶠ v, localEpsilon (localChar (toHecke χ hu) v) (localAdelicChar E v) (1 / 2)) = finEps χ a (1 / 2) := by
    refine finprod_congr fun v => ?_
    by_cases hv : a v = 0
    · have := ha v
      rw [hv] at this ⊢
      exact L_locUnr χ hu v this
    · exact L_locRam χ hu v hv (ha v)
  rw [h2] at h1
  rw [HeckeCharacter.rootNumber, HeckeCharacter.fourierConst, prod_weight_toHecke hφ hu hi, ← h1]
  ring

def conductorNormalizedCompletedLFunction (χ : HChar E) (hu : IsUnitary χ) (s : ℂ) : ℂ :=
  ((toHecke χ hu).discrNormConductor : ℂ) ^ (-(s / 2)) * (toHecke χ hu).completedLFunction s

theorem isCompletedL_completed (hφ : IsCMType φ) (hu : IsUnitary χ) (hi : Formalism.L2.Host.HChar.HasInf χ φ n)
    (hn : ∃ i, n i ≠ 0) : IsCompletedL χ n (conductorNormalizedCompletedLFunction χ hu) := by
  have hA : ((toHecke χ hu).discrNormConductor : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (toHecke χ hu).discrNormConductor_pos.ne'
  refine ⟨?_, fun s hs => ⟨_, L_euler χ hu hs, ?_⟩⟩
  · refine Differentiable.mul (fun s => ?_)
      ((toHecke χ hu).differentiable_completedLFunction (L_notPow φ hφ χ hu n hi hn))
    exact ((differentiableAt_id.div_const 2).neg).const_cpow (Or.inl hA)
  · rw [conductorNormalizedCompletedLFunction, (toHecke χ hu).completedLFunction_eq hs, gammaFactor_toHecke hφ hu hi, ← mul_assoc, ← mul_assoc,
      ← Complex.cpow_add _ _ hA, neg_add_cancel, Complex.cpow_zero, one_mul]

theorem absNorm_conductor_toHecke (hu : IsUnitary χ) {a : HeightOneSpectrum (𝓞 E) →₀ ℕ} (ha : ∀ w, ExpAt χ w (a w)) :
    Ideal.absNorm (toHecke χ hu).conductor = a.prod fun v k => Ideal.absNorm v.asIdeal ^ k := by
  have hm := fun v => L_cond χ hu v (a v) (ha v)
  have h : (toHecke χ hu).conductorPrimes = a.support := by
    ext v
    rw [HeckeCharacter.mem_conductorPrimes, Finsupp.mem_support_iff, ← hm v]
    constructor
    · intro h
      exact (multiplicity_pos_of_dvd h).ne'
    · intro h
      by_contra h'
      exact h (multiplicity_eq_zero.2 h')
  rw [HeckeCharacter.absNorm_conductor, Finsupp.prod, h]
  exact Finset.prod_congr rfl fun v _ => by rw [hm v]

theorem discrNormConductor_toHecke (hu : IsUnitary χ) {a : HeightOneSpectrum (𝓞 E) →₀ ℕ} (ha : ∀ w, ExpAt χ w (a w)) :
    ((toHecke χ hu).discrNormConductor : ℂ) =
      (((discr E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k : ℕ) : ℂ) := by
  rw [HeckeCharacter.discrNormConductor, absNorm_conductor_toHecke hu ha, ← Complex.ofReal_natCast, Nat.cast_mul,
    Nat.cast_natAbs, Int.cast_abs]

theorem completed_eq (hφ : IsCMType φ) (hu : IsUnitary χ) (hi : Formalism.L2.Host.HChar.HasInf χ φ n) (hn : ∃ i, n i ≠ 0)
    (hu' : IsUnitary χ⁻¹) (s : ℂ) :
    conductorNormalizedCompletedLFunction χ hu s = (toHecke χ hu).rootNumber * ((toHecke χ hu).discrNormConductor : ℂ) ^ (1 / 2 - s) *
      conductorNormalizedCompletedLFunction χ⁻¹ hu' (1 - s) := by
  have hA : ((toHecke χ hu).discrNormConductor : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (toHecke χ hu).discrNormConductor_pos.ne'
  rw [conductorNormalizedCompletedLFunction, conductorNormalizedCompletedLFunction, toHecke_inv χ hu hu', HeckeCharacter.discrNormConductor_inv,
    (toHecke χ hu).completedLFunction_eq_rootNumber_mul_of_not (L_notPow φ hφ χ hu n hi hn) s]
  have e : ((toHecke χ hu).discrNormConductor : ℂ) ^ (-(s / 2)) =
      ((toHecke χ hu).discrNormConductor : ℂ) ^ (1 / 2 - s) *
        ((toHecke χ hu).discrNormConductor : ℂ) ^ (-((1 - s) / 2)) := by
    rw [← Complex.cpow_add _ _ hA]
    congr 1
    ring
  rw [e]
  ring

end

end GlobalTheory.CompanionTheory.HeckeFE

theorem GlobalTheory.CompanionTheory.HeckeFE.heckeTateFunctionalEquation : GlobalTheory.Published.HeckeTateFunctionalEquation := by
  intro E _ _ _ I _ φ hφ χ n a hu hi hn ha
  have hu' := GlobalTheory.Published.HeckeFEModel.isUnitary_inv hu
  have hi' := GlobalTheory.Published.HeckeFEModel.hasInf_inv hi
  have hn' : ∃ i, -n i ≠ 0 := hn.imp fun i h => neg_ne_zero.2 h
  refine ⟨conductorNormalizedCompletedLFunction χ hu, conductorNormalizedCompletedLFunction χ⁻¹ hu', isCompletedL_completed hφ hu hi hn,
    isCompletedL_completed hφ hu' hi' hn', fun s => ?_⟩
  rw [L_shift χ a s, ← discrNormConductor_toHecke hu ha, completed_eq hφ hu hi hn hu' s, rootNumber_toHecke hφ hu hi ha]
  ring
