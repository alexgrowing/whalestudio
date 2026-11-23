import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisIncl
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
open scoped Formalism.Per

namespace GlobalTheory.BdRQuot

theorem isUnit_one_add {R : Type} [CommRing R] (I : Ideal R) (z : AdicCompletion I R)
    (hz : AdicCompletion.evalₐ I 1 z = 0) : IsUnit (1 + z) := by
  have h1 : z.val 1 = 0 := by
    have h' : (I ^ 1 • ⊤ : Ideal R) = I ^ 1 := by ext x; simp
    exact (map_eq_zero_iff _ (Ideal.quotientEquivAlgOfEq R h').injective).1 hz
  have hu : ∀ n, IsUnit (1 + z.val n) := by
    intro n
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (z.val (n + 1))
    have e1 := z.property (show 1 ≤ n + 1 by omega)
    have e2 := z.property (show n ≤ n + 1 by omega)
    rw [← hr, AdicCompletion.transitionMap_ideal_mk] at e1 e2
    rw [h1, Ideal.Quotient.eq_zero_iff_mem] at e1
    have hrI : r ∈ I := by simpa using e1
    refine IsNilpotent.isUnit_one_add ⟨n, ?_⟩
    rw [← e2, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    simpa using Ideal.pow_mem_pow hrI n
  let u : AdicCompletion I R := ⟨fun n => Ring.inverse (1 + z.val n), fun {m n} hmn => by
    have e := congrArg (AdicCompletion.transitionMap I R hmn) (Ring.inverse_mul_cancel _ (hu n))
    rw [AdicCompletion.transitionMap_map_mul, map_add, AdicCompletion.transitionMap_map_one,
      z.property hmn] at e
    exact left_inv_eq_right_inv e (Ring.mul_inverse_cancel _ (hu m))⟩
  refine IsUnit.of_mul_eq_one u ?_
  ext n
  exact Ring.mul_inverse_cancel _ (hu n)

variable {l : ℕ} [Fact l.Prime]

theorem one_mem_FilP_zero : (1 : Per.BdRp l) ∈ Per.FilP l 0 := by
  rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, map_one, ← map_one (Ideal.Quotient.mk (Per.kerP l ^ 0)), Ideal.Quotient.eq_zero_iff_mem]
  simp

theorem mem_FilD_nat (n : ℕ) (x : Per.BdR l) :
    x ∈ Per.FilD l n ↔ ∃ z ∈ Per.FilP l n, algebraMap (Per.BdRp l) (Per.BdR l) z = x := by
  constructor
  · exact fun h => GlobalTheory.RingIface.exists_of_mem_FilD_nat l h
  · rintro ⟨z, hz, rfl⟩
    exact GlobalTheory.RingIface.alg_mem_FilD_nat l hz

theorem mem_filtration_zero (y : Per.BdRp l) : y ∈ Per.FilP l 0 := by
  simpa using Ideal.mul_mem_left _ y one_mem_FilP_zero

variable {P : LocPrime l} {AI : LocAinf l P}

theorem eD_ιA (T : LocTied l P AI) (a : Ainf l) :
    T.eD (P.ιB (AI.ιA a)) = Per.pD l (algebraMap (Per.Ainf l) (Per.AinfP l) a) := by
  have h := GlobalTheory.CrisIncl.incl_aB l _ T.incl a
  rw [← T.ιA, ← GlobalTheory.RingIface.pD_eq_alg] at h
  simpa using h

theorem exists_approx (T : LocTied l P AI) (n : ℕ) (x : P.R.BdR) (hx : x ∈ (P.PD (botExt l)).Fil 0) :
    ∃ (k : ℕ) (a : Ainf l), (l : P.R.BdR) ^ k * x - P.ιB (AI.ιA a) ∈ (P.PD (botExt l)).Fil (n : ℤ) := by
  obtain ⟨y, -, hy⟩ := (mem_FilD_nat 0 _).1 ((T.fil _ _ _).1 hx)
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (Per.ev l n y)
  obtain ⟨k, a, ha⟩ := IsLocalization.Away.surj (S := Per.AinfP l) (l : Per.Ainf l) s
  refine ⟨k, a, (T.fil _ _ _).2 ((mem_FilD_nat n _).2
    ⟨(l : Per.BdRp l) ^ k * y - algebraMap (Per.AinfP l) (Per.BdRp l) (algebraMap (Per.Ainf l) _ a), ?_, ?_⟩)⟩
  · rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow]
    have e : ∀ r : Per.AinfP l, Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) r) =
        Ideal.Quotient.mk _ r := fun r => GlobalTheory.RingIface.ev_alg l n r
    rw [map_sub, e, ← ha, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast, map_natCast,
      hs, mul_comm, sub_self]
  · rw [map_sub, map_sub, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast, eD_ιA, hy,
      GlobalTheory.RingIface.pD_eq_alg]

theorem exists_inv (T : LocTied l P AI) (y : P.R.BdR) (hy : y ∈ (P.PD (botExt l)).Fil 1) :
    ∃ u ∈ (P.PD (botExt l)).Fil 0, (1 + y) * u = 1 := by
  obtain ⟨z, hz, e⟩ := (mem_FilD_nat 1 _).1 ((T.fil _ _ _).1 hy)
  have hU : IsUnit (1 + z : Per.BdRp l) := by
    obtain ⟨c, -, hc⟩ := GlobalTheory.RingIface.exists_bdRp_equiv l
    have h := isUnit_one_add (Per.kerP l) (c z) (by rw [hc]; exact (GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow l 1 z).1 hz)
    have h' := h.map c.symm
    rwa [map_add, map_one, RingEquiv.symm_apply_apply] at h'
  obtain ⟨v, hv'⟩ := hU.exists_right_inv
  refine ⟨T.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) v), (T.fil _ _ _).2 ?_, T.eD.injective ?_⟩
  · rw [RingEquiv.apply_symm_apply]
    exact (mem_FilD_nat 0 _).2 ⟨v, mem_filtration_zero _, rfl⟩
  · rw [map_mul, map_add, map_one, RingEquiv.apply_symm_apply, ← e,
      ← map_one (algebraMap (Per.BdRp l) (Per.BdR l)), ← map_add, ← map_mul, hv']

theorem mul_mem_zero {a : ℤ} {x y : P.R.BdR} (hx : x ∈ (P.PD (botExt l)).Fil 0)
    (hy : y ∈ (P.PD (botExt l)).Fil a) : x * y ∈ (P.PD (botExt l)).Fil a := by
  simpa using (P.PD (botExt l)).Fil_mul 0 a x y hx hy

theorem pow_mem_Fil {a : ℤ} {x : P.R.BdR} (hx : x ∈ (P.PD (botExt l)).Fil a) (n : ℕ) :
    x ^ n ∈ (P.PD (botExt l)).Fil (n * a) := by
  induction n with
  | zero => simpa using (P.PD (botExt l)).one_mem
  | succ n ih =>
    rw [pow_succ, Nat.cast_succ, add_mul, one_mul]
    exact (P.PD (botExt l)).Fil_mul _ _ _ _ ih hx

theorem theta_pow (J : ThetaL P AI) (a : Ainf l) (k : ℕ) :
    J.θ (P.ιB (AI.ιA (a ^ k))) = J.θ (P.ιB (AI.ιA a)) ^ k := by
  induction k with
  | zero => simpa using J.θ_one
  | succ k ih => rw [pow_succ, map_mul, map_mul, J.θ_mul _ (AI.ainf_image_mem_filtration_zero _ _) _ (AI.ainf_image_mem_filtration_zero _ _), ih, pow_succ]

theorem εroot_pow (n : ℕ) : AI.εroot (n + 1) ^ l ^ n = AI.ε1 := by
  induction n with
  | zero => simp [LocAinf.εroot, LocAinf.ε1]
  | succ n ih =>
    rw [pow_succ', pow_mul, ← ih, LocAinf.εroot, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
    rfl

theorem ζ_pow (n : ℕ) : AI.ζ (n + 1) ^ l ^ n = AI.ζ 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, AI.ζ_succ, ih]

theorem theta_teich (J : ThetaL P AI) :
    J.θ (P.ιB (AI.ιA (WittVector.teichmuller l AI.ε1))) = ((AI.ζ 1 : OC l) : PadicComplex l) := by
  have key : ∀ n : ℕ, ‖J.θ (P.ιB (AI.ιA (WittVector.teichmuller l AI.ε1))) -
      ((AI.ζ 1 : OC l) : PadicComplex l)‖ ≤ ‖(l : PadicComplex l)‖ ^ (n + 1) := by
    intro n
    let c : OC l := ⟨J.θ (P.ιB (AI.ιA (WittVector.teichmuller l (AI.εroot (n + 1))))),
      (GlobalTheory.RingBasics.mem_OC _).2 (J.θ_int _)⟩
    have h1 := J.θ_teich (AI.εroot (n + 1)) (AI.ζ (n + 1)) (by
      rw [LocAinf.εroot, PreTilt.coeff_iterate_frobeniusEquiv_symm, zero_add, AI.ε_coeff])
    have h2 : ((l : ℕ) : OC l) ∣ c - AI.ζ (n + 1) := by
      have := (GlobalTheory.RingBasics.mem_span_pow_OC 1 (c - AI.ζ (n + 1))).2 (by simpa using h1)
      rwa [pow_one, Ideal.mem_span_singleton] at this
    have h3 := dvd_sub_pow_of_dvd_sub h2 n
    rw [← Ideal.mem_span_singleton, ← Ideal.span_singleton_pow, GlobalTheory.RingBasics.mem_span_pow_OC, ζ_pow] at h3
    rw [← εroot_pow (AI := AI) n, map_pow, theta_pow]
    simpa using h3
  have lim := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (l : PadicComplex l))
    GlobalTheory.RingBasics.norm_p_lt).comp (Filter.tendsto_add_atTop_nat 1)
  exact sub_eq_zero.1 (norm_le_zero_iff.1 (ge_of_tendsto' lim key))

theorem exists_t_eq (T : LocTied l P AI) (J : ThetaL P AI) :
    ∃ w ∈ (P.PD (botExt l)).Fil 0, P.ιB P.tB = P.ιB (AI.ιA AI.ξ) * w ∧
      J.θ w = ((AI.ζ 1 : OC l) : PadicComplex l) - 1 := by
  obtain ⟨y, hy, e⟩ := (J.fil_succ_iff_mul_t 1 _).1 J.t_μ
  obtain ⟨u, hu, hyu⟩ := exists_inv T y hy
  have hy0 : y ∈ (P.PD (botExt l)).Fil 0 := (P.PD (botExt l)).Fil_anti 0 hy
  have h1 := (P.PD (botExt l)).one_mem
  have hθu : J.θ u = 1 := by
    have := congrArg J.θ hyu
    rwa [J.θ_mul _ (add_mem h1 hy0) _ hu, J.θ_add _ h1 _ hy0, (J.θ_ker y hy0).2 hy, J.θ_one,
      add_zero, one_mul] at this
  have hπ : J.θ (P.ιB (AI.ιA AI.π₁)) = ((AI.ζ 1 : OC l) : PadicComplex l) - 1 := by
    rw [eq_sub_iff_add_eq, ← theta_teich J, ← J.θ_one, ← J.θ_add _ (AI.ainf_image_mem_filtration_zero _ _) _ h1]
    simp [LocAinf.π₁]
  refine ⟨P.ιB (AI.ιA AI.π₁) * u, mul_mem_zero (AI.ainf_image_mem_filtration_zero _ _) hu, ?_, ?_⟩
  · rw [AI.μ_eq, map_mul, map_mul] at e
    linear_combination (-u) * e - P.ιB P.tB * hyu
  · rw [J.θ_mul _ (AI.ainf_image_mem_filtration_zero _ _) _ hu, hθu, mul_one, hπ]

theorem exists_t_pow (J : ThetaL P AI) (a : ℤ) (n : ℕ) (x : P.R.BdR)
    (hx : x ∈ (P.PD (botExt l)).Fil (a + n)) :
    ∃ y ∈ (P.PD (botExt l)).Fil a, x = P.ιB P.tB ^ n * y := by
  induction n generalizing x with
  | zero => exact ⟨x, by simpa using hx, by simp⟩
  | succ n ih =>
    rw [Nat.cast_succ, ← add_assoc] at hx
    obtain ⟨z, hz, rfl⟩ := (J.fil_succ_iff_mul_t _ _).1 hx
    obtain ⟨y, hy, rfl⟩ := ih z hz
    exact ⟨y, hy, by ring⟩

theorem mem_Fil_iff (T : LocTied l P AI) (J : ThetaL P AI) (n : ℕ) (a : Ainf l) :
    P.ιB (AI.ιA a) ∈ (P.PD (botExt l)).Fil (n : ℤ) ↔ AI.ξ ^ n ∣ a := by
  have hξ : P.ιB (AI.ιA AI.ξ) ∈ (P.PD (botExt l)).Fil 1 :=
    (AI.ainf_image_mem_filtration_one_iff _ _).2 ⟨1, (mul_one _).symm⟩
  constructor
  · obtain ⟨w, hw, ht, -⟩ := exists_t_eq T J
    have hunit : IsUnit (P.ιB (AI.ιA AI.ξ)) := by
      have := (P.PD (botExt l)).t_unit.map P.ιB
      rw [P.period_datum_t_eq, ht] at this
      exact isUnit_of_mul_isUnit_left this
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro h
      rw [Nat.cast_succ] at h
      obtain ⟨b, rfl⟩ := ih ((P.PD (botExt l)).Fil_anti _ h)
      rw [add_comm] at h
      obtain ⟨y, hy, e⟩ := exists_t_pow J 1 n _ h
      rw [map_mul, map_mul, map_pow, map_pow, ht, mul_pow, mul_assoc] at e
      have e' := (hunit.pow n).mul_left_cancel e
      have hb : P.ιB (AI.ιA b) ∈ (P.PD (botExt l)).Fil 1 := by
        rw [e']
        exact mul_mem_zero (by simpa using pow_mem_Fil hw n) hy
      obtain ⟨c, rfl⟩ := (AI.ainf_image_mem_filtration_one_iff _ _).1 hb
      exact ⟨c, by rw [pow_succ, mul_assoc]; rfl⟩
  · rintro ⟨b, rfl⟩
    rw [map_mul, map_mul, map_pow, map_pow, mul_comm]
    exact mul_mem_zero (AI.ainf_image_mem_filtration_zero _ _) (by simpa using pow_mem_Fil hξ n)

theorem fil_quotient : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (J : ThetaL P AI) (n : ℕ),
    (∀ x ∈ (P.PD (botExt l)).Fil 0, ∃ (k : ℕ) (a : Ainf l),
      (l : P.R.BdR) ^ k * x - P.ιB (AI.ιA a) ∈ (P.PD (botExt l)).Fil (n : ℤ)) ∧
    (∀ a : Ainf l, P.ιB (AI.ιA a) ∈ (P.PD (botExt l)).Fil (n : ℤ) ↔ AI.ξ ^ n ∣ a) ∧
    (∃ w ∈ (P.PD (botExt l)).Fil 0, P.ιB P.tB = P.ιB (AI.ιA AI.ξ) * w ∧
      J.θ w = ((AI.ζ 1 : OC l) : PadicComplex l) - 1) :=
  fun _ _ _ _ T J n => ⟨exists_approx T n, mem_Fil_iff T J n, exists_t_eq T J⟩

end GlobalTheory.BdRQuot
