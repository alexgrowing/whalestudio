import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSecondVeroneseParts
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionsRank
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter fwdDiff
open scoped Pointwise

noncomputable section

namespace VeroneseGenDeg

theorem finrank_homog (D n : ℕ) :
    Module.finrank ℤ (homogeneousSubmodule (Fin (D + 1)) ℤ n) = (n + D).choose D := by
  have hs : {d : Fin (D + 1) →₀ ℕ | d.degree = n} =
      ((Finset.univ.finsuppAntidiag n : Finset (Fin (D + 1) →₀ ℕ)) : Set (Fin (D + 1) →₀ ℕ)) := by
    ext d; simp [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum]
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported, hs,
    (AddMonoidAlgebra.supportedEquivFinsupp _).finrank_eq, Module.finrank_finsupp_self]
  simp only [Finset.coe_sort_coe, Fintype.card_coe, Finset.card_finsuppAntidiag_nat_eq_choose,
    Finset.card_univ, Fintype.card_fin]
  rw [show D + 1 + n - 1 = n + D by omega]
  exact Nat.choose_symm_add

theorem range_alt (D : ℕ) : Set.range (Veronese.x D) = Set.range (Veronese.t D) ^ 2 := by
  ext y
  rw [pow_two, Set.mem_mul]
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨_, ⟨_, rfl⟩, _, ⟨_, rfl⟩, rfl⟩
  · rintro ⟨a, ⟨i, rfl⟩, b, ⟨j, rfl⟩, rfl⟩
    rcases le_total i j with hij | hij
    · exact ⟨⟨(), ⟨(i, j), hij⟩⟩, rfl⟩
    · exact ⟨⟨(), ⟨(j, i), hij⟩⟩, mul_comm _ _⟩

theorem aeval_t_injective (D : ℕ) :
    Function.Injective (aeval (Veronese.t D) : MvPolynomial (Fin (D + 1)) ℤ →ₐ[ℤ] Veronese.Fld D) := by
  have h : (aeval (Veronese.t D) : MvPolynomial (Fin (D + 1)) ℤ →ₐ[ℤ] Veronese.Fld D).toRingHom =
      (algebraMap (MvPolynomial (Fin (D + 1)) ℚ) (Veronese.Fld D)).comp
        (MvPolynomial.map (Int.castRingHom ℚ)) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · simp
    · simp [Veronese.t]
  have hinj : Function.Injective ((algebraMap (MvPolynomial (Fin (D + 1)) ℚ) (Veronese.Fld D)).comp
      (MvPolynomial.map (Int.castRingHom ℚ))) :=
    (IsFractionRing.injective (MvPolynomial (Fin (D + 1)) ℚ) (Veronese.Fld D)).comp
      (MvPolynomial.map_injective _ (RingHom.injective_int _))
  rw [← h] at hinj
  exact hinj

theorem finrank_sec (D n : ℕ) :
    Module.finrank ℤ (sec ℤ (Veronese.x D) n) = (2 * n + D).choose D := by
  have h1 : sec ℤ (Veronese.x D) n = sec ℤ (Veronese.t D) (2 * n) := by
    rw [SectionsRank.sec_eq_span, SectionsRank.sec_eq_span, range_alt, ← pow_mul]
  rw [h1, ← finrank_homog D (2 * n)]
  exact (Submodule.equivMapOfInjective _ (aeval_t_injective D) _).finrank_eq.symm

theorem mixedDiff_const {K : Type*} (D : ℕ) (b : K → ℤ) (h : (K → ℤ) → ℤ) :
    GroundTheory.Heights₂.Heights.NumbersDVR.mixedDiff (fun _ : Fin D => b) h =
      (GroundTheory.Heights₂.Heights.NumbersDVR.diffStep b)^[D] h := by
  unfold GroundTheory.Heights₂.Heights.NumbersDVR.mixedDiff
  rw [List.ofFn_const]
  induction D with
  | zero => rfl
  | succ D ih => rw [List.replicate_succ, List.foldr_cons, ih, Function.iterate_succ_apply']

theorem iterate_diffStep (D : ℕ) (H : (Unit → ℤ) → ℤ) (k : ℤ) :
    (GroundTheory.Heights₂.Heights.NumbersDVR.diffStep 1)^[D] H (fun _ => k) =
      (fwdDiff (1 : ℤ))^[D] (fun j : ℤ => H (fun _ => j)) (k - D) := by
  induction D generalizing H with
  | zero => simp
  | succ D ih =>
    rw [Function.iterate_succ_apply, ih]
    have hg : (fun j : ℤ => GroundTheory.Heights₂.Heights.NumbersDVR.diffStep 1 H (fun _ => j)) =
        fun j : ℤ => fwdDiff 1 (fun j : ℤ => H (fun _ => j)) (j + -1) := by
      funext j
      have e1 : (fun _ : Unit => j + -1 + 1) = fun _ => j := by funext u; ring
      have e2 : ((fun _ : Unit => j) - 1) = fun _ => j + -1 := by funext u; simp; ring
      simp only [GroundTheory.Heights₂.Heights.NumbersDVR.diffStep, fwdDiff, e1, e2]
    rw [hg, fwdDiff_iter_comp_add, ← Function.iterate_succ_apply,
      show k - (D : ℤ) + -1 = k - ((D + 1 : ℕ) : ℤ) by push_cast; ring]

def hilbPoly (D : ℕ) : Polynomial ℚ :=
  (Polynomial.preHilbertPoly ℚ D 0).comp (Polynomial.C 2 * Polynomial.X)

theorem hilbPoly_eval (D n : ℕ) : (hilbPoly D).eval (n : ℚ) = ((2 * n + D).choose D : ℚ) := by
  rw [hilbPoly, Polynomial.eval_comp]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  have := Polynomial.preHilbertPoly_eq_choose_sub_add ℚ D (k := 0) (n := 2 * n) (Nat.zero_le _)
  push_cast at this
  rw [this, Nat.sub_zero]

theorem fwdDiff_hilbPoly (D : ℕ) (y : ℚ) : (fwdDiff (1 : ℚ))^[D] (hilbPoly D).eval y = 2 ^ D := by
  have hdeg : (hilbPoly D).natDegree = D := by
    rw [hilbPoly, Polynomial.natDegree_comp, Polynomial.natDegree_preHilbertPoly,
      Polynomial.natDegree_C_mul_X _ two_ne_zero, mul_one]
  have hlc : (hilbPoly D).leadingCoeff = (D.factorial : ℚ)⁻¹ * 2 ^ D := by
    rw [hilbPoly, Polynomial.leadingCoeff_comp (by rw [Polynomial.natDegree_C_mul_X _ two_ne_zero]; exact one_ne_zero),
      Polynomial.leadingCoeff_preHilbertPoly, Polynomial.leadingCoeff_C_mul_X,
      Polynomial.natDegree_preHilbertPoly]
  have h := congrFun (Polynomial.fwdDiff_iter_degree_eq_factorial (hilbPoly D)) y
  rw [hdeg, hlc] at h
  rw [h]
  have hf : (D.factorial : ℚ) ≠ 0 := by positivity
  simp only [Pi.smul_apply, Pi.natCast_apply, smul_eq_mul]
  field_simp

theorem eventualValue_eq {K : Type*} (F : (K → ℤ) → ℤ) (c : ℤ)
    (h : ∀ᶠ m in atTop, F m = c) : GroundTheory.Heights₂.Heights.NumbersDVR.eventualValue F = c := by
  unfold GroundTheory.Heights₂.Heights.NumbersDVR.eventualValue
  have hex : ∃ c, ∀ᶠ m in atTop, F m = c := ⟨c, h⟩
  rw [dif_pos hex]
  obtain ⟨m, h1, h2⟩ := (hex.choose_spec.and h).exists
  rw [← h1, h2]

end VeroneseGenDeg

open VeroneseGenDeg in

theorem VeroneseGenDeg.proof : VeroneseGenDeg.Statement := by
  intro D _
  set q := (coordIdeal ℤ (Veronese.x D)).map (MvPolynomial.map (Int.castRingHom ℚ)) with hq
  set g : ℤ → ℤ := fun j => GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn (ι := GlobalTheory (Veronese.Idx D)) q (fun _ => j)
    with hgdef

  have hg : ∀ j : ℤ, 0 ≤ j → (g j : ℚ) = (hilbPoly D).eval (j : ℚ) := by
    intro j hj
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hj
    have h := SectionsRank.proof (Veronese.Fld D) (Veronese.Idx D) (Veronese.x D) n
    rw [finrank_sec] at h
    simp only [hgdef]
    rw [← hq] at h
    rw [h, Int.cast_natCast, Int.cast_natCast, hilbPoly_eval]
  have hev : ∀ᶠ m in atTop, GroundTheory.Heights₂.Heights.NumbersDVR.mixedDiff (fun _ : Fin D => (1 : Unit → ℤ))
      (GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn (ι := GlobalTheory (Veronese.Idx D)) q) m = 2 ^ D := by
    filter_upwards [eventually_ge_atTop (fun _ : Unit => (D : ℤ))] with m hm
    have hm' : m = fun _ => m () := funext fun u => rfl
    have hD : (D : ℤ) ≤ m () := hm ()
    rw [mixedDiff_const, hm', iterate_diffStep]
    have key : (((fwdDiff (1 : ℤ))^[D] g (m () - D) : ℤ) : ℚ) = 2 ^ D := by
      rw [← fwdDiff_hilbPoly D ((m () - D : ℤ) : ℚ), fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [nsmul_eq_mul, mul_one, smul_eq_mul, zsmul_eq_mul]
      push_cast
      rw [hg _ (by omega)]
      push_cast
      ring
    exact_mod_cast key
  unfold genDeg GroundTheory.Heights₂.Heights.NumbersDVR.intNum
  apply eventualValue_eq
  convert hev

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
