import Mathlib
import GroundTheory.PAdicHodge.KerTheta
import GroundTheory.PAdicHodge.TiltValuation
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open WittVector

section WittGeneral

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R]

theorem WittVector.teichmuller_add_verschiebung_shift (x : WittVector p R) :
    teichmuller p (x.coeff 0) + verschiebung (x.shift 1) = x := by
  ext n
  rw [coeff_add_of_disjoint n _ _ fun m => ?_]
  · rcases n with _ | n
    · rw [teichmuller_coeff_zero, verschiebung_coeff_zero, add_zero]
    · rw [teichmuller_coeff_pos p _ _ n.succ_pos, verschiebung_coeff_succ, shift_coeff, zero_add,
        add_comm]
  · rcases m with _ | m
    · exact Or.inr (verschiebung_coeff_zero _)
    · exact Or.inl (teichmuller_coeff_pos p _ _ m.succ_pos)

variable [CharP R p]

theorem WittVector.frobenius_teichmuller (a : R) :
    frobenius (teichmuller p a) = teichmuller p (a ^ p) := by
  rw [frobenius_eq_map_frobenius, map_teichmuller, frobenius_def]

theorem WittVector.teichmuller_mul_coeff (a : R) (x : WittVector p R) (n : ℕ) :
    (teichmuller p a * x).coeff n = a ^ p ^ n * x.coeff n := by
  induction n generalizing a x with
  | zero => rw [mul_coeff_zero, teichmuller_coeff_zero, pow_zero, pow_one]
  | succ n ih =>
    conv_lhs => rw [← WittVector.teichmuller_add_verschiebung_shift x]
    rw [mul_add, ← map_mul, mul_comm (teichmuller p a), ← verschiebung_mul_frobenius,
      WittVector.frobenius_teichmuller]
    rw [coeff_add_of_disjoint (n + 1) _ _ fun m => ?_]
    · rw [teichmuller_coeff_pos p _ _ n.succ_pos, zero_add, verschiebung_coeff_succ, mul_comm,
        ih, shift_coeff, ← pow_mul, ← pow_succ', add_comm 1 n]
    · rcases m with _ | m
      · exact Or.inr (verschiebung_coeff_zero _)
      · exact Or.inl (teichmuller_coeff_pos p _ _ m.succ_pos)

theorem WittVector.mem_span_teichmuller_iff (b : R) (y : WittVector p R) :
    y ∈ Ideal.span {teichmuller p b} ↔ ∀ n, b ^ p ^ n ∣ y.coeff n := by
  constructor
  · intro h n
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 h
    rw [mul_comm, WittVector.teichmuller_mul_coeff]
    exact dvd_mul_right _ _
  · intro h
    choose w hw using h
    refine Ideal.mem_span_singleton'.2 ⟨WittVector.mk p w, ?_⟩
    ext n
    rw [mul_comm, WittVector.teichmuller_mul_coeff, coeff_mk, hw]

omit [CharP R p] in

theorem WittVector.span_teichmuller_pow (b : R) (N : ℕ) :
    Ideal.span {teichmuller p b} ^ N = Ideal.span {teichmuller p (b ^ N)} := by
  rw [Ideal.span_singleton_pow, map_pow]

theorem WittVector.mem_span_teichmuller_pow_iff (b : R) (N : ℕ) (y : WittVector p R) :
    y ∈ Ideal.span {teichmuller p b} ^ N ↔ ∀ n, b ^ (N * p ^ n) ∣ y.coeff n := by
  rw [WittVector.span_teichmuller_pow, WittVector.mem_span_teichmuller_iff]
  simp only [← pow_mul]

def WittVector.teichmullerSeries (a : ℕ → R) : WittVector p R :=
  WittVector.mk p fun n => a n ^ p ^ n

omit hp [CharP R p] in
theorem WittVector.teichmullerSeries_coeff (a : ℕ → R) (n : ℕ) :
    (WittVector.teichmullerSeries (p := p) a).coeff n = a n ^ p ^ n := rfl

theorem WittVector.coeff_sum_teichmuller_mul_pow (a : ℕ → R) (n j : ℕ) :
    (∑ i ∈ Finset.Iic n, teichmuller p (a i) * (p : WittVector p R) ^ i).coeff j =
      if j ≤ n then a j ^ p ^ j else 0 := by
  rw [WittVector.sum_coeff_eq_coeff_sum]
  · split_ifs with hj
    · rw [Finset.sum_eq_single_of_mem j (Finset.mem_Iic.2 hj) fun i _ hij =>
        teichmuller_mul_pow_coeff_of_ne _ (Ne.symm hij), teichmuller_mul_pow_coeff]
    · refine Finset.sum_eq_zero fun i hi => teichmuller_mul_pow_coeff_of_ne _ ?_
      rintro rfl
      exact hj (Finset.mem_Iic.1 hi)
  · refine fun m => ⟨fun ⟨i, _, hi⟩ ⟨k, _, hk⟩ => ?_⟩
    ext
    dsimp only [ne_eq, Set.mem_ofPred_eq] at hi hk ⊢
    rw [← Not.imp_symm (teichmuller_mul_pow_coeff_of_ne _) hi]
    exact Not.imp_symm (teichmuller_mul_pow_coeff_of_ne _) hk

variable [PerfectRing R p]

theorem WittVector.eq_teichmullerSeries_iff (a : ℕ → R) (x : WittVector p R) :
    x = WittVector.teichmullerSeries a ↔
      ∀ n, (p : WittVector p R) ^ (n + 1) ∣
        x - ∑ i ∈ Finset.Iic n, teichmuller p (a i) * (p : WittVector p R) ^ i := by
  have key : ∀ (n : ℕ) (d : WittVector p R), (p : WittVector p R) ^ (n + 1) ∣ d ↔
      ∀ j < n + 1, d.coeff j = 0 := fun n d => by
    rw [← Ideal.mem_span_singleton, mem_span_p_pow_iff_le_coeff_eq_zero]
  simp_rw [key, ← le_coeff_eq_iff_le_sub_coeff_eq_zero]
  constructor
  · rintro rfl n j hj
    rw [WittVector.coeff_sum_teichmuller_mul_pow, if_pos (Nat.lt_succ_iff.1 hj),
      WittVector.teichmullerSeries_coeff]
  · intro h
    ext j
    rw [h j j (Nat.lt_succ_self j), WittVector.coeff_sum_teichmuller_mul_pow, if_pos le_rfl,
      WittVector.teichmullerSeries_coeff]

theorem WittVector.dvd_sub_sum_teichmullerSeries (a : ℕ → R) (n : ℕ) :
    (p : WittVector p R) ^ (n + 1) ∣ WittVector.teichmullerSeries a -
      ∑ i ∈ Finset.Iic n, teichmuller p (a i) * (p : WittVector p R) ^ i :=
  (WittVector.eq_teichmullerSeries_iff a _).1 rfl n

theorem frobeniusEquiv_pow_apply (y : R) (n : ℕ) :
    ((_root_.frobeniusEquiv R p) ^ n) y = y ^ p ^ n := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, RingAut.mul_apply, ih, _root_.frobeniusEquiv_apply, frobenius_def, ← pow_mul,
      ← pow_succ']

theorem frobeniusEquiv_symm_pow_apply_pow (y : R) (n : ℕ) :
    ((_root_.frobeniusEquiv R p).symm ^ n) y ^ p ^ n = y := by
  rw [← frobeniusEquiv_pow_apply]
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ', RingAut.mul_apply, RingAut.mul_apply, RingEquiv.apply_symm_apply, ih]

theorem WittVector.teichmullerSeries_coeff_eq (x : WittVector p R) :
    WittVector.teichmullerSeries (fun n => ((_root_.frobeniusEquiv R p).symm ^ n) (x.coeff n)) =
      x := by
  ext n
  rw [WittVector.teichmullerSeries_coeff, frobeniusEquiv_symm_pow_apply_pow]

end WittGeneral

section Frobenius

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p] [PerfectRing R p]

theorem WittVector.teichmullerSeries_injective :
    Function.Injective (WittVector.teichmullerSeries (p := p) (R := R)) := by
  intro a b h
  funext n
  have := congrArg (fun x => x.coeff n) h
  simp only [WittVector.teichmullerSeries_coeff, ← frobeniusEquiv_pow_apply] at this
  exact (_root_.frobeniusEquiv R p ^ n).injective this

omit [CharP R p] [PerfectRing R p] in

theorem ringEquiv_pow_apply_symm_pow_apply {S : Type*} [Semiring S] (f : S ≃+* S) (n : ℕ)
    (y : S) : (f ^ n) ((f.symm ^ n) y) = y := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ', RingAut.mul_apply, RingAut.mul_apply, RingEquiv.apply_symm_apply, ih]

omit [CharP R p] [PerfectRing R p] in

theorem ringEquiv_symm_pow_apply_pow_apply {S : Type*} [Semiring S] (f : S ≃+* S) (n : ℕ)
    (y : S) : (f.symm ^ n) ((f ^ n) y) = y := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ', RingAut.mul_apply, RingAut.mul_apply, RingEquiv.symm_apply_apply, ih]

theorem WittVector.frobeniusEquiv_coeff (x : WittVector p R) (n : ℕ) :
    (WittVector.frobeniusEquiv p R x).coeff n = x.coeff n ^ p := by
  rw [WittVector.frobeniusEquiv_apply, coeff_frobenius_charP]

theorem WittVector.frobeniusEquiv_symm_coeff (x : WittVector p R) (n : ℕ) :
    ((WittVector.frobeniusEquiv p R).symm x).coeff n = (_root_.frobeniusEquiv R p).symm (x.coeff n) := by
  conv_rhs => rw [← RingEquiv.apply_symm_apply (WittVector.frobeniusEquiv p R) x,
    WittVector.frobeniusEquiv_coeff]
  rw [← frobenius_def, frobeniusEquiv_symm_apply_frobenius]

theorem WittVector.frobeniusEquiv_teichmuller (a : R) :
    WittVector.frobeniusEquiv p R (teichmuller p a) = teichmuller p (a ^ p) := by
  rw [WittVector.frobeniusEquiv_apply, WittVector.frobenius_teichmuller]

theorem WittVector.frobeniusEquiv_symm_teichmuller (a : R) :
    (WittVector.frobeniusEquiv p R).symm (teichmuller p a) =
      teichmuller p ((_root_.frobeniusEquiv R p).symm a) := by
  apply (WittVector.frobeniusEquiv p R).injective
  rw [RingEquiv.apply_symm_apply, WittVector.frobeniusEquiv_teichmuller, frobeniusEquiv_symm_pow_p]

theorem WittVector.frobeniusEquiv_symm_pow_teichmuller (a : R) (n : ℕ) :
    ((WittVector.frobeniusEquiv p R).symm ^ n) (teichmuller p a) =
      teichmuller p (((_root_.frobeniusEquiv R p).symm ^ n) a) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', RingAut.mul_apply, ih, WittVector.frobeniusEquiv_symm_teichmuller, pow_succ',
      RingAut.mul_apply]

theorem WittVector.frobeniusEquiv_pow_teichmuller (a : R) (n : ℕ) :
    (WittVector.frobeniusEquiv p R ^ n) (teichmuller p a) = teichmuller p (a ^ p ^ n) := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', RingAut.mul_apply, ih, WittVector.frobeniusEquiv_teichmuller, ← pow_mul,
      ← pow_succ]

theorem WittVector.frobeniusEquiv_teichmullerSeries (a : ℕ → R) :
    WittVector.frobeniusEquiv p R (WittVector.teichmullerSeries a) =
      WittVector.teichmullerSeries fun n => a n ^ p := by
  ext n
  rw [WittVector.frobeniusEquiv_coeff, WittVector.teichmullerSeries_coeff,
    WittVector.teichmullerSeries_coeff, ← pow_mul, ← pow_mul, mul_comm]

theorem WittVector.frobeniusEquiv_symm_teichmullerSeries (a : ℕ → R) :
    (WittVector.frobeniusEquiv p R).symm (WittVector.teichmullerSeries a) =
      WittVector.teichmullerSeries fun n => (_root_.frobeniusEquiv R p).symm (a n) := by
  apply (WittVector.frobeniusEquiv p R).injective
  rw [RingEquiv.apply_symm_apply, WittVector.frobeniusEquiv_teichmullerSeries]
  simp only [frobeniusEquiv_symm_pow_p]

end Frobenius

abbrev AInf (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] (p : ℕ) [Fact p.Prime] :=
  WittVector p (PreTilt (normInteger K) p)

namespace AInf

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]

local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)

variable (K p) in

instance isDomain : IsDomain (AInf K p) :=
  IsPerfectoidField.isDomain_wittVector_preTilt K p

theorem fontaineTheta_frobeniusEquiv_symm_pow_teichmuller (x : 𝒪♭) (n : ℕ) :
    θ (((φ).symm ^ n) (teichmuller p x)) =
      PreTilt.untilt (((_root_.frobeniusEquiv 𝒪♭ p).symm ^ n) x) := by
  rw [WittVector.frobeniusEquiv_symm_pow_teichmuller, fontaineTheta_teichmuller]

theorem fontaineTheta_frobeniusEquiv_symm_pow_teichmuller_pow (x : 𝒪♭) (n : ℕ) :
    θ (((φ).symm ^ n) (teichmuller p x)) ^ p ^ n = PreTilt.untilt x := by
  rw [fontaineTheta_frobeniusEquiv_symm_pow_teichmuller, RingAut.coe_pow,
    PreTilt.untilt_iterate_frobeniusEquiv_symm_pow]

theorem ker_fontaineTheta_comp_frobeniusEquiv_symm_pow {ξ : AInf K p}
    (hξ : RingHom.ker θ = Ideal.span {ξ}) (n : ℕ) :
    RingHom.ker ((fontaineTheta (normInteger K) p).comp ((φ).symm ^ n : AInf K p ≃+* AInf K p).toRingHom) =
      Ideal.span {(φ ^ n) ξ} := by
  ext x
  rw [RingHom.mem_ker, RingHom.comp_apply, ← RingHom.mem_ker, hξ, Ideal.mem_span_singleton,
    Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨(φ ^ n) c, ?_⟩
    rw [← map_mul, ← hc, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      ringEquiv_pow_apply_symm_pow_apply]
  · rintro ⟨c, rfl⟩
    refine ⟨((φ).symm ^ n) c, ?_⟩
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, map_mul,
      ringEquiv_symm_pow_apply_pow_apply]

end AInf

end GroundTheory.PAdicHodge
