import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import ReciprocityTheory.DualLattices.CyclicRecursionStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.XiMulNu
import ReciprocityTheory.DualLattices.AinfFacts

noncomputable section

open WittVector Ideal

namespace GlobalTheory.AinfXi

section Tilt

variable {p : ℕ} [hp : Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]

theorem coeff_pow_pow_zero (x : PreTilt O p) (n : ℕ) :
    PreTilt.coeff n x ^ p ^ n = PreTilt.coeff 0 x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, PreTilt.coeff_pow_p, ih]

theorem isUnit_of_coeff_zero {x : PreTilt O p} (h : IsUnit (PreTilt.coeff 0 x)) : IsUnit x := by
  have hn : ∀ n, IsUnit (PreTilt.coeff n x) := fun n =>
    (isUnit_pow_iff (pow_ne_zero n hp.out.ne_zero)).1 (by rw [coeff_pow_pow_zero]; exact h)
  have hu : ∀ n, (hn (n + 1)).unit ^ p = (hn n).unit := fun n =>
    Units.ext (by simp [PreTilt.coeff_pow_p])
  let f : ℕ → ModP O p := fun n => (((hn n).unit⁻¹ : (ModP O p)ˣ) : ModP O p)
  have hf : ∀ n, f (n + 1) ^ p = f n := fun n => by
    simp only [f]
    rw [← Units.val_pow_eq_pow_val, inv_pow, hu]
  let y : PreTilt O p := (⟨f, hf⟩ : Perfection (ModP O p) p)
  refine isUnit_iff_exists_inv.2 ⟨y, ?_⟩
  refine Perfection.ext fun n => ?_
  change PreTilt.coeff n (x * y) = PreTilt.coeff n 1
  rw [map_mul, map_one]
  change PreTilt.coeff n x * f n = 1
  exact IsUnit.mul_val_inv (hn n)

end Tilt

section Witt

variable {p : ℕ} [hp : Fact p.Prime] {R : Type} [CommRing R] [CharP R p] [PerfectRing R p]

theorem witt_isUnit (c : WittVector p R) (h : IsUnit (constantCoeff c)) : IsUnit c := by
  obtain ⟨u, hu⟩ := h
  have hmem : c * teichmuller p ((u⁻¹ : Rˣ) : R) - 1 ∈ span {(p : WittVector p R)} := by
    rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, map_mul, map_one, ← hu,
      constantCoeff_apply (x := teichmuller p _), teichmuller_coeff_zero, Units.mul_inv, sub_self]
  have hj := IsAdicComplete.le_jacobson_bot (span {(p : WittVector p R)}) hmem
  have h1 := (mem_jacobson_bot.1 hj) 1
  rw [mul_one, sub_add_cancel] at h1
  exact isUnit_of_mul_isUnit_left h1

end Witt

section Main

open GlobalTheory.Sandwich

variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]

theorem isDomain_ainf (hv : v.Integers O) : IsDomain (Ainf p O) := by
  have : IsDomain (PreTilt O p) := PreTilt.isDomain C v O hv p
  infer_instance

theorem isLocalRing_preTilt (hv : v.Integers O) : IsLocalRing (PreTilt O p) := by
  have : IsDomain (PreTilt O p) := PreTilt.isDomain C v O hv p
  haveI : IsLocalRing O := ReciprocityTheory.PGsh.Ainf.O_local O hv
  haveI : Nontrivial (ModP O p) := ReciprocityTheory.PGsh.Ainf.quot_nontrivial _ (by
    rw [Ne, Ideal.span_singleton_eq_top]; exact Fact.out)
  haveI : IsLocalRing (ModP O p) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (PreTilt.coeff 0 a) with h | h
  · exact Or.inl (isUnit_of_coeff_zero h)
  · exact Or.inr (isUnit_of_coeff_zero (by rwa [map_sub, map_one]))

theorem isLocalRing_ainf (hv : v.Integers O) : IsLocalRing (Ainf p O) := by
  haveI := isDomain_ainf (p := p) hv
  haveI := isLocalRing_preTilt (p := p) hv
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (constantCoeff a) with h | h
  · exact Or.inl (witt_isUnit a h)
  · exact Or.inr (witt_isUnit _ (by rwa [map_sub, map_one]))

variable (hv : v.Integers O) (ε : PreTilt O p) (hε : IsPrimitiveRoot (root ε).untilt p)
include hv hε

theorem ker_theta : RingHom.ker (fontaineTheta O p) = span {xi ε} :=
  ReciprocityTheory.PGsh.Ainf.ker_theta p O hv ε hε

theorem xi_nzd (y : Ainf p O) (hy : y * xi ε = 0) : y = 0 :=
  ReciprocityTheory.PGsh.Ainf.xi_nzd p O hv ε hε y hy

theorem dvd_of_dvd_mul_p (N : ℕ) (z : Ainf p O) (h : xi ε ^ N ∣ z * p) : xi ε ^ N ∣ z := by
  induction N generalizing z with
  | zero => simp
  | succ N ih =>
    obtain ⟨w, hw⟩ := h
    have h1 : fontaineTheta O p (z * p) = 0 := by
      rw [hw, map_mul, map_pow,
        show fontaineTheta O p (xi ε) = 0 from ReciprocityTheory.PGsh.Ainf.theta_xi p O hv ε hε,
        zero_pow (Nat.succ_ne_zero _), zero_mul]
    rw [map_mul, map_natCast] at h1
    have h0 : fontaineTheta O p z = 0 :=
      ReciprocityTheory.PGsh.Ainf.torsion_free p O hv 1 _ (by rw [pow_one]; exact h1)
    obtain ⟨z1, rfl⟩ := mem_span_singleton'.1 (by rw [← ker_theta hv ε hε]; exact h0)
    have h2 : (z1 * p - xi ε ^ N * w) * xi ε = 0 := by linear_combination hw
    obtain ⟨w', hw'⟩ := ih z1 ⟨w, sub_eq_zero.1 (xi_nzd hv ε hε _ h2)⟩
    exact ⟨w', by rw [hw']; ring⟩

theorem coeff_zero_eq_zero (x : Ainf p O) (hx : ∀ N, xi ε ^ N ∣ x) : constantCoeff x = 0 := by
  obtain ⟨⟨pf, hpf⟩, -, -, hX, -, -⟩ := ReciprocityTheory.PGsh.a0 p C v O hv
  obtain ⟨u, hu⟩ := ((hX ε hv hε).2.2.2 pf hpf).2
  have hu' : xi ε = u * ((p : Ainf p O) - teichmuller p pf) := hu
  have hxi : constantCoeff (xi ε) = constantCoeff (u : Ainf p O) * (-pf) := by
    rw [hu', map_mul, map_sub, map_natCast, CharP.cast_eq_zero, zero_sub,
      constantCoeff_apply (x := teichmuller p pf), teichmuller_coeff_zero]
  refine Perfection.ext fun n => ?_
  obtain ⟨w, hw⟩ := hx (p ^ n)
  change PreTilt.coeff n (constantCoeff x) = PreTilt.coeff n 0
  have h0 : PreTilt.coeff n (-pf) ^ p ^ n = 0 := by
    rw [coeff_pow_pow_zero, map_neg, ← PreTilt.mk_untilt_eq_coeff_zero, hpf, neg_eq_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  simp only [hw, hxi, map_mul, map_pow, mul_pow]
  rw [h0, mul_zero, zero_mul, map_zero]

theorem eq_zero_of_forall_dvd (x : Ainf p O) (hx : ∀ N, xi ε ^ N ∣ x) : x = 0 := by
  have key : ∀ k, ∀ x : Ainf p O, (∀ N, xi ε ^ N ∣ x) → (p : Ainf p O) ^ k ∣ x := by
    intro k
    induction k with
    | zero => intro x _; rw [pow_zero]; exact one_dvd _
    | succ k ih =>
      intro x hx
      have h0 := coeff_zero_eq_zero hv ε hε x hx
      rw [constantCoeff_apply] at h0
      obtain ⟨z, rfl⟩ := mem_span_singleton'.1 ((mem_span_p_iff_coeff_zero_eq_zero x).2 h0)
      obtain ⟨w, hw⟩ := ih z fun N => dvd_of_dvd_mul_p hv ε hε N z (hx N)
      exact ⟨w, by rw [hw]; ring⟩
  ext n
  have h := (mem_span_p_pow_iff_le_coeff_eq_zero x (n + 1)).1
    (mem_span_singleton.2 (key (n + 1) x hx)) n (Nat.lt_succ_self n)
  simpa using h

theorem exists_order (x : Ainf p O) (hx : x ≠ 0) :
    ∃ (N : ℕ) (y : Ainf p O), x = xi ε ^ N * y ∧ fontaineTheta O p y ≠ 0 := by
  classical
  have hex : ∃ N, ¬ xi ε ^ N ∣ x := by
    by_contra h
    exact hx (eq_zero_of_forall_dvd hv ε hε x fun N => by_contra fun h' => h ⟨N, h'⟩)
  have hM := Nat.find_spec hex
  have hM0 : Nat.find hex ≠ 0 := fun h => hM (by rw [h, pow_zero]; exact one_dvd _)
  obtain ⟨N, hN⟩ := Nat.exists_eq_succ_of_ne_zero hM0
  obtain ⟨y, hy⟩ : xi ε ^ N ∣ x := not_not.1 (Nat.find_min hex (by omega))
  refine ⟨N, y, hy, fun h0 => hM ?_⟩
  obtain ⟨y1, rfl⟩ := mem_span_singleton'.1 (by rw [← ker_theta hv ε hε]; exact h0)
  rw [hN, Nat.succ_eq_add_one]
  exact ⟨y1, by rw [hy]; ring⟩

end Main

section Statement

open ReciprocityTheory.PGsh.Up GlobalTheory.Sandwich Matrix

theorem ainf_local_xi_order : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ ε : PreTilt O p, IsPrimitiveRoot (root ε).untilt p → IsDomain (Ainf p O) ∧ IsLocalRing (Ainf p O) ∧ RingHom.ker (WittVector.fontaineTheta O p) = Ideal.span {xi ε} ∧ Function.Surjective (WittVector.fontaineTheta O p) ∧ WittVector.fontaineTheta O p (nu ε) ≠ 0 ∧ xi ε ≠ 0 ∧ (∀ x : Ainf p O, x ≠ 0 → ∃ (N : ℕ) (y : Ainf p O), x = xi ε ^ N * y ∧ WittVector.fontaineTheta O p y ≠ 0) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε
  haveI := isDomain_ainf (p := p) hv
  refine ⟨inferInstance, isLocalRing_ainf hv, ker_theta hv ε hε,
    ReciprocityTheory.PGsh.Ainf.theta_surj p O hv, ReciprocityTheory.PGsh.Ainf.theta_nu p O hv ε hε, fun h => ?_,
    fun x hx => exists_order hv ε hε x hx⟩
  exact one_ne_zero (xi_nzd hv ε hε 1 (by rw [h, mul_zero]))

end Statement

end GlobalTheory.AinfXi
