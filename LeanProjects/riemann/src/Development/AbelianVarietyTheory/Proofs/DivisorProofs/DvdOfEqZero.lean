import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuDvdOfDvdIterates

set_option autoImplicit false
noncomputable section
open Polynomial WittVector GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta

namespace GlobalTheory.BRing

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem frob_congr (x : Ainf p O) : ∃ z, frobenius x = x ^ p + (p : Ainf p O) * z := by
  have h : frobenius x - x ^ p ∈ Ideal.span {(p : Ainf p O)} := by
    rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, map_pow,
      WittVector.constantCoeff_apply, WittVector.constantCoeff_apply, coeff_frobenius_charP, sub_self]
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp h
  exact ⟨y, by linear_combination -hy⟩

theorem frob_teich (r : PreTilt O p) :
    frobenius (teichmuller p r : Ainf p O) = teichmuller p (r ^ p) := by
  rw [frobenius_eq_map_frobenius, map_teichmuller, frobenius_def]

theorem frob_nu (ε : PreTilt O p) : frobenius (nu ε) = mu ε := by
  rw [nu, mu, map_sub, map_one, frob_teich, root, frobeniusEquiv_symm_pow_p]

theorem frob_mu (ε : PreTilt O p) : frobenius (mu ε) = mu ε * frobenius (xi ε) := by
  rw [show frobenius (mu ε) = frobenius (xi ε * nu ε) by rw [xi_mul_nu], map_mul, frob_nu,
    mul_comm]

theorem frob_xi (ε : PreTilt O p) : ∃ d, frobenius (xi ε) = p + mu ε * d := by
  have h : frobenius (xi ε) = ∑ i ∈ Finset.range p, (teichmuller p ε : Ainf p O) ^ i := by
    rw [xi, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_pow, frob_teich, root, frobeniusEquiv_symm_pow_p]
  have hd : ∀ i : ℕ, mu ε ∣ (teichmuller p ε : Ainf p O) ^ i - 1 := fun i => by
    rw [mu]; simpa using sub_dvd_pow_sub_pow (teichmuller p ε : Ainf p O) 1 i
  choose d hd using hd
  refine ⟨∑ i ∈ Finset.range p, d i, ?_⟩
  rw [h, Finset.mul_sum, ← Finset.sum_congr rfl fun i _ => hd i]
  simp [Finset.sum_sub_distrib]

theorem theta_mu {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) :
    fontaineTheta O p (mu ε) = 0 := by
  rw [mu, map_sub, fontaineTheta_teichmuller, map_one, sub_eq_zero]
  exact hε.zeta_zero

variable (ε : PreTilt O p)

def rel : Ideal (Ainf p O)[X] := Ideal.span {C (p : Ainf p O) * X - C (mu ε), X ^ 2}

abbrev BR : Type := (Ainf p O)[X] ⧸ rel ε

def a : Ainf p O →+* BR ε := (Ideal.Quotient.mk (rel ε)).comp C

def τ : BR ε := Ideal.Quotient.mk (rel ε) X

theorem p_τ : (p : BR ε) * τ ε = a ε (mu ε) := by
  rw [τ, a, RingHom.comp_apply, ← map_natCast (Ideal.Quotient.mk (rel ε)), ← map_mul,
    ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, ← map_natCast C]
  exact Ideal.subset_span (Set.mem_insert _ _)

theorem τ_sq : τ ε * τ ε = 0 := by
  rw [τ, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, ← sq]
  exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)

theorem a_natCast (n : ℕ) : a ε n = n := map_natCast _ n

def θ {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) : BR ε →+* O :=
  Ideal.Quotient.lift (rel ε) (eval₂RingHom (fontaineTheta O p) 0) (fun f hf => by
    have h : rel ε ≤ RingHom.ker (eval₂RingHom (fontaineTheta O p) 0) := by
      refine Ideal.span_le.2 ?_
      rintro g (rfl | rfl) <;> simp [theta_mu hε]
    exact (RingHom.mem_ker).1 (h hf))

theorem θ_a {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) (x : Ainf p O) :
    θ hε (a ε x) = fontaineTheta O p x := by
  rw [θ, a, RingHom.comp_apply, Ideal.Quotient.lift_mk]; simp

theorem θ_τ {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) : θ hε (τ ε) = 0 := by
  rw [θ, τ, Ideal.Quotient.lift_mk]; simp

def σ : BR ε →+* BR ε :=
  Ideal.Quotient.lift (rel ε) (eval₂RingHom ((a ε).comp frobenius) (τ ε * a ε (frobenius (xi ε))))
    (fun f hf => by
      have h : rel ε ≤ RingHom.ker (eval₂RingHom ((a ε).comp frobenius)
          (τ ε * a ε (frobenius (xi ε)))) := by
        refine Ideal.span_le.2 ?_
        rintro g (rfl | rfl)
        · simp only [SetLike.mem_coe, RingHom.mem_ker, coe_eval₂RingHom, eval₂_sub, eval₂_mul,
            eval₂_C, eval₂_X, eval₂_natCast, RingHom.comp_apply, map_natCast]
          rw [frob_mu, map_mul, ← p_τ]; ring
        · simp only [SetLike.mem_coe, RingHom.mem_ker, coe_eval₂RingHom, eval₂_X_pow]
          rw [mul_pow, sq (τ ε), τ_sq, zero_mul]
      exact (RingHom.mem_ker).1 (h hf))

theorem σ_a (x : Ainf p O) : σ ε (a ε x) = a ε (frobenius x) := by
  simp [σ, a, Ideal.Quotient.lift_mk]

theorem σ_τ : σ ε (τ ε) = τ ε * a ε (frobenius (xi ε)) := by
  simp [σ, τ, Ideal.Quotient.lift_mk]

abbrev BQ : Type := Localization.Away (p : BR ε)

def s : BQ ε →+* BQ ε :=
  IsLocalization.map (M := Submonoid.powers (p : BR ε)) (T := Submonoid.powers (p : BR ε))
    (BQ ε) (σ ε) (by
      rintro _ ⟨n, rfl⟩
      exact ⟨n, by rw [map_pow, map_natCast]⟩)

theorem s_alg (b : BR ε) : s ε (algebraMap (BR ε) (BQ ε) b) = algebraMap (BR ε) (BQ ε) (σ ε b) :=
  IsLocalization.map_eq _ _

theorem gen (b : BR ε) : ∃ x y, b = a ε x + τ ε * a ε y := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
  refine ⟨f.coeff 0, f.divX.coeff 0, ?_⟩
  have h1 := divX_mul_X_add f
  have h2 := divX_mul_X_add f.divX
  have hX : Ideal.Quotient.mk (rel ε) (X ^ 2) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  conv_lhs => rw [← h1, ← h2]
  simp only [map_add, map_mul, a, τ, RingHom.comp_apply]
  have : Ideal.Quotient.mk (rel ε) f.divX.divX * Ideal.Quotient.mk (rel ε) X *
      Ideal.Quotient.mk (rel ε) X = 0 := by
    rw [mul_assoc, ← map_mul, ← sq, hX, mul_zero]
  linear_combination this

section Faithful

variable {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} [Algebra O C]
  {ε : PreTilt O p}

theorem prim (hε : IsPrimitiveSystem ε) : IsPrimitiveRoot (root ε).untilt p := by
  simpa [zeta] using hε 1

theorem eps_ne (hv : v.Integers O) (hε : IsPrimitiveSystem ε) : ε - 1 ≠ 0 := by
  rw [← GlobalTheory.MuDivides.constantCoeff_mu, WittVector.constantCoeff_apply]
  exact (GlobalTheory.DetInv.mu_coeff_zero_ne_zero p C v O hv ε (prim hε)).1

theorem mu_ne (hv : v.Integers O) (hε : IsPrimitiveSystem ε) : mu ε ≠ 0 :=
  (GlobalTheory.DetInv.mu_coeff_zero_ne_zero p C v O hv ε (prim hε)).2.1

theorem mu_dvd (hv : v.Integers O) (hε : IsPrimitiveSystem ε) (w : Ainf p O)
    (h : mu ε ∣ (p : Ainf p O) * w) : mu ε ∣ w :=
  GlobalTheory.MuDivides.dvd_of_dvd_p_mul hv ε (eps_ne hv hε) w h

theorem mu_sq_dvd (hv : v.Integers O) (hε : IsPrimitiveSystem ε) (w : Ainf p O)
    (h : mu ε ^ 2 ∣ (p : Ainf p O) * w) : mu ε ^ 2 ∣ w := by
  haveI := GlobalTheory.AinfXi.isDomain_ainf (p := p) hv
  obtain ⟨w', rfl⟩ := mu_dvd hv hε w (dvd_trans (dvd_pow_self _ two_ne_zero) h)
  rw [sq, mul_left_comm] at h
  rw [sq]
  exact mul_dvd_mul_left _ (mu_dvd hv hε w' ((mul_dvd_mul_iff_left (mu_ne hv hε)).1 h))

theorem dvd_of_eq_zero (x y : Ainf p O) (h : a ε x + τ ε * a ε y = 0) :
    mu ε ^ 2 ∣ (p : Ainf p O) * x + mu ε * y := by
  have hm : C x + C y * X ∈ rel ε := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← h, map_add, map_mul, mul_comm]; rfl
  obtain ⟨h1, h2, he⟩ := Ideal.mem_span_pair.1 hm
  have he' : C x + C y * X = h1 * C (p : Ainf p O) * X - h1 * C (mu ε) + h2 * X ^ 2 := by
    rw [← he]; ring
  have e0 := congrArg (fun f => Polynomial.coeff f 0) he'
  have e1 := congrArg (fun f => Polynomial.coeff f 1) he'
  simp only [coeff_add, coeff_sub, coeff_C_zero, coeff_mul_X_zero, coeff_mul_C,
    coeff_mul_X_pow', coeff_C_succ] at e0 e1
  rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_mul_X, coeff_mul_X, coeff_mul_C, coeff_C_zero] at e1
  simp only [coeff_C_succ, zero_add, Nat.one_lt_ofNat, if_neg (by norm_num : ¬ (2 ≤ 1)),
    if_neg (by norm_num : ¬ (2 ≤ 0)), add_zero, zero_sub] at e0 e1
  refine ⟨-(h1.coeff 1), ?_⟩
  rw [e0, e1]; ring

theorem eq_zero_of_dvd (hv : v.Integers O) (hε : IsPrimitiveSystem ε) (x y : Ainf p O)
    (h : mu ε ^ 2 ∣ (p : Ainf p O) * x + mu ε * y) : a ε x + τ ε * a ε y = 0 := by
  haveI := GlobalTheory.AinfXi.isDomain_ainf (p := p) hv
  obtain ⟨z, hz⟩ := h
  obtain ⟨x', rfl⟩ := mu_dvd hv hε x ⟨-y + mu ε * z, by linear_combination hz⟩
  have hy : y = mu ε * z - p * x' := by
    have : mu ε * (y - (mu ε * z - p * x')) = 0 := by linear_combination hz
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (mu_ne hv hε))
  subst hy
  have h1 := p_τ ε
  have h2 := τ_sq ε
  simp only [map_mul, map_sub, map_natCast]
  rw [← h1]
  linear_combination (↑p * a ε z) * h2

theorem torsion_free (hv : v.Integers O) (hε : IsPrimitiveSystem ε) (b : BR ε)
    (h : (p : BR ε) * b = 0) : b = 0 := by
  obtain ⟨x, y, rfl⟩ := gen ε b
  refine eq_zero_of_dvd hv hε x y (mu_sq_dvd hv hε _ ?_)
  have := dvd_of_eq_zero (ε := ε) (p * x) (p * y) (by
    rw [map_mul, map_mul, a_natCast]; linear_combination h)
  rw [show (p : Ainf p O) * (p * x + mu ε * y) = p * (p * x) + mu ε * (p * y) by ring]
  exact this

end Faithful

end GlobalTheory.BRing
