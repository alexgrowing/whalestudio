import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TowerOriginModel

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem chi_odd (H : Host E) :
    haveI : Fact H.d.Prime := ⟨H.d_prime⟩
    ((quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ)) (-1) = -1 := by
  haveI : Fact H.d.Prime := ⟨H.d_prime⟩
  have h4 : H.d % 4 = 3 := by have := H.d_mod; omega
  have h2 : ringChar (ZMod H.d) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; have := H.d_mod; omega
  rw [MulChar.ringHomComp_apply, quadraticChar_neg_one h2, ZMod.card, ZMod.χ₄_nat_three_mod_four h4]
  simp

theorem L_ne (H : Host E) :
    haveI : Fact H.d.Prime := ⟨H.d_prime⟩
    DirichletCharacter.LFunction
      ((quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ) : DirichletCharacter ℂ H.d) 1 ≠ 0 := by
  haveI : Fact H.d.Prime := ⟨H.d_prime⟩
  haveI : NeZero H.d := ⟨H.d_prime.ne_zero⟩
  apply DirichletCharacter.LFunction_apply_one_ne_zero
  intro h
  have h1 := chi_odd (E := E) H
  rw [h, MulChar.one_apply isUnit_one.neg] at h1
  norm_num at h1

theorem hostRd_pow : hostRd E ^ Module.finrank ℚ E = |(discr E : ℝ)| := by
  have hn : (Module.finrank ℚ E : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := E)).ne'
  unfold hostRd
  rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _), one_div, inv_mul_cancel₀ hn, Real.rpow_one]

theorem bad_exists (l : Tor.Level H) : ∃ bad : Finset ℕ, 2 ∈ bad ∧
    ∀ r : ℕ, r ∈ bad ↔ r.Prime ∧ (r : ℤ) ∣ 2 * discr E * l.M' := by
  have hM : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
  have hne : (2 * discr E * (l.M' : ℤ)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (NumberField.discr_ne_zero E)) (by exact_mod_cast hM)
  refine ⟨(2 * discr E * (l.M' : ℤ)).natAbs.primeFactors, ?_, ?_⟩
  · rw [Nat.mem_primeFactors]
    refine ⟨Nat.prime_two, ?_, Int.natAbs_ne_zero.mpr hne⟩
    rw [← Int.natCast_dvd]
    exact ⟨discr E * (l.M' : ℤ), by push_cast; ring⟩
  · intro r
    rw [Nat.mem_primeFactors, Int.natCast_dvd]
    constructor
    · rintro ⟨hp, hd, -⟩
      exact ⟨hp, hd⟩
    · rintro ⟨hp, hd⟩
      exact ⟨hp, hd, Int.natAbs_ne_zero.mpr hne⟩

variable {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {T : Top.RootTower (CMType H) (D.p + D.q)}

theorem sig_pos (o : TowerOrigin Y T) : 1 ≤ D.p ∧ 1 ≤ D.q := by
  have h1 := T.j_pos
  have h2 := T.j_lt
  rw [o.j_eq] at h1 h2
  omega

variable {O : Type} [CommRing O] {β : O →+* c.F} {Y' : Model Xo c β} {S : Finset ℕ}
  {RM : Top.RootModel (CMType H) (D.p + D.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))} {Fx : FixedData Y' Sys}

theorem finite_g (o : RootOrigin Y' S RM Fx) : letI := o.g.toAlgebra; Module.Finite Fx.Ωf RM.Ω := by
  letI := o.g.toAlgebra
  have hd : 0 < o.Fl.deg := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hpos, _⟩ := o.Fl.generic
    exact hpos
  exact Module.finite_of_finrank_pos (by rw [o.g_deg]; exact hd)

theorem pi_pt_ne (o : RootOrigin Y' S RM Fx) (x : o.Re.R.X) :
    ∃ a : ℂ, a ≠ 0 ∧ (fun i => o.Re.R.lift x x ⟨o.k₀, o.ix i⟩) = a • Fx.pt (o.Re.π x) := by
  obtain ⟨a, ha⟩ := o.π_pt x
  refine ⟨a, ?_, ha⟩
  rintro rfl
  obtain ⟨hnz, -⟩ := o.Re.R.mem x x (o.Re.R.mem_U x)
  obtain ⟨i, hi⟩ := hnz o.k₀
  apply hi
  have h := congrFun ha (o.ix.symm i)
  simp only [Equiv.apply_symm_apply, zero_smul, Pi.zero_apply] at h
  exact h

theorem genPt_eq (o : RootOrigin Y' S RM Fx) : genPt Fx.ξf = genPt o.𝔐.ξ₀ := by
  have hsub : ∀ (K : Type) [Field K] (p q : PrimeSpectrum K), p = q := fun K _ p q =>
    PrimeSpectrum.ext ((Ideal.eq_bot_of_prime p.asIdeal).trans (Ideal.eq_bot_of_prime q.asIdeal).symm)
  have h1 := o.g_over
  have h2 := o.𝔐.fn_over
  unfold Dominates at h2
  rw [h1] at h2
  have h3 : Fx.ξf ((spMap o.g) (IsLocalRing.closedPoint RM.Ω)) =
      o.𝔐.ξ₀ ((Spec.map (CommRingCat.ofHom o.𝔐.fn)) (IsLocalRing.closedPoint RM.Ω)) :=
    congrArg (fun φ => φ (IsLocalRing.closedPoint RM.Ω)) h2
  unfold genPt
  rw [hsub Fx.Ωf (IsLocalRing.closedPoint Fx.Ωf) ((spMap o.g) (IsLocalRing.closedPoint RM.Ω)),
    hsub o.𝔐.Ω₀ (IsLocalRing.closedPoint o.𝔐.Ω₀)
      ((Spec.map (CommRingCat.ofHom o.𝔐.fn)) (IsLocalRing.closedPoint RM.Ω))]
  exact h3

end GlobalTheory.CompanionTheory.Ar.TowerOriginModel
