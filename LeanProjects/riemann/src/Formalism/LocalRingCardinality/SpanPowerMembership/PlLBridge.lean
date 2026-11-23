import Formalism.LocalRingCardinality.SpanPowerMembership.PlOver

noncomputable section

namespace Formalism.BasicNotions.Examples₂.PlOver

open NumberField IsDedekindDomain

variable (D : D7)

def plLEquiv (p : ℕ) [Fact p.Prime] :
    {v : HeightOneSpectrum (𝓞 D.what₂.LL) // ((p : ℕ) : 𝓞 D.what₂.LL) ∈ v.asIdeal} ≃
      {w : D.what₂.places.Pl // D.what₂.places.resChar w = p} :=
  (D.plEq.subtypeEquiv (fun w => resChar_eq_iff D p w)).symm

theorem plEq_plLEquiv (p : ℕ) [Fact p.Prime]
    (v : {v : HeightOneSpectrum (𝓞 D.what₂.LL) // ((p : ℕ) : 𝓞 D.what₂.LL) ∈ v.asIdeal}) :
    D.plEq (plLEquiv D p v).1 = v.1 := D.plEq.apply_symm_apply v.1

theorem wtLog_eq (p : ℕ) [hp : Fact p.Prime]
    (v : {v : HeightOneSpectrum (𝓞 D.what₂.LL) // ((p : ℕ) : 𝓞 D.what₂.LL) ∈ v.asIdeal}) :
    (eWL D.what₂.LL v.1 : ℝ) * Real.log (Ideal.absNorm v.1.asIdeal : ℝ) /
        (Real.log (p : ℝ) * (Module.finrank ℚ D.what₂.LL : ℝ)) =
      (D.what₂.places.ramIdx (plLEquiv D p v).1 : ℝ) *
        (padicValNat p (Ideal.absNorm (D.plEq (plLEquiv D p v).1).asIdeal) : ℝ) /
        (Module.finrank ℚ D.what₂.LL : ℝ) := by
  rw [D.ram_eq, plEq_plLEquiv]
  have := v.1.isPrime
  have : v.1.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := liesOver_of_mem _ v.2
  rw [Ideal.absNorm_eq_pow_inertiaDeg' (p := p) _ hp.out, padicValNat.prime_pow]
  have hlog : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hp.out.one_lt)).ne'
  have h0 : (Module.finrank ℚ D.what₂.LL : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  push_cast
  rw [Real.log_pow]
  field_simp

end Formalism.BasicNotions.Examples₂.PlOver
