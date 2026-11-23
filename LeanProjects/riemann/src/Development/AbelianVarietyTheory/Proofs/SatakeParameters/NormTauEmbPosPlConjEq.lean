import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrimeOfLiesOver

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical

namespace GlobalTheory.KerStd

open GlobalTheory.InertCompare GlobalTheory.Proof.IdempotentLatticeSequence

section General

variable {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]

theorem SamePrime.lt_one_imp {ρ ρ' : E →+* ℂ_[l]} (h : SamePrime ρ ρ') (x : E) (hx : ‖ρ x‖ < 1) : ‖ρ' x‖ < 1 := by
  have hone : ∀ (σ : E →+* ℂ_[l]) (a : 𝓞 E), ¬ ‖σ (a : E)‖ < 1 → ‖σ (a : E)‖ = 1 := fun σ a ha =>
    le_antisymm (norm_int_le σ a) (not_lt.1 ha)
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 E) :=
    ⟨primeOf ρ, primeOf_isPrime ρ, fun hb => by
      have := natCast_mem_primeOf ρ
      rw [hb, Ideal.mem_bot] at this
      exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast this)⟩
  obtain ⟨n, d, e | e⟩ := v.exists_primeCompl_mul_eq_or_mul_eq (K := E) x
  · have hd : ¬ ‖ρ ((d : 𝓞 E) : E)‖ < 1 := d.2
    have hd' : ¬ ‖ρ' ((d : 𝓞 E) : E)‖ < 1 := fun c => hd ((h _).2 c)
    have e' : x * ((d : 𝓞 E) : E) = (n : E) := e
    have hn : ‖ρ (n : E)‖ < 1 := by
      rw [← e', map_mul, norm_mul, hone ρ _ hd, mul_one]
      exact hx
    have hn' := (h n).1 hn
    rwa [← e', map_mul, norm_mul, hone ρ' _ hd', mul_one] at hn'
  · exfalso
    have hd : ¬ ‖ρ ((d : 𝓞 E) : E)‖ < 1 := d.2
    have e' : x * (n : E) = ((d : 𝓞 E) : E) := e
    apply hd
    rw [← e', map_mul, norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (norm_int_le ρ n)) hx

theorem SamePrime.norm_eq {ρ ρ' : E →+* ℂ_[l]} (h : SamePrime ρ ρ') (x : E) : ‖ρ x‖ = ‖ρ' x‖ := by
  let u : AbsoluteValue E ℝ := (NormedField.toAbsoluteValue ℂ_[l]).comp ρ.injective
  let w : AbsoluteValue E ℝ := (NormedField.toAbsoluteValue ℂ_[l]).comp ρ'.injective
  have hu (x) : u x = ‖ρ x‖ := rfl
  have hw (x) : w x = ‖ρ' x‖ := rfl
  have he : u.IsEquiv w := AbsoluteValue.isEquiv_iff_lt_one_iff.2 fun a =>
    ⟨SamePrime.lt_one_imp h a, SamePrime.lt_one_imp (fun b => (h b).symm) a⟩
  obtain ⟨c, hc, hce⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 he
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hn (σ : E →+* ℂ_[l]) : ‖σ (l : E)‖ = (l : ℝ)⁻¹ := by
    rw [map_natCast, ← Padic.norm_p, ← PadicComplex.norm_extends']
    simp
  have h1 : c = 1 := by
    have h2 := congrFun hce (l : E)
    simp only [hu, hw, hn] at h2
    have h3 : ((l : ℝ)⁻¹) ^ c = ((l : ℝ)⁻¹) ^ (1 : ℝ) := by rw [h2, Real.rpow_one]
    exact (Real.rpow_right_inj (by positivity) (by
      exact (inv_lt_one₀ (by positivity)).2 hl |>.ne)).1 h3
  have h4 := congrFun hce x
  simp only [hu, hw, h1, Real.rpow_one] at h4
  exact h4

end General

theorem norm_tauEmb_posPl_conj_eq : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), (IsResidueClassZero D p ∨ IsSg D p) → ∀ (z : Bool × HH D) (y : D.host.E), ‖tauEmb D lam (tauPl D (posPl D p z 1)) (D.host.conj y)‖ = ‖tauEmb D lam (tauPl D z) y‖ := by
  intro D p _ lam h z y
  have hcc : D.host.conj (D.host.conj y) = y := D.host.φ₀.injective (by
    rw [D.host.toHostAx.conjE_apply, D.host.toHostAx.conjE_apply, Complex.conj_conj])
  have h1 := SamePrime.norm_eq (samePrime_step D p lam h z) (D.host.conj y)
  have h2 : rhoC D lam (tauPl D z) (D.host.conj y) = rhoH D lam (tauPl D z) y := by
    change rhoH D lam (tauPl D z) (D.host.conj (D.host.conj y)) = _
    rw [hcc]
  rw [h2] at h1
  rw [← coe_rhoH, ← coe_rhoH]
  exact h1

end GlobalTheory.KerStd
