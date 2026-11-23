import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.FactsW
import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.IdempotentCalculationHolds
import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.GlueSmulSame

noncomputable section

namespace Formalism.L2.GenusGluing.Gen

open NumberField IsDedekindDomain Matrix Formalism.L2.Col
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem one_tmul_injective : Function.Injective (fun a : Formalism.L2.Herm.Af F => (1 : E) ⊗ₜ[F] a) := by
  have h := Algebra.TensorProduct.includeRight_injective (R := F) (A := E) (B := Formalism.L2.Herm.Af F)
    (algebraMap F E).injective
  intro a b hab
  apply h
  simpa [Algebra.TensorProduct.includeRight_apply] using hab

theorem eAt_eq (v : HeightOneSpectrum (𝓞 F)) :
    eAt E v = (1 : E) ⊗ₜ[F] ((Formalism.L2.DIV.idemAd (fun w => w = v) : Formalism.UG.intAd F) : Formalism.L2.Herm.Af F) := rfl

end SlopeTestRemainingChoices

theorem evaluationNeZero_holds : EAtNeZero := by
  intro F E _ _ _ _ _ v h
  rw [eAt_eq, ← TensorProduct.tmul_zero (R := F) (Formalism.L2.Herm.Af F) (1 : E)] at h
  have h2 := one_tmul_injective h
  have h3 : ((Formalism.L2.DIV.idemAd (fun w => w = v) : Formalism.UG.intAd F) : Formalism.L2.Herm.Af F) v =
      (0 : Formalism.L2.Herm.Af F) v := by rw [h2]
  rw [Formalism.L2.DIV.idemAd_pos (P := fun w => w = v) rfl] at h3
  exact one_ne_zero h3

theorem unitDichotomy_holds : UnitDich := by
  classical
  intro F E _ _ _ _ _ _ hc v u
  set σ := Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F) with hσ
  have hfix : σ (u * σ u) = u * σ u := by
    rw [map_mul, hσ, Formalism.L2.DIV.sigR_sigR, mul_comm]
  obtain ⟨a, ha⟩ := Formalism.L2.DIV.exists_adele_of_fixed hc _ hfix
  set idem : Formalism.L2.Herm.Af F := ((Formalism.L2.DIV.idemAd (fun w => w = v) : Formalism.UG.intAd F) : Formalism.L2.Herm.Af F)
    with hidem
  by_cases hav : a v = 0
  · left
    rw [ha, eAt_eq, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← TensorProduct.tmul_zero (R := F)
      (Formalism.L2.Herm.Af F) (1 : E)]
    congr 1
    apply FiniteAdeleRing.ext
    intro w
    show idem w * a w = 0
    by_cases hw : w = v
    · subst hw; rw [hav, mul_zero]
    · rw [hidem, Formalism.L2.DIV.idemAd_neg (P := fun x => x = v) hw, zero_mul]
  · right
    let f : ∀ w : HeightOneSpectrum (𝓞 F), w.adicCompletion F := fun w => if w = v then (a w)⁻¹ else 0
    have hf : ∀ᶠ w in Filter.cofinite, f w ∈ w.adicCompletionIntegers F := by
      filter_upwards [Filter.eventually_cofinite_ne v] with w hw
      simp only [f, if_neg hw]
      exact zero_mem _
    let a' : Formalism.L2.Herm.Af F := ⟨f, hf⟩
    have hprod : idem * a * a' = idem := by
      apply FiniteAdeleRing.ext
      intro w
      show idem w * a w * f w = idem w
      by_cases hw : w = v
      · subst hw
        simp only [f, if_pos rfl]
        rw [mul_assoc, mul_inv_cancel₀ hav, mul_one]
      · rw [hidem, Formalism.L2.DIV.idemAd_neg (P := fun x => x = v) hw, zero_mul, zero_mul]
    refine ⟨σ u * ((1 : E) ⊗ₜ[F] a'), ?_⟩
    rw [← mul_assoc u (σ u), ha, ← mul_assoc, eAt_eq, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul]
    simp only [one_mul]
    exact congrArg _ hprod

section Aux2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem exists_star_ne (hc : Formalism.BasicNotions.CMData F E) : ∃ θ : E, star θ ≠ θ := by
  by_contra h
  push Not at h
  have hb : Function.Bijective (algebraMap F E) :=
    ⟨(algebraMap F E).injective, fun x => by
      obtain ⟨y, hy⟩ := RingHom.mem_range.1 ((hc.fixed x).1 (h x))
      exact ⟨y, hy⟩⟩
  have h1 := Module.finrank_of_bijective_algebraMap hb
  rw [hc.deg2] at h1
  exact absurd h1 (by norm_num)

theorem exists_norm_one (hc : Formalism.BasicNotions.CMData F E) : ∃ t : E, star t * t = 1 ∧ star t - t ≠ 0 := by
  obtain ⟨θ, hθ⟩ := exists_star_ne hc
  set d : E := θ - star θ with hd_def
  have hd : star d = -d := by rw [hd_def, star_sub, star_star, neg_sub]
  have hd0 : d ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
  have h2 : (2 : E) ≠ 0 := two_ne_zero
  have hs : (1 + d) ≠ 0 := by
    intro h
    have h' : star (1 + d) = 0 := by rw [h, star_zero]
    rw [star_add, star_one, hd] at h'
    exact h2 (by linear_combination h + h')
  have hsb : (1 - d) ≠ 0 := by
    intro h
    have h' : star (1 - d) = 0 := by rw [h, star_zero]
    rw [star_sub, star_one, hd] at h'
    exact h2 (by linear_combination h + h')
  have e1 : star ((1 + d) * (1 - d)⁻¹) = (1 + d)⁻¹ * (1 - d) := by
    rw [star_mul, star_inv₀, star_sub, star_add, star_one, hd, sub_neg_eq_add, ← sub_eq_add_neg]
  have hsi : (1 + d) * (1 + d)⁻¹ = 1 := mul_inv_cancel₀ hs
  have hsbi : (1 - d) * (1 - d)⁻¹ = 1 := mul_inv_cancel₀ hsb
  refine ⟨(1 + d) * (1 - d)⁻¹, ?_, ?_⟩
  · rw [e1]
    have hinv : (1 + d)⁻¹ * (1 + d) = 1 := inv_mul_cancel₀ hs
    linear_combination (1 - d) * (1 - d)⁻¹ * hinv + hsbi
  · rw [e1]
    intro h
    have h4 : (4 : E) * d = 0 := by
      linear_combination (-((1 + d) * (1 - d))) * h + (1 - d) ^ 2 * hsi - (1 + d) ^ 2 * hsbi
    rcases mul_eq_zero.1 h4 with h5 | h5
    · exact absurd h5 (by norm_num)
    · exact hd0 h5

end Aux2

theorem shiftOne_holds : ShiftOne := by
  intro F E _ _ _ _ _ _ hc v α β ⟨α', hα⟩
  set e := eAt E v with he_def
  set σ := Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F) with hσ
  have hσι : ∀ t : E, σ (iA F E t) = iA F E (star t) := fun t => rfl
  set b := β * α' with hb
  have win : ∀ t : E, star t * t = 1 → (∃ u', e * ((iA F E t + b) * u') = e) →
      ∃ t : E, star t * t = 1 ∧ ∃ w, e * ((α * iA F E t + β) * w) = e := by
    rintro t ht ⟨u', hu'⟩
    refine ⟨t, ht, α' * u', ?_⟩
    rw [hb] at hu'
    linear_combination hu' + (iA F E t * u') * hα
  obtain ⟨t3, ht3, hne⟩ := exists_norm_one hc
  rcases unitDichotomy_holds F E hc v (iA F E 1 + b) with h1 | h1
  swap
  · exact win 1 (by rw [star_one, one_mul]) h1
  rcases unitDichotomy_holds F E hc v (iA F E (-1) + b) with h2 | h2
  swap
  · exact win (-1) (by rw [star_neg, star_one, neg_mul_neg, one_mul]) h2
  rcases unitDichotomy_holds F E hc v (iA F E t3 + b) with h3 | h3
  swap
  · exact win t3 ht3 h3
  exfalso
  rw [map_add, hσι, star_one, map_one] at h1
  rw [map_add, hσι, star_neg, star_one, map_neg, map_one] at h2
  rw [map_add, hσι] at h3
  set sb := σ b
  set T := iA F E t3
  set S := iA F E (star t3)
  have hTS : S * T = 1 := by rw [← map_mul, ht3, map_one]
  set k := iA F E (star t3 - t3)⁻¹
  have hk : (S - T) * k = 1 := by rw [← map_sub, ← map_mul, mul_inv_cancel₀ hne, map_one]
  set half := iA F E (2 : E)⁻¹
  have hh : half * 2 = 1 := by
    rw [show (2 : E ⊗[F] Formalism.L2.Herm.Af F) = iA F E 2 from (map_ofNat (iA F E) 2).symm, ← map_mul,
      inv_mul_cancel₀ (two_ne_zero : (2 : E) ≠ 0), map_one]
  have A : e * (b + sb) = 0 := by linear_combination half * h1 - half * h2 - (e * (b + sb)) * hh
  have B : e * (1 + b * sb) = 0 := by linear_combination half * h1 + half * h2 - (e * (1 + b * sb)) * hh
  have C : e * b * (S - T) = 0 := by linear_combination h3 - B - T * A - e * hTS
  have D : e * b = 0 := by linear_combination k * C - (e * b) * hk
  have hE : e = 0 := by linear_combination B - sb * D
  exact evaluationNeZero_holds F E v hE

end Formalism.L2.GenusGluing.Gen
