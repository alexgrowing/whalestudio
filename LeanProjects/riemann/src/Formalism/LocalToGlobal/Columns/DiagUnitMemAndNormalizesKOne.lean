import Formalism.LocalToGlobal.Columns.ChainTwTopQ
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.TopLawQ
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.LocalProductMeasures.HilbertNinetyNormOne
import Formalism.LocalToGlobal.Columns.ChainTwFrA

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section TwK1b

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E))

def NormalizesKOne (n r c : ℕ) (g : Sp E n ≃ₗ[E] Sp E n) : Prop :=
  g ∈ LocE.JQ P (qOf P) r n 0 ∧ g ∈ stabL E n (LocE.sclLat P (qOf P) n (kOneLastExponents n c)) ∧
    g ∈ stabL E n (LocE.sclLat P (qOf P) n (twistedLevelExponent n c))

theorem twLamQB_red_one (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {kj n' N : ℕ} (hn : n' ≤ N) (y : Sp E N ≃ₗ[E] Sp E N)
    (hent : ∀ s t : Fin N, kj ≤ s.1 → s.1 < n' → kj ≤ t.1 → t.1 < n' →
      IntAt P (y (Pi.single t 1) s) ∧ redP P (y (Pi.single t 1) s) = if s = t then 1 else 0) :
    LocE.lamQB ξ kj n' (y : Sp E N →ₗ[E] Sp E N) = 1 := by
  classical
  have hlt : ∀ u : Fin (n' - kj), kj + u.1 < N := fun u => by have := u.2; omega
  have hlt' : ∀ u : Fin (n' - kj), kj + u.1 < n' := fun u => by have := u.2; omega
  have hM : ∀ s t : Fin (n' - kj), Loc.atN ((y : Sp E N →ₗ[E] Sp E N) (Loc.eN E N (kj + t.1))) (kj + s.1)
      = y (Pi.single (⟨kj + t.1, hlt t⟩ : Fin N) 1) ⟨kj + s.1, hlt s⟩ := by
    intro s t
    have he : Loc.eN E N (kj + t.1) = Pi.single (⟨kj + t.1, hlt t⟩ : Fin N) 1 := by
      funext l
      simp [Loc.eN, Pi.single_apply, Fin.ext_iff]
    rw [he]
    simp only [Loc.atN, dif_pos (hlt s)]
    rfl
  have hent' := fun s t : Fin (n' - kj) =>
    hent ⟨kj + s.1, hlt s⟩ ⟨kj + t.1, hlt t⟩ (by simp) (hlt' s) (by simp) (hlt' t)
  have hdet : redP P (Matrix.of fun s t : Fin (n' - kj) =>
      Loc.atN ((y : Sp E N →ₗ[E] Sp E N) (Loc.eN E N (kj + t.1))) (kj + s.1)).det = 1 := by
    rw [reduction_det_eq_det_reduction]
    · have h1 : (Matrix.of fun s t : Fin (n' - kj) =>
          redP P (Loc.atN ((y : Sp E N →ₗ[E] Sp E N) (Loc.eN E N (kj + t.1))) (kj + s.1))) = 1 := by
        ext s t
        rw [Matrix.of_apply, hM, (hent' s t).2, Matrix.one_apply]
        simp [Fin.ext_iff]
      rw [h1, Matrix.det_one]
    · intro s t
      rw [hM]
      exact (hent' s t).1
  unfold LocE.lamQB LocE.unitV
  split_ifs with hu
  · have hu1 : hu.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, hdet]; rfl)
    rw [hu1, map_one, Units.val_one, inv_one]
  · exact absurd (hdet ▸ isUnit_one) hu

theorem twRed0_of_val {w : E} (hw : P.valuation E w < 1) : IntAt P w ∧ redP P w = 0 := by
  classical
  obtain ⟨x, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) w
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hsE : algebraMap (𝓞 E) E s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
  obtain ⟨m, hm⟩ : ∃ m : ℕ, P.intValuation s = WithZero.exp (-(m : ℤ)) :=
    ⟨_, P.intValuation_if_neg hs0⟩
  obtain ⟨J, hJ⟩ := (P.intValuation_le_pow_iff_dvd s m).mp hm.le
  have hJP : ¬ J ≤ P.asIdeal := by
    intro hle
    have h2 : P.asIdeal ^ (m + 1) ∣ Ideal.span {s} := by
      rw [hJ, pow_succ]
      exact mul_dvd_mul_left _ (Ideal.dvd_iff_le.mpr hle)
    have h3 := (P.intValuation_le_pow_iff_dvd s (m + 1)).mpr h2
    rw [hm, WithZero.exp_le_exp] at h3
    push_cast at h3
    omega
  obtain ⟨t, htJ, htP⟩ := SetLike.not_le_iff_exists.mp hJP
  have htE : algebraMap (𝓞 E) E t ≠ 0 := by
    have ht0 : t ≠ 0 := fun h => htP (h ▸ P.asIdeal.zero_mem)
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)]
  have hx : x ∈ P.asIdeal ^ m := by
    rw [← P.intValuation_le_pow_iff_mem, ← hm, ← HeightOneSpectrum.valuation_of_algebraMap (K := E),
      ← HeightOneSpectrum.valuation_of_algebraMap (K := E)]
    change P.valuation E (algebraMap (𝓞 E) E x) ≤ P.valuation E (algebraMap (𝓞 E) E s)
    have e : algebraMap (𝓞 E) E x = (algebraMap (𝓞 E) E x / algebraMap (𝓞 E) E s) * algebraMap (𝓞 E) E s := by
      field_simp
    rw [e, map_mul]
    exact mul_le_of_le_one_left' hw.le
  have hxt : x * t ∈ Ideal.span {s} := by
    rw [hJ]
    exact Ideal.mul_mem_mul hx htJ
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hxt
  have hz' : algebraMap (𝓞 E) E x / algebraMap (𝓞 E) E s = algebraMap (𝓞 E) E z / algebraMap (𝓞 E) E t := by
    rw [div_eq_div_iff hsE htE, ← map_mul, ← map_mul, ← hz, mul_comm]
  have hrel : algebraMap (𝓞 E) E t * (algebraMap (𝓞 E) E x / algebraMap (𝓞 E) E s) = algebraMap (𝓞 E) E z := by
    rw [hz']
    field_simp
  have ht1 : P.valuation E (algebraMap (𝓞 E) E t) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.mpr htP
  have hzP : z ∈ P.asIdeal := by
    rw [← P.intValuation_lt_one_iff_mem, ← HeightOneSpectrum.valuation_of_algebraMap (K := E)]
    change P.valuation E (algebraMap (𝓞 E) E z) < 1
    rw [← hrel, map_mul, ht1, one_mul]
    exact hw
  refine ⟨⟨z, t, htP, hrel⟩, redP_eq P htP hrel ?_⟩
  rw [mul_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem]
  exact hzP

end TwK1b

end Formalism.L2.Col
