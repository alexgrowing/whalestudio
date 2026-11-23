import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.TwoSplitIdem
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.EqOfLeOfAbsNormEq

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {R : Ranks}

def alphaH (H : Host R) : H.E := (1 + H.sqrtMinusD) / 2

theorem alphaH_sq (H : Host R) :
    alphaH H * (alphaH H - 1) = -(((H.d + 1) / 4 : ℕ) : H.E) := by
  have hd16 : H.d % 16 = 7 := H.hyp.2.2.2.1
  have hb : H.sqrtMinusD ^ 2 = -(H.d : H.E) := H.sqd_sq
  have h4 : ((H.d + 1) / 4 : ℕ) * 4 = H.d + 1 := by omega
  have h4' : ((((H.d + 1) / 4 : ℕ) : H.E)) * 4 = (H.d : H.E) + 1 := by exact_mod_cast h4
  unfold alphaH
  linear_combination (1 / 4 : H.E) * hb + (1 / 4 : H.E) * h4'

theorem alphaH_integral (H : Host R) : IsIntegral ℤ (alphaH H) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (((H.d + 1) / 4 : ℕ) : ℤ), by monicity!, ?_⟩
  have h := alphaH_sq H
  rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
    algebraMap_int_eq, eq_intCast, Int.cast_natCast]
  linear_combination h

theorem star_alphaH (H : Host R) : (letI := H.cmStar; star (alphaH H)) = 1 - alphaH H := by
  rw [Formalism.BasicNotions.Examples₂.star_eq_conj]
  unfold alphaH
  rw [map_div₀, map_add, map_one, Formalism.MainNotions.UnusedSlot33.HK.conj_b]
  have h2 : H.conj (2 : H.E) = 2 := map_ofNat _ 2
  rw [h2]
  ring

theorem twoSplits (D : D7) : TwoSplits D := by
  intro P h2 hconj
  obtain ⟨a, ha⟩ : ∃ a : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E a = alphaH D.host :=
    ⟨⟨alphaH D.host, alphaH_integral D.host⟩, rfl⟩
  have inj := FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E
  have coe : ∀ x : 𝓞 D.host.E, (x : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E x := fun _ => rfl
  have hP := P.isPrime
  have hd16 : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  have hprod : a * (a - 1) ∈ P.asIdeal := by
    have heven : ((D.host.d + 1) / 4 : ℕ) = 2 * (((D.host.d + 1) / 4 : ℕ) / 2) := by omega
    have hk : ((((D.host.d + 1) / 4 : ℕ) : D.host.E)) = 2 * ((((D.host.d + 1) / 4 / 2 : ℕ) : D.host.E)) := by
      conv_lhs => rw [heven]
      push_cast; ring
    have he : a * (a - 1) = 2 * (-((((D.host.d + 1) / 4 / 2 : ℕ) : 𝓞 D.host.E))) := by
      apply inj
      have h := alphaH_sq D.host
      rw [hk] at h
      simp only [map_mul, map_sub, map_one, map_neg, map_natCast, map_ofNat, ha]
      linear_combination h
    rw [he]
    exact P.asIdeal.mul_mem_right _ h2
  have hstar : ∀ x : 𝓞 D.host.E, x ∈ P.asIdeal →
      ∃ c' ∈ P.asIdeal, algebraMap (𝓞 D.host.E) D.host.E c' = star (algebraMap (𝓞 D.host.E) D.host.E x) := hconj
  have hsa := star_alphaH D.host
  rcases hP.mem_or_mem hprod with hm | hm
  · obtain ⟨c', hc', hc'e⟩ := hstar a hm
    have h1 : a + c' = 1 := by
      apply inj
      rw [map_add, map_one, hc'e, ha, hsa]; ring
    exact hP.ne_top ((Ideal.eq_top_iff_one _).2 (h1 ▸ P.asIdeal.add_mem hm hc'))
  · obtain ⟨c', hc', hc'e⟩ := hstar _ hm
    have h1 : -c' - (a - 1) = 1 := by
      apply inj
      rw [map_sub, map_neg, map_sub, map_one, hc'e, map_sub, map_one, star_sub, star_one, ha, hsa]; ring
    exact hP.ne_top ((Ideal.eq_top_iff_one _).2 (h1 ▸ P.asIdeal.sub_mem (P.asIdeal.neg_mem hc') hm))

end Formalism.IndefR.Fin

end
