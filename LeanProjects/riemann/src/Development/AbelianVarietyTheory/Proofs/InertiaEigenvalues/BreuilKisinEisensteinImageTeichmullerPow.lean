import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.EisImage

theorem isUnit_of_constantCoeff {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [CharP O l] [PerfectRing O l]
    (c : WittVector l O) (h : IsUnit (WittVector.constantCoeff c)) : IsUnit c := by
  obtain ⟨u, hu⟩ := h
  have h1 : c * WittVector.teichmuller l ((u⁻¹ : Oˣ) : O) - 1 ∈ Ideal.span {(l : WittVector l O)} := by
    rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, map_mul, map_one, ← hu,
      WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero, Units.mul_inv, sub_self]
  have h2 := IsAdicComplete.le_jacobson_bot (Ideal.span {(l : WittVector l O)}) h1
  have h3 := Ideal.isUnit_of_sub_one_mem_jacobson_bot _ h2
  exact isUnit_of_mul_isUnit_left h3

theorem exists_eq {R : Type} [CommRing R] (l : R) (P : Polynomial R) (hm : P.Monic) (hd : 0 < P.natDegree)
    (hc : ∀ i < P.natDegree, l ∣ P.coeff i) (w : R) (h0 : P.coeff 0 = l * w) :
    ∃ G : Polynomial R, P = Polynomial.X ^ P.natDegree +
      Polynomial.C l * (Polynomial.C w + Polynomial.X * G) := by
  have h1 : Polynomial.C l ∣ (P - Polynomial.X ^ P.natDegree).divX := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    rw [Polynomial.coeff_divX, Polynomial.coeff_sub, Polynomial.coeff_X_pow]
    rcases lt_trichotomy (i + 1) P.natDegree with h | h | h
    · rw [if_neg h.ne, sub_zero]
      exact hc _ h
    · rw [if_pos h, h, hm.coeff_natDegree, sub_self]
      exact dvd_zero _
    · rw [if_neg h.ne', sub_zero, Polynomial.coeff_eq_zero_of_natDegree_lt h]
      exact dvd_zero _
  obtain ⟨G, hG⟩ := h1
  refine ⟨G, ?_⟩
  have h2 := Polynomial.X_mul_divX_add (P - Polynomial.X ^ P.natDegree)
  rw [hG, Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_neg hd.ne, sub_zero, h0, map_mul] at h2
  linear_combination -h2

theorem map_E_eq : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (O : Type) [CommRing O] [IsLocalRing O] [CharP O l] [PerfectRing O l] (ψ : OCb l →+* O), ¬ IsUnit (ψ bk.flat) → ∃ w : WittVector l O, IsUnit w ∧ WittVector.map ψ (bk.ev bk.E) = WittVector.teichmuller l (ψ bk.flat) ^ bk.Ep.natDegree + ((l : ℕ) : WittVector l O) * w := by
  intro l _ K bk O _ _ _ _ ψ hψ
  obtain ⟨w₀, hw₀⟩ := bk.coeff_zero
  obtain ⟨G, hG⟩ := exists_eq (l : Wq l bk.a) bk.Ep bk.monic bk.deg_pos bk.dvd_coeff w₀ hw₀
  let f : Polynomial (Wq l bk.a) →+* WittVector l O :=
    (WittVector.map ψ).comp (bk.ev.comp (Polynomial.coeToPowerSeries.ringHom))
  have hX : f Polynomial.X = WittVector.teichmuller l (ψ bk.flat) := by
    change WittVector.map ψ (bk.ev ((Polynomial.X : Polynomial (Wq l bk.a)) : (Wq l bk.a)⟦X⟧)) = _
    rw [Polynomial.coe_X, bk.ev_X, WittVector.map_teichmuller]
  refine ⟨f (Polynomial.C (w₀ : Wq l bk.a) + Polynomial.X * G), ?_, ?_⟩
  · apply isUnit_of_constantCoeff
    have hu : IsUnit (WittVector.constantCoeff (f (Polynomial.C (w₀ : Wq l bk.a)))) :=
      ((w₀.isUnit.map Polynomial.C).map f).map _
    rw [map_add, map_mul, hX, map_add, map_mul, WittVector.constantCoeff_apply (WittVector.teichmuller l _),
      WittVector.teichmuller_coeff_zero]
    by_contra hn
    have h1 : ψ bk.flat * WittVector.constantCoeff (f G) ∈ IsLocalRing.maximalIdeal O :=
      Ideal.mul_mem_right _ _ hψ
    have h2 := Ideal.sub_mem _ (show _ ∈ IsLocalRing.maximalIdeal O from hn) h1
    rw [add_sub_cancel_right] at h2
    exact h2 hu
  · have h1 := congrArg f hG
    rw [map_add, map_pow, hX, map_mul, map_natCast Polynomial.C, map_natCast f] at h1
    exact h1

end GlobalTheory.BSP.EisImage
