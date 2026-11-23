import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ConstantCoeffResidueUXPow
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DvdCoeffsOfMemSpanDistinguished
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DivAddLogbLeEightMulErrorScale

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries
namespace ArcLengthThreeFiltration

open PowerSeries

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

theorem mem_pair_X_iff (a : O) (f : O⟦X⟧) (B : ℕ) :
    f ∈ Ideal.span {C a, (X : O⟦X⟧) ^ B} ↔ ∀ j < B, a ∣ coeff j f := by
  constructor
  · intro hf j hj
    obtain ⟨u, w, huw⟩ := Ideal.mem_span_pair.mp hf
    rw [← huw, map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', if_neg (by omega), add_zero]
    exact dvd_mul_left _ _
  · intro h
    choose c hc using h
    set g : O⟦X⟧ := PowerSeries.mk fun j => if hj : j < B then c j hj else 0 with hg
    have hdvd : (X : O⟦X⟧) ^ B ∣ f - C a * g := by
      rw [PowerSeries.X_pow_dvd_iff]
      intro m hm
      rw [map_sub, PowerSeries.coeff_C_mul, hg, PowerSeries.coeff_mk, dif_pos hm, ← hc m hm, sub_self]
    obtain ⟨w, hw⟩ := hdvd
    rw [Ideal.mem_span_pair]
    exact ⟨g, w, by linear_combination (-1 : O⟦X⟧) * hw⟩

private theorem exists_unit_natCast_eq_mul_uniformizer_pow_eO {l : ℕ} {ϖ : O} (hϖ : Irreducible ϖ) (hl0 : (l : O) ≠ 0) :
    ∃ u : Oˣ, (l : O) = ↑u * ϖ ^ eO (O := O) l := by
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hl0 hϖ
  have hl' : (l : O) = ↑u⁻¹ * ϖ ^ n := by
    rw [← hu, mul_comm (l : O), ← mul_assoc, Units.inv_mul, one_mul]
  have he : eO (O := O) l = n := by
    unfold eO
    rw [IsDiscreteValuationRing.addVal_def (l : O) u⁻¹ hϖ n hl']
    simp
  exact ⟨u⁻¹, by rw [he]; exact hl'⟩

theorem pair_l_eq {l : ℕ} [Fact l.Prime] {ϖ : O} (hϖ : Irreducible ϖ) (hl0 : (l : O) ≠ 0) (s : ℕ)
    (g : O⟦X⟧) :
    Ideal.span {(C (l : O) : O⟦X⟧) ^ s, g} = Ideal.span {C ϖ ^ (eO (O := O) l * s), g} := by
  obtain ⟨u, hu⟩ := exists_unit_natCast_eq_mul_uniformizer_pow_eO hϖ hl0
  have hC : (C (l : O) : O⟦X⟧) ^ s = C ϖ ^ (eO (O := O) l * s) * C ((u : O) ^ s) := by
    rw [hu, map_mul, map_pow, map_pow, mul_pow, ← pow_mul, mul_comm]
  rw [Ideal.span_insert, Ideal.span_insert, hC,
    Ideal.span_singleton_mul_right_unit (((Units.isUnit u).pow s).map C)]

theorem eO_pos {l : ℕ} [Fact l.Prime] {ϖ : O} (hϖ : Irreducible ϖ) (hl0 : (l : O) ≠ 0)
    (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) : 1 ≤ eO (O := O) l := by
  obtain ⟨u, hu⟩ := exists_unit_natCast_eq_mul_uniformizer_pow_eO hϖ hl0
  by_contra h0
  have h0' : eO (O := O) l = 0 := by omega
  rw [h0', pow_zero, mul_one] at hu
  have hn := (IsLocalRing.mem_maximalIdeal _).mp hl
  rw [hu] at hn
  exact hn (Units.isUnit u)

theorem cancel_l {l : ℕ} [Fact l.Prime] {ϖ : O} (hϖ : Irreducible ϖ) (hl0 : (l : O) ≠ 0) (k s B : ℕ)
    (hks : k ≤ s) (f : O⟦X⟧)
    (h : C (l : O) ^ k * f ∈ Ideal.span {C ϖ ^ (eO (O := O) l * s), (X : O⟦X⟧) ^ B}) :
    f ∈ Ideal.span {C ϖ ^ (eO (O := O) l * (s - k)), (X : O⟦X⟧) ^ B} := by
  obtain ⟨u, hu⟩ := exists_unit_natCast_eq_mul_uniformizer_pow_eO hϖ hl0
  rw [← map_pow] at h ⊢
  rw [mem_pair_X_iff] at h ⊢
  intro j hj
  have hj' := h j hj
  rw [← map_pow, PowerSeries.coeff_C_mul, hu] at hj'
  have hpow : ϖ ^ (eO (O := O) l * s) = ϖ ^ (eO (O := O) l * (s - k)) * ϖ ^ (eO (O := O) l * k) := by
    rw [← pow_add, ← mul_add, Nat.sub_add_cancel hks]
  have hrw : ((u : O) * ϖ ^ eO (O := O) l) ^ k * coeff j f =
      (((u ^ k : Oˣ) : O) * coeff j f) * ϖ ^ (eO (O := O) l * k) := by
    rw [Units.val_pow_eq_pow_val, mul_pow, ← pow_mul]
    ring
  rw [hpow, hrw] at hj'
  have hne : ϖ ^ (eO (O := O) l * k) ≠ 0 := pow_ne_zero _ hϖ.ne_zero
  exact Units.dvd_mul_left.mp ((mul_dvd_mul_iff_right hne).mp hj')

theorem content_notMem {l : ℕ} [Fact l.Prime] (P : PhiData O l) (σ A S y b₁ η s₁ : ℕ)
    (hs : 2 * σ < s₁) (hk : A + s₁ - 1 < b₁ - η) (hy1 : 1 ≤ y)
    (hc2 : ¬ (((s₁ : ℝ) - 2 * σ) ≤ max 0 ((y : ℝ) - ((b₁ - η - (A + s₁ - 1) : ℕ) : ℝ) / l + 2 + Real.logb l y))) :
    C (l : O) ^ (2 * σ) * (X - C (l : O)) ^ A * X ^ S * P.p 1 ^ y ∉
      Ideal.span {(C (l : O) : O⟦X⟧) ^ s₁, (X : O⟦X⟧) ^ (b₁ + S - η)} := by
  intro hmem
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hs1 : 1 ≤ s₁ := by omega
  set t := s₁ - 2 * σ with ht
  have ht1 : 1 ≤ t := by omega
  set B := b₁ - η - (A + s₁ - 1) with hBdef
  have hB : 1 ≤ B := by omega
  have hre : C (l : O) ^ (2 * σ) * (X - C (l : O)) ^ A * X ^ S * P.p 1 ^ y =
      C (l : O) ^ (2 * σ) * ((X - C (l : O)) ^ A * X ^ S * P.p 1 ^ y) := by ring
  rw [hre, pair_l_eq hϖ P.hl0 s₁] at hmem
  have hG := cancel_l hϖ P.hl0 (2 * σ) s₁ (b₁ + S - η) (by omega) _ hmem
  rw [← ht, ← pair_l_eq hϖ P.hl0 t] at hG
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp (PhiData.X_pow_mem_span_q_pow_l_pow (l := l) hϖ A t ht1)
  have hK : (X : O⟦X⟧) ^ (A + t - 1 + S) * P.p 1 ^ y ∈
      Ideal.span {(C (l : O) : O⟦X⟧) ^ t, (X : O⟦X⟧) ^ (b₁ + S - η)} := by
    have hexp : (X : O⟦X⟧) ^ (A + t - 1 + S) * P.p 1 ^ y =
        a * ((X - C (l : O)) ^ A * X ^ S * P.p 1 ^ y) + (b * X ^ S * P.p 1 ^ y) * C (l : O) ^ t := by
      rw [pow_add, ← hab]
      ring
    rw [hexp]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hG) (Ideal.mul_mem_left _ _ ?_)
    exact Ideal.subset_span (Set.mem_insert _ _)
  rw [← map_pow, mem_pair_X_iff] at hK
  have hP : P.p 1 ^ y ∈ Ideal.span {(C (l : O) : O⟦X⟧) ^ t, (X : O⟦X⟧) ^ B} := by
    rw [← map_pow, mem_pair_X_iff]
    intro j hj
    have h2 := hK (j + (A + t - 1 + S)) (by omega)
    rwa [PowerSeries.coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel] at h2
  rw [pair_l_eq hϖ P.hl0 t] at hP
  have hdX : IsDist ((X : O⟦X⟧) ^ B) := by
    unfold IsDist
    rw [map_pow, PowerSeries.map_X]
    exact pow_ne_zero _ PowerSeries.X_ne_zero
  have hle := (mem_iff_le_cont hϖ hdX _ _).mp hP
  obtain ⟨hne, hbd⟩ := PhiData.constant_le_rpow_of_three_le P hϖ B y hB hy1
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
  rw [← hn] at hle hbd
  have hle' : eO (O := O) l * t ≤ n := by exact_mod_cast hle
  have he := eO_pos hϖ P.hl0 P.hl
  have hle'' : ((eO (O := O) l : ℝ) * t) ≤ (eO (O := O) l : ℝ) *
      max 0 ((y : ℝ) - B / l + 2 + Real.logb l y) := by
    have : ((eO (O := O) l * t : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hle'
    simp only [ENat.toNat_coe] at hbd
    push_cast at this
    linarith
  have hepos : (0 : ℝ) < eO (O := O) l := by exact_mod_cast he
  have htle := le_of_mul_le_mul_left hle'' hepos
  apply hc2
  have : ((t : ℕ) : ℝ) = (s₁ : ℝ) - 2 * σ := by
    rw [ht]
    push_cast [show 2 * σ ≤ s₁ by omega]
    ring
  rw [← this]
  exact htle

end ArcLengthThreeFiltration
end Formalism.MainNotions.N.FrobeniusPowerSeries
