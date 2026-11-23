import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelicRingClassLatticeOneEqOrder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedOrderIffPlacewise
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdempotentAdelesAndSmallAdelicMatrices

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex GlobalTheory.CMVal.Euler

namespace GlobalTheory.CMVal.LatLoc

variable {E : Type} [Field E] [NumberField E]

theorem natCast_coord (n : ℕ) (w : HeightOneSpectrum (𝓞 E)) : (n : Af E) w = (n : w.adicCompletion E) := by
  rfl

theorem val_nat_le_one (n : ℕ) (w : HeightOneSpectrum (𝓞 E)) : Valued.v ((n : Af E) w) ≤ 1 := by
  have h : (n : Af E) = iota ((n : ℕ) : OF E) := by rw [iota, map_natCast, map_natCast]
  rw [h]; exact val_iota_le_one w _

theorem val_nat_eq_one {n : ℕ} {w : HeightOneSpectrum (𝓞 E)} (hw : (n : 𝓞 E) ∉ w.asIdeal) :
    Valued.v ((n : Af E) w) = 1 := by
  have h1 := (w.valuation_eq_one_iff_notMem (K := E)).mpr hw
  have h2 := w.valuedAdicCompletion_eq_valuation' (K := E) ((n : ℕ) : E)
  have h3 : (algebraMap E (w.adicCompletion E)) ((n : ℕ) : E) = ((n : ℕ) : w.adicCompletion E) := map_natCast _ _
  have h4 : (((n : ℕ) : 𝓞 E) : E) = ((n : ℕ) : E) := map_natCast (algebraMap (𝓞 E) E) _
  rw [natCast_coord, ← h3]
  exact h2.trans (h4 ▸ h1)

theorem exp_neg_nat_le_one (k : ℕ) : WithZero.exp (-(k : ℤ)) ≤ 1 := by
  rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega

theorem mul_mem_hatO [IsCMField E] {c : Ideal (OF E)} (hc : c ≠ ⊥) {l : ℕ} {u : Af E}
    (hu : ∀ P : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ P.asIdeal → u P = 1) {n : ℕ}
    (hn : ∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∉ w.asIdeal →
      Valued.v ((n : Af E) w) ≤ WithZero.exp (-(multiplicity w.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) : ℤ)) ∧
      Valued.v ((n : Af E) w) * Valued.v (u w) ≤
        WithZero.exp (-(multiplicity w.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) : ℤ)))
    {z : Af E} (hz : z ∈ hatO c) : (n : Af E) * z * u ∈ hatO c := by
  obtain ⟨a, ha, hai, hza⟩ := (HatPlace.mem_hatO_iff E c hc z).1 hz
  refine (HatPlace.mem_hatO_iff E c hc _).2 ⟨(n : Af E) * a, (hatF (E := E)).mul_mem (natCast_mem _ n) ha,
    fun w => ?_, fun w => ?_⟩
  · rw [mul_coord, map_mul]; exact mul_le_one' (val_nat_le_one n w) (hai w)
  · have hzi : Valued.v (z w) ≤ 1 := by
      have h := Valuation.map_add_le Valued.v ((hza w).trans (exp_neg_nat_le_one _)) (hai w)
      rwa [sub_add_cancel] at h
    by_cases hw : (l : 𝓞 E) ∈ w.asIdeal
    · rw [mul_coord, mul_coord, mul_coord, hu w hw, mul_one, ← mul_sub, map_mul]
      exact (mul_le_mul' (val_nat_le_one n w) (hza w)).trans_eq (one_mul _)
    · obtain ⟨h1, h2⟩ := hn w hw
      refine Valuation.map_sub_le _ ?_ ?_
      · rw [mul_coord, mul_coord, map_mul, map_mul]
        calc Valued.v ((n : Af E) w) * Valued.v (z w) * Valued.v (u w)
            ≤ Valued.v ((n : Af E) w) * 1 * Valued.v (u w) := mul_le_mul' (mul_le_mul' le_rfl hzi) le_rfl
          _ ≤ _ := by rw [mul_one]; exact h2
      · rw [mul_coord, map_mul]; exact (mul_le_mul' h1 (hai w)).trans_eq (mul_one _)

theorem lattice_near_orderC : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime →
    ∀ y : (Af E)ˣ, (∀ P : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ P.asIdeal → (y : Af E) P = 1) →
    ∃ n : ℕ, n.Coprime l ∧ (∀ x ∈ lattice c y, (n : E) * x ∈ orderC c) ∧ ∀ x ∈ orderC c, (n : E) * x ∈ lattice c y := by
  intro E _ _ _ c hc l hl y hy
  have hy' : ∀ P : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ P.asIdeal → (↑y⁻¹ : Af E) P = 1 := fun P hP => by
    have h : ((y : Af E) * ↑y⁻¹) P = 1 := by rw [Units.mul_inv]; rfl
    rwa [mul_coord, hy P hP, one_mul] at h
  obtain ⟨m₁, hm₁, hi₁⟩ := GlobalTheory.UnRep.SmallMat.exists_nsmul_integral (F := E) (y : Af E)
  obtain ⟨m₂, hm₂, hi₂⟩ := GlobalTheory.UnRep.SmallMat.exists_nsmul_integral (F := E) (↑y⁻¹ : Af E)
  have hN : Ideal.absNorm c ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hn0 : Ideal.absNorm c * m₁ * m₂ ≠ 0 := mul_ne_zero (mul_ne_zero hN hm₁) hm₂
  obtain ⟨k, n, hln, hkn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 l hl.one_lt.ne'

  have hint : ∀ (m : ℕ) (u : Af E), (∀ v, (m • u) v ∈ v.adicCompletionIntegers E) → ∀ w : HeightOneSpectrum (𝓞 E),
      Valued.v ((m : Af E) w) * Valued.v (u w) ≤ 1 := fun m u hmu w => by
    have h := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hmu w)
    change Valued.v (m • u w) ≤ 1 at h
    rwa [nsmul_eq_mul, map_mul, ← natCast_coord] at h
  have hNw : ∀ w : HeightOneSpectrum (𝓞 E), Valued.v ((Ideal.absNorm c : Af E) w) ≤
      WithZero.exp (-(multiplicity w.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) : ℤ)) := fun w => by
    have h := HatPlace.val_mul_le hc (Ideal.absNorm_mem c) (y := 1) (fun w => by
      show Valued.v ((1 : w.adicCompletion E)) ≤ 1
      rw [map_one]) w
    have e : iota ((Ideal.absNorm c : ℕ) : OF E) * 1 = (Ideal.absNorm c : Af E) := by
      rw [mul_one, iota, map_natCast, map_natCast]
    rwa [e] at h
  have hnw : ∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∉ w.asIdeal →
      Valued.v ((n : Af E) w) = Valued.v ((Ideal.absNorm c : Af E) w) * Valued.v ((m₁ : Af E) w) *
        Valued.v ((m₂ : Af E) w) := fun w hw => by
    have h1 : Valued.v (((Ideal.absNorm c * m₁ * m₂ : ℕ) : Af E) w) = Valued.v ((n : Af E) w) := by
      rw [hkn, Nat.cast_mul, Nat.cast_pow, mul_coord, map_mul]
      have h2 : Valued.v ((((l : ℕ) : Af E) ^ k) w) = 1 := by
        rw [← Nat.cast_pow, natCast_coord, Nat.cast_pow, map_pow, ← natCast_coord, val_nat_eq_one hw, one_pow]
      rw [h2, one_mul]
    rw [← h1, Nat.cast_mul, Nat.cast_mul, mul_coord, mul_coord, map_mul, map_mul]
  have hle : ∀ a b : WithZero (Multiplicative ℤ), a ≤ 1 → b ≤ 1 → ∀ e, ∀ t : WithZero (Multiplicative ℤ), t ≤ e →
      t * a * b ≤ e := fun a b ha hb e t ht =>
    (mul_le_mul' (mul_le_mul' ht ha) hb).trans_eq (by rw [mul_one, mul_one])
  refine ⟨n, Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hl).2 hln), fun x hx => ?_, fun x hx => ?_⟩
  · have h := LatLoc.mul_mem_hatO hc hy (n := n) (fun w hw => by
      rw [hnw w hw]
      refine ⟨hle _ _ (val_nat_le_one _ w) (val_nat_le_one _ w) _ _ (hNw w), ?_⟩
      have e : Valued.v ((Ideal.absNorm c : Af E) w) * Valued.v ((m₁ : Af E) w) * Valued.v ((m₂ : Af E) w) *
          Valued.v ((y : Af E) w) = Valued.v ((Ideal.absNorm c : Af E) w) * (Valued.v ((m₁ : Af E) w) *
            Valued.v ((y : Af E) w)) * Valued.v ((m₂ : Af E) w) := by ac_rfl
      rw [e]
      exact hle _ _ (hint m₁ _ hi₁ w) (val_nat_le_one _ w) _ _ (hNw w)) (mem_lattice.1 hx)
    have e : (n : Af E) * (algebraMap E (Af E) x * (↑y⁻¹ : Af E)) * (y : Af E) = algebraMap E (Af E) ((n : E) * x) := by
      rw [mul_assoc, mul_assoc, Units.inv_mul, mul_one, map_mul, map_natCast]
    rw [e] at h
    exact HatCap.mem_orderC_of_mem_hatO hc h
  · have h := LatLoc.mul_mem_hatO hc hy' (n := n) (fun w hw => by
      rw [hnw w hw]
      refine ⟨hle _ _ (val_nat_le_one _ w) (val_nat_le_one _ w) _ _ (hNw w), ?_⟩
      have e : Valued.v ((Ideal.absNorm c : Af E) w) * Valued.v ((m₁ : Af E) w) * Valued.v ((m₂ : Af E) w) *
          Valued.v ((↑y⁻¹ : Af E) w) = Valued.v ((Ideal.absNorm c : Af E) w) * Valued.v ((m₁ : Af E) w) *
            (Valued.v ((m₂ : Af E) w) * Valued.v ((↑y⁻¹ : Af E) w)) := by ac_rfl
      rw [e]
      exact hle _ _ (val_nat_le_one _ w) (hint m₂ _ hi₂ w) _ _ (hNw w)) (algebraMap_mem_hatO hx)
    rw [mem_lattice, map_mul, map_natCast]
    exact h

end GlobalTheory.CMVal.LatLoc
