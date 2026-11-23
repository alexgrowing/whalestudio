import Mathlib
import Formalism.PairingDivisors.StatementA
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartEqOneOfLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModFMulPosPrincipal

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.Euler

variable {E : Type} [Field E] [NumberField E]

def iota (a : OF E) : Af E := algebraMap E (Af E) (algebraMap (OF E) E a)

def LocIn (n : ℕ) (v : HeightOneSpectrum (OF E)) (z : Af E) : Prop :=
  ∃ a : OF E, ∀ P, Over P v → Valued.v (z P - iota a P) ≤ WithZero.exp (-(n : ℤ))

theorem iota_mul (a b : OF E) : iota (a * b) = iota a * iota b := by simp [iota]

theorem iota_sub (a b : OF E) : iota (a - b) = iota a - iota b := by simp [iota]

theorem iota_add (a b : OF E) : iota (a + b) = iota a + iota b := by simp [iota]

theorem iota_one : iota (1 : OF E) = 1 := by simp [iota]

theorem iota_zero : iota (0 : OF E) = 0 := by simp [iota]

theorem mul_coord (z z' : Af E) (P : HeightOneSpectrum (𝓞 E)) : (z * z') P = z P * z' P := rfl

theorem sub_coord (z z' : Af E) (P : HeightOneSpectrum (𝓞 E)) : (z - z') P = z P - z' P := rfl

theorem add_coord (z z' : Af E) (P : HeightOneSpectrum (𝓞 E)) : (z + z') P = z P + z' P := rfl

theorem one_coord (P : HeightOneSpectrum (𝓞 E)) : (1 : Af E) P = 1 := rfl

theorem zero_coord (P : HeightOneSpectrum (𝓞 E)) : (0 : Af E) P = 0 := rfl

theorem inv_coord (y : (Af E)ˣ) (P : HeightOneSpectrum (𝓞 E)) : ((y⁻¹ : (Af E)ˣ) : Af E) P = ((y : Af E) P)⁻¹ :=
  eq_inv_of_mul_eq_one_left (coord P y).inv_val

theorem val_iota_le_iff (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (a : OF E) :
    Valued.v (iota a P) ≤ WithZero.exp (-(n : ℤ)) ↔ algebraMap (OF E) (𝓞 E) a ∈ P.asIdeal ^ n := by
  have : iota a = algebraMap E (Af E) (algebraMap (𝓞 E) E (algebraMap (OF E) (𝓞 E) a)) := rfl
  rw [this, FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    HeightOneSpectrum.valuation_of_algebraMap]
  exact P.intValuation_le_pow_iff_mem _ n

theorem val_iota_le_one (P : HeightOneSpectrum (𝓞 E)) (a : OF E) : Valued.v (iota a P) ≤ 1 := by
  simpa using (val_iota_le_iff P 0 a).2 (by simp)

theorem val_iota_le_of_mem {P : HeightOneSpectrum (𝓞 E)} {v : HeightOneSpectrum (OF E)} (h : Over P v) (n : ℕ) {a : OF E}
    (ha : a ∈ v.asIdeal ^ n) : Valued.v (iota a P) ≤ WithZero.exp (-(n : ℤ)) := by
  rw [val_iota_le_iff]
  have h1 : Ideal.map (algebraMap (OF E) (𝓞 E)) (v.asIdeal ^ n) ≤ P.asIdeal ^ n := by
    rw [Ideal.map_pow]
    refine Ideal.pow_right_mono ?_ n
    rw [Ideal.map_le_iff_le_comap]
    exact h.ge
  exact h1 (Ideal.mem_map_of_mem _ ha)

theorem over_iff_under (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (OF E)) : Over P v ↔ P.under (OF E) = v :=
  ⟨fun h => HeightOneSpectrum.ext h, fun h => by rw [← h]; rfl⟩

theorem over_under (P : HeightOneSpectrum (𝓞 E)) : Over P (P.under (OF E)) := rfl

theorem mem_aboveF (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (OF E)) :
    P ∈ Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) v ↔ Over P v := by
  unfold Formalism.L2.Host.aboveF
  rw [Set.Finite.mem_toFinset, over_iff_under]
  rfl

theorem LocIn.mono {m n : ℕ} {v : HeightOneSpectrum (OF E)} {z : Af E} (h : LocIn n v z) (hm : m ≤ n) : LocIn m v z := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, fun P hP => (ha P hP).trans (WithZero.exp_le_exp.2 (by omega))⟩

theorem LocIn.val_le {n : ℕ} {v : HeightOneSpectrum (OF E)} {z : Af E} (h : LocIn n v z) {P : HeightOneSpectrum (𝓞 E)}
    (hP : Over P v) : Valued.v (z P) ≤ 1 := by
  obtain ⟨a, ha⟩ := h.mono (Nat.zero_le n)
  have h1 : Valued.v (z P - iota a P) ≤ 1 := by simpa using ha P hP
  have := Valuation.map_add_le _ h1 (val_iota_le_one P a)
  rwa [sub_add_cancel] at this

theorem locIn_zero_iff {v : HeightOneSpectrum (OF E)} {z : Af E} : LocIn 0 v z ↔ ∀ P, Over P v → Valued.v (z P) ≤ 1 :=
  ⟨fun h _ hP => h.val_le hP, fun h => ⟨0, fun P hP => by simpa [iota_zero, zero_coord] using h P hP⟩⟩

theorem locIn_congr {n : ℕ} {v : HeightOneSpectrum (OF E)} {z z' : Af E} (h : ∀ P, Over P v → z P = z' P) :
    LocIn n v z ↔ LocIn n v z' :=
  exists_congr fun _ => forall₂_congr fun P hP => by rw [h P hP]

theorem locIn_of_sub_one {n : ℕ} {v : HeightOneSpectrum (OF E)} {z : Af E}
    (h : ∀ P, Over P v → Valued.v (z P - 1) ≤ WithZero.exp (-(n : ℤ))) : LocIn n v z :=
  ⟨1, fun P hP => by rw [iota_one]; exact h P hP⟩

theorem LocIn.mul {n : ℕ} {v : HeightOneSpectrum (OF E)} {z z' : Af E} (h : LocIn n v z) (h' : LocIn n v z') :
    LocIn n v (z * z') := by
  have hz := fun P hP => h.val_le (P := P) hP
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := h'
  refine ⟨a * b, fun P hP => ?_⟩
  have : (z * z') P - iota (a * b) P = z P * (z' P - iota b P) + (z P - iota a P) * iota b P := by
    rw [iota_mul, mul_coord, mul_coord]; ring
  rw [this]
  refine Valuation.map_add_le _ ?_ ?_
  · rw [map_mul]; exact (mul_le_mul' (hz P hP) (hb P hP)).trans_eq (one_mul _)
  · rw [map_mul]; exact (mul_le_mul' (ha P hP) (val_iota_le_one P b)).trans_eq (mul_one _)

theorem LocIn.inv {n : ℕ} {v : HeightOneSpectrum (OF E)} {y : (Af E)ˣ} (h : LocIn n v y)
    (hu : ∀ P, Over P v → Valued.v ((y : Af E) P) = 1) : LocIn n v (y⁻¹ : (Af E)ˣ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact locIn_zero_iff.2 fun P hP => by rw [inv_coord, map_inv₀, hu P hP, inv_one]
  obtain ⟨a, ha⟩ := h
  by_cases hav : a ∈ v.asIdeal
  · refine ⟨0, fun P hP => absurd (hu P hP) (ne_of_lt ?_)⟩
    have h1 := val_iota_le_of_mem hP 1 (a := a) (by simpa using hav)
    have h2 := (ha P hP).trans (WithZero.exp_le_exp.2 (show -(n : ℤ) ≤ -((1 : ℕ) : ℤ) by omega))
    have := Valuation.map_add_le _ h2 h1
    rw [sub_add_cancel] at this
    refine this.trans_lt ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hco : IsCoprime (Ideal.span {a}) (v.asIdeal ^ n) := by
    refine IsCoprime.pow_right ?_
    rw [Ideal.isCoprime_iff_sup_eq, sup_comm]
    exact v.isMaximal.1.2 _ (lt_of_le_of_ne le_sup_left fun h => hav (h.ge (Ideal.mem_sup_right (Ideal.mem_span_singleton_self a))))
  obtain ⟨s, hs, t, ht, hst⟩ := Ideal.isCoprime_iff_exists.1 hco
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hs
  refine ⟨b, fun P hP => ?_⟩
  have h0 : (y : Af E) P ≠ 0 := (coord P y).ne_zero
  have h1 : iota b P * iota a P + iota t P = 1 := by
    rw [← mul_coord, ← add_coord, ← iota_mul, ← iota_add, hst, iota_one, one_coord]
  have : ((y⁻¹ : (Af E)ˣ) : Af E) P - iota b P =
      ((y : Af E) P)⁻¹ * (iota t P - iota b P * ((y : Af E) P - iota a P)) := by
    rw [inv_coord]; field_simp; linear_combination -h1
  rw [this, map_mul, map_inv₀, hu P hP, inv_one, one_mul]
  refine Valuation.map_sub_le _ (val_iota_le_of_mem hP n ht) ?_
  rw [map_mul]; exact (mul_le_mul' (val_iota_le_one P b) (ha P hP)).trans_eq (one_mul _)

theorem locIn_of_mem_hatO {c : Ideal (OF E)} {z : Af E} (hz : z ∈ hatO c) (v : HeightOneSpectrum (OF E)) :
    LocIn (expIn c v) v z := by
  obtain ⟨a, ha⟩ := OrderUnits.exists_cong v (expIn c v) (pow_multiplicity_dvd _ _) _
    (fun P hP => (mem_aboveF P v).1 hP) hz
  exact ⟨a, fun P hP => by rw [Valuation.map_sub_swap]; exact ha P ((mem_aboveF P v).2 hP)⟩

end GlobalTheory.CMVal.Euler
