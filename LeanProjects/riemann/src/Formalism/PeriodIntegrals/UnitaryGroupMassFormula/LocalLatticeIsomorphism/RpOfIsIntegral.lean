import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeIsomorphism.LatticeFromNormOne

noncomputable section
open scoped BigOperators
open NumberField

namespace PI.KLW

section
variable {K : Type} [Field K] [NumberField K]

theorem mem_range_iff {x : K} : x ∈ (algebraMap (𝓞 K) K).range ↔ IsIntegral ℤ x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact RingOfIntegers.isIntegral_coe y
  · intro h
    exact ⟨⟨x, h⟩, rfl⟩

theorem Rp_of_isIntegral {p : ℕ} {x : K} (h : IsIntegral ℤ x) : Rp K p x :=
  ⟨1, Nat.coprime_one_left p, by rw [Nat.cast_one, one_mul, mem_range_iff]; exact h⟩

theorem Rp_zero {p : ℕ} : Rp K p 0 := Rp_of_isIntegral isIntegral_zero

theorem Rp_one {p : ℕ} : Rp K p 1 := Rp_of_isIntegral isIntegral_one

theorem Rp_natCast {p : ℕ} (m : ℕ) : Rp K p (m : K) := Rp_of_isIntegral (by
  simpa using (isIntegral_algebraMap (R := ℤ) (A := K) (x := (m : ℤ))))

theorem Rp_intCast {p : ℕ} (m : ℤ) : Rp K p (m : K) := Rp_of_isIntegral (by
  simpa using (isIntegral_algebraMap (R := ℤ) (A := K) (x := m)))

theorem Rp_add {p : ℕ} {x y : K} (hx : Rp K p x) (hy : Rp K p y) : Rp K p (x + y) := by
  obtain ⟨s, hs, hsx⟩ := hx
  obtain ⟨t, ht, hty⟩ := hy
  refine ⟨s * t, Nat.Coprime.mul_left hs ht, ?_⟩
  rw [mem_range_iff] at *
  have e : ((s * t : ℕ) : K) * (x + y) = (t : K) * ((s : K) * x) + (s : K) * ((t : K) * y) := by
    push_cast; ring
  rw [e]
  have ht' : IsIntegral ℤ (t : K) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := K) (x := (t : ℤ)))
  have hs' : IsIntegral ℤ (s : K) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := K) (x := (s : ℤ)))
  exact (ht'.mul hsx).add (hs'.mul hty)

theorem Rp_mul {p : ℕ} {x y : K} (hx : Rp K p x) (hy : Rp K p y) : Rp K p (x * y) := by
  obtain ⟨s, hs, hsx⟩ := hx
  obtain ⟨t, ht, hty⟩ := hy
  refine ⟨s * t, Nat.Coprime.mul_left hs ht, ?_⟩
  rw [mem_range_iff] at *
  have e : ((s * t : ℕ) : K) * (x * y) = ((s : K) * x) * ((t : K) * y) := by
    push_cast; ring
  rw [e]
  exact hsx.mul hty

theorem Rp_neg {p : ℕ} {x : K} (hx : Rp K p x) : Rp K p (-x) := by
  have := Rp_mul (Rp_intCast (K := K) (p := p) (-1)) hx
  simpa using this

theorem Rp_sub {p : ℕ} {x y : K} (hx : Rp K p x) (hy : Rp K p y) : Rp K p (x - y) := by
  simpa [sub_eq_add_neg] using Rp_add hx (Rp_neg hy)

theorem Rp_map {p : ℕ} (c : K →+* K) {x : K} (hx : Rp K p x) : Rp K p (c x) := by
  obtain ⟨s, hs, hsx⟩ := hx
  refine ⟨s, hs, ?_⟩
  rw [mem_range_iff] at *
  have := hsx.map c.toIntAlgHom
  simpa using this

theorem Rp_inv_natCast {p : ℕ} {s : ℕ} (hs : Nat.Coprime s p) : Rp K p ((s : K)⁻¹) := by
  refine ⟨s, hs, ?_⟩
  rw [mem_range_iff]
  by_cases h : (s : K) = 0
  · rw [h, zero_mul]; exact isIntegral_zero
  · rw [mul_inv_cancel₀ h]; exact isIntegral_one

end

section
variable {K : Type} [Field K] {ι : Type} [Fintype ι] (c : K →+* K)

theorem hf_add_left (v v' w : ι → K) : hf c (v + v') w = hf c v w + hf c v' w := by
  simp [hf, add_mul, Finset.sum_add_distrib]

theorem hf_add_right (v w w' : ι → K) : hf c v (w + w') = hf c v w + hf c v w' := by
  simp [hf, mul_add, Finset.sum_add_distrib]

theorem hf_smul_left (a : K) (v w : ι → K) : hf c (a • v) w = a * hf c v w := by
  simp [hf, Finset.mul_sum, mul_assoc]

theorem hf_smul_right (a : K) (v w : ι → K) : hf c v (a • w) = c a * hf c v w := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem hf_zero_left (w : ι → K) : hf c 0 w = 0 := by simp [hf]

theorem hf_symm (hc : ∀ x, c (c x) = x) (v w : ι → K) : hf c w v = c (hf c v w) := by
  simp only [hf, map_sum, map_mul, hc]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem hf_single_left [DecidableEq ι] (i : ι) (a : K) (w : ι → K) :
    hf c (Pi.single i a) w = a * c (w i) := by
  simp [hf, Pi.single_apply]

end

section
variable {K : Type} [Field K] [NumberField K] {c : K →+* K} {p : ℕ} {ι : Type} [Fintype ι]
  {L : Set (ι → K)}

theorem Unimod.zero_mem (hL : Unimod K c p L) : (0 : ι → K) ∈ L :=
  (hL 0).2 fun w _ => by simpa [hf_zero_left] using (Rp_zero : Rp K p 0)

theorem Unimod.add_mem (hL : Unimod K c p L) {v v' : ι → K} (hv : v ∈ L) (hv' : v' ∈ L) :
    v + v' ∈ L :=
  (hL _).2 fun w hw => by
    rw [hf_add_left]; exact Rp_add ((hL v).1 hv w hw) ((hL v').1 hv' w hw)

theorem Unimod.smul_mem (hL : Unimod K c p L) {a : K} (ha : Rp K p a) {v : ι → K} (hv : v ∈ L) :
    a • v ∈ L :=
  (hL _).2 fun w hw => by
    rw [hf_smul_left]; exact Rp_mul ha ((hL v).1 hv w hw)

theorem Unimod.neg_mem (hL : Unimod K c p L) {v : ι → K} (hv : v ∈ L) : -v ∈ L := by
  simpa using hL.smul_mem (Rp_intCast (-1)) hv

theorem Unimod.sub_mem (hL : Unimod K c p L) {v v' : ι → K} (hv : v ∈ L) (hv' : v' ∈ L) :
    v - v' ∈ L := by
  simpa [sub_eq_add_neg] using hL.add_mem hv (hL.neg_mem hv')

theorem Unimod.hf_mem (hL : Unimod K c p L) {v w : ι → K} (hv : v ∈ L) (hw : w ∈ L) :
    Rp K p (hf c v w) := (hL v).1 hv w hw

end

end PI.KLW
