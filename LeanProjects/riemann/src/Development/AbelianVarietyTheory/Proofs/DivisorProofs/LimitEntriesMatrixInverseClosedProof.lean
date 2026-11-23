import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
open GlobalTheory.IsoTriv

namespace GlobalTheory.LimInv

variable {R V : Type} [CommRing R] [CommRing V]

def limSub (φ : R →+* V) (q : R) : Subring V where
  carrier := {t | ∀ N : ℕ, ∃ a z, φ a = t + φ q ^ N * z}
  mul_mem' := by
    intro s t hs ht N
    obtain ⟨a, z, ha⟩ := hs N
    obtain ⟨b, w, hb⟩ := ht N
    refine ⟨a * b, z * t + s * w + φ q ^ N * z * w, ?_⟩
    rw [map_mul, ha, hb]; ring
  one_mem' := fun N => ⟨1, 0, by simp⟩
  add_mem' := by
    intro s t hs ht N
    obtain ⟨a, z, ha⟩ := hs N
    obtain ⟨b, w, hb⟩ := ht N
    exact ⟨a + b, z + w, by rw [map_add, ha, hb]; ring⟩
  zero_mem' := fun N => ⟨0, 0, by simp⟩
  neg_mem' := by
    intro s hs N
    obtain ⟨a, z, ha⟩ := hs N
    exact ⟨-a, -z, by rw [map_neg, ha]; ring⟩

theorem inv_mem_limSub [IsDedekindDomain R] [IsDomain V] [IsDiscreteValuationRing V]
    (φ : R →+* V) (q : R) (hq0 : φ q ≠ 0) (hqu : ¬ IsUnit (φ q)) (u : Vˣ)
    (hu : (u : V) ∈ limSub φ q) : ((u⁻¹ : Vˣ) : V) ∈ limSub φ q := by
  intro N
  obtain ⟨a, z, ha⟩ := hu (N + 1)
  have hqm : φ q ∈ IsLocalRing.maximalIdeal V := (IsLocalRing.mem_maximalIdeal _).2 hqu
  have haU : IsUnit (φ a) := by
    by_contra h
    have h1 : φ a ∈ IsLocalRing.maximalIdeal V := (IsLocalRing.mem_maximalIdeal _).2 h
    have h2 : φ q ^ (N + 1) * z ∈ IsLocalRing.maximalIdeal V :=
      Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hqm _ (Nat.succ_pos N))
    have h3 : (u : V) ∈ IsLocalRing.maximalIdeal V := by
      have : (u : V) = φ a - φ q ^ (N + 1) * z := by rw [ha]; ring
      rw [this]; exact Ideal.sub_mem _ h1 h2
    exact ((IsLocalRing.mem_maximalIdeal _).1 h3) u.isUnit
  set w : Ideal R := (IsLocalRing.maximalIdeal V).comap φ with hw
  have hwp : w.IsPrime := Ideal.comap_isPrime φ _
  have hqw : q ∈ w := hqm
  have hwne : w ≠ ⊥ := by
    intro h
    have : q = 0 := by rw [h] at hqw; exact (Submodule.mem_bot R).1 hqw
    exact hq0 (by rw [this, map_zero])
  have hwm : w.IsMaximal := hwp.isMaximal hwne
  have haw : a ∉ w := fun h => ((IsLocalRing.mem_maximalIdeal _).1 h) haU
  obtain ⟨y, i, hiw, hyi⟩ := hwm.exists_inv haw
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨n, e, he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (pow_ne_zero N hq0) hϖ
  have hiV : φ i ∈ Ideal.span {ϖ} := by rw [← hϖ.maximalIdeal_eq]; exact hiw
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hiV
  let b : R := y * ∑ j ∈ Finset.range n, i ^ j
  have hab : φ a * φ b = 1 - φ q ^ N * ((e⁻¹ : Vˣ) * c ^ n) := by
    have h1 : a * b = 1 - i ^ n := by
      have : a * y = 1 - i := by linear_combination hyi
      calc a * b = (a * y) * ∑ j ∈ Finset.range n, i ^ j := by ring
        _ = 1 - i ^ n := by rw [this, mul_neg_geom_sum]
    have h2 : φ a * φ b = 1 - φ i ^ n := by rw [← map_mul, h1, map_sub, map_one, map_pow]
    rw [h2, he, ← hc, mul_pow]
    have : ((e : V) * (e⁻¹ : Vˣ)) = 1 := Units.mul_inv e
    linear_combination (c ^ n * ϖ ^ n) * this
  refine ⟨b, -((u⁻¹ : Vˣ) : V) * ((e⁻¹ : Vˣ) * c ^ n) - ((u⁻¹ : Vˣ) : V) * φ q * z * φ b, ?_⟩
  have hu1 : (u : V) * ((u⁻¹ : Vˣ) : V) = 1 := Units.mul_inv u
  linear_combination ((u⁻¹ : Vˣ) : V) * hab - (((u⁻¹ : Vˣ) : V) * φ b) * ha - φ b * hu1

end GlobalTheory.LimInv

open GlobalTheory.LimInv in
theorem GlobalTheory.IsoTriv.limitEntriesMatrixInverseClosed_proof : InvSt := by
  intro R V _ _ _ _ _ φ q hq0 hqu n M hdet hM
  classical
  let S := limSub φ q
  let M₀ : Matrix (Fin n) (Fin n) S := fun b b' => ⟨M b b', fun N => hM b b' N⟩
  have hMM : S.subtype.mapMatrix M₀ = M := by ext b b'; rfl
  have hadj : ∀ b b', M.adjugate b b' ∈ S := by
    intro b b'
    rw [← hMM, ← RingHom.map_adjugate]
    exact (M₀.adjugate b b').2
  have hdetS : M.det ∈ S := by
    rw [← hMM, ← RingHom.map_det]; exact (M₀.det).2
  set u := hdet.unit with hu
  have huS : (u : V) ∈ S := by rw [hu, IsUnit.unit_spec]; exact hdetS
  have hinv := inv_mem_limSub φ q hq0 hqu u huS
  refine ⟨((u⁻¹ : Vˣ) : V) • M.adjugate, ?_, ?_⟩
  · rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul]
    have : ((u⁻¹ : Vˣ) : V) * M.det = 1 := by
      rw [show M.det = (u : V) by rw [hu, IsUnit.unit_spec]]; exact Units.inv_mul u
    rw [this, one_smul]
  · intro b b' N
    have : (((u⁻¹ : Vˣ) : V) • M.adjugate) b b' ∈ S := by
      rw [Matrix.smul_apply, smul_eq_mul]; exact S.mul_mem hinv (hadj b b')
    exact this N
