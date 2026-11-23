import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ProjectionSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCplAtApprox

open IsLocalRing GlobalTheory.Pat

namespace GlobalTheory.Pat.CplMap

variable {R S S' : Type} [CommRing R] [CommRing S] [IsLocalRing S] [CommRing S'] [IsLocalRing S']
  {q : Ideal R} {φ : R →+* S} {ψ : R →+* S'}

theorem isUnit_mk (hψ : (maximalIdeal S').comap ψ = q) (n : ℕ) {b : R} (hb : b ∉ q) :
    IsUnit (Ideal.Quotient.mk (maximalIdeal S' ^ n) (ψ b)) := by
  have h1 : IsUnit (ψ b) := by
    by_contra h
    exact hb (hψ ▸ (Ideal.mem_comap.mpr ((mem_maximalIdeal _).mpr h)))
  exact h1.map _

theorem map_mem_pow (hψ : (maximalIdeal S').comap ψ = q) (n : ℕ) {a : R} (ha : a ∈ q ^ n) :
    ψ a ∈ maximalIdeal S' ^ n := by
  have h : (q ^ n).map ψ ≤ maximalIdeal S' ^ n := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr hψ.ge) n
  exact h (Ideal.mem_map_of_mem ψ ha)

theorem ext_mem_pow (hφ : IsCplAt q φ) (hψ : (maximalIdeal S').comap ψ = q) {F : S →+* S'}
    (hF : F.comp φ = ψ) (n : ℕ) {x : S} (hx : x ∈ maximalIdeal S ^ n) :
    F x ∈ maximalIdeal S' ^ n := by
  have h1 : (maximalIdeal S).map F ≤ maximalIdeal S' := by
    rw [hφ.max_eq, Ideal.map_map, hF]
    exact Ideal.map_le_iff_le_comap.mpr hψ.ge
  have h2 : (maximalIdeal S ^ n).map F ≤ maximalIdeal S' ^ n := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono h1 n
  exact h2 (Ideal.mem_map_of_mem F hx)

variable [hq : q.IsPrime]

def IsVal (q : Ideal R) (φ : R →+* S) (ψ : R →+* S') (n : ℕ) (s : S)
    (t : S' ⧸ maximalIdeal S' ^ n) : Prop :=
  ∀ a b : R, b ∉ q → φ b * s - φ a ∈ maximalIdeal S ^ n →
    Ideal.Quotient.mk (maximalIdeal S' ^ n) (ψ b) * t = Ideal.Quotient.mk (maximalIdeal S' ^ n) (ψ a)

theorem exists_val (hφ : IsCplAt q φ) (hψ : (maximalIdeal S').comap ψ = q) (n : ℕ) (s : S) :
    ∃ t, IsVal q φ ψ n s t := by
  obtain ⟨a0, b0, hb0, h0⟩ := (isCplAt_approx R S q φ hφ n).1 s
  obtain ⟨u, hu⟩ := isUnit_mk hψ n hb0
  refine ⟨Ideal.Quotient.mk _ (ψ a0) * (↑u⁻¹ : S' ⧸ maximalIdeal S' ^ n), fun a b _ h => ?_⟩
  have hm : φ (b * a0 - b0 * a) ∈ maximalIdeal S ^ n := by
    have : φ (b * a0 - b0 * a) = φ b0 * (φ b * s - φ a) - φ b * (φ b0 * s - φ a0) := by
      simp only [map_sub, map_mul]; ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_left _ _ h0)
  obtain ⟨c, hc, hcq⟩ := (isCplAt_approx R S q φ hφ n).2 _ hm
  have h1 := Ideal.Quotient.eq_zero_iff_mem.mpr (map_mem_pow hψ n hcq)
  simp only [map_mul, map_sub] at h1
  have h2 := sub_eq_zero.mp ((isUnit_mk hψ n hc).mul_right_eq_zero.mp h1)
  rw [← mul_assoc, h2, ← hu, mul_right_comm, Units.mul_inv, one_mul]

omit hq in
theorem val_unique_of_pair (hψ : (maximalIdeal S').comap ψ = q) {n : ℕ} {s : S}
    {t t' : S' ⧸ maximalIdeal S' ^ n} (ht : IsVal q φ ψ n s t) {a b : R} (hb : b ∉ q)
    (h : φ b * s - φ a ∈ maximalIdeal S ^ n)
    (e : Ideal.Quotient.mk (maximalIdeal S' ^ n) (ψ b) * t' =
      Ideal.Quotient.mk (maximalIdeal S' ^ n) (ψ a)) : t = t' :=
  (isUnit_mk hψ n hb).mul_left_cancel ((ht a b hb h).trans e.symm)

theorem one_notMem : (1 : R) ∉ q := fun h => hq.ne_top ((Ideal.eq_top_iff_one q).mpr h)

theorem exists_levHom (hφ : IsCplAt q φ) (hψ : (maximalIdeal S').comap ψ = q) (n : ℕ) :
    ∃ f : S →+* S' ⧸ maximalIdeal S' ^ n, ∀ s, IsVal q φ ψ n s (f s) := by
  choose f hf using exists_val hφ hψ n
  have ap := (isCplAt_approx R S q φ hφ n).1
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hf⟩
  · exact val_unique_of_pair hψ (hf 1) (a := 1) (b := 1) one_notMem (by simp) (by simp)
  · intro x y
    obtain ⟨a1, b1, hb1, h1⟩ := ap x
    obtain ⟨a2, b2, hb2, h2⟩ := ap y
    have hb : b1 * b2 ∉ q := fun h => (hq.mem_or_mem h).elim hb1 hb2
    refine val_unique_of_pair hψ (hf (x * y)) (a := a1 * a2) hb ?_ ?_
    · have : φ (b1 * b2) * (x * y) - φ (a1 * a2) =
          (φ b1 * x - φ a1) * (φ b2 * y) + φ a1 * (φ b2 * y - φ a2) := by
        simp only [map_mul]; ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ h1) (Ideal.mul_mem_left _ _ h2)
    · simp only [map_mul]
      rw [← hf x a1 b1 hb1 h1, ← hf y a2 b2 hb2 h2]; ring
  · exact val_unique_of_pair hψ (hf 0) (a := 0) (b := 1) one_notMem (by simp) (by simp)
  · intro x y
    obtain ⟨a1, b1, hb1, h1⟩ := ap x
    obtain ⟨a2, b2, hb2, h2⟩ := ap y
    have hb : b1 * b2 ∉ q := fun h => (hq.mem_or_mem h).elim hb1 hb2
    refine val_unique_of_pair hψ (hf (x + y)) (a := a1 * b2 + a2 * b1) hb ?_ ?_
    · have : φ (b1 * b2) * (x + y) - φ (a1 * b2 + a2 * b1) =
          φ b2 * (φ b1 * x - φ a1) + φ b1 * (φ b2 * y - φ a2) := by
        simp only [map_mul, map_add]; ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)
    · simp only [map_mul, map_add]
      rw [← hf x a1 b1 hb1 h1, ← hf y a2 b2 hb2 h2]; ring

end GlobalTheory.Pat.CplMap

namespace GlobalTheory.Pat

open CplMap

theorem isCplAt_existsUnique_map : ∀ (R S S' : Type) [CommRing R] [CommRing S] [IsLocalRing S]
    [CommRing S'] [IsLocalRing S'] [IsAdicComplete (maximalIdeal S') S'] (q : Ideal R) [q.IsPrime]
    (φ : R →+* S) (ψ : R →+* S'), IsCplAt q φ → (maximalIdeal S').comap ψ = q →
    ∃! θ : S →+* S', IsLocalHom θ ∧ θ.comp φ = ψ := by
  intro R S S' _ _ _ _ _ _ q _ φ ψ hφ hψ
  choose f hf using exists_levHom hφ hψ
  have hc : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow (maximalIdeal S') hle).comp (f n) = f m := by
    intro m n hle
    ext s
    obtain ⟨a, b, hb, h⟩ := (isCplAt_approx R S q φ hφ n).1 s
    refine (val_unique_of_pair hψ (hf m s) hb (Ideal.pow_le_pow_right hle h) ?_).symm
    have e := congrArg (Ideal.Quotient.factorPow (maximalIdeal S') hle) (hf n s a b hb h)
    rw [map_mul] at e
    exact e
  have hcomp : (IsAdicComplete.liftRingHom (maximalIdeal S') f hc).comp φ = ψ := by
    ext r
    refine congrFun (IsHausdorff.funext' (maximalIdeal S')
      (f := fun r => IsAdicComplete.liftRingHom (maximalIdeal S') f hc (φ r)) (g := fun r => ψ r)
      (fun n r => ?_)) r
    rw [IsAdicComplete.mk_liftRingHom]
    exact val_unique_of_pair hψ (hf n (φ r)) (a := r) (b := 1) one_notMem (by simp) (by simp)
  refine ⟨IsAdicComplete.liftRingHom (maximalIdeal S') f hc, ⟨⟨fun s hs => ?_⟩, hcomp⟩, ?_⟩
  · by_contra hn
    have h1 := ext_mem_pow hφ hψ hcomp 1 (x := s) (by
      rw [pow_one]; exact (mem_maximalIdeal _).mpr hn)
    rw [pow_one] at h1
    exact (mem_maximalIdeal _).mp h1 hs
  · rintro F ⟨-, hF⟩
    refine IsAdicComplete.eq_liftRingHom _ f hc F (fun n => ?_)
    ext s
    obtain ⟨a, b, hb, h⟩ := (isCplAt_approx R S q φ hφ n).1 s
    refine (val_unique_of_pair hψ (hf n s) hb h ?_).symm
    have h1 := ext_mem_pow hφ hψ hF n h
    rw [RingHom.comp_apply, ← map_mul, Ideal.Quotient.eq, ← hF]
    simpa using h1

end GlobalTheory.Pat
