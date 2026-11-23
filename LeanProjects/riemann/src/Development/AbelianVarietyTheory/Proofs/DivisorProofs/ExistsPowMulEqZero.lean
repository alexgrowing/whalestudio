import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero

namespace GlobalTheory.CocycleCoboundaryNumerator

theorem exists_numerator (R : Type) [CommRing R] (D : Type) [CommRing D] [Algebra R D] (u v : D)
    (f : (E : Type) → [CommRing E] → [Algebra R E] → (D →ₐ[R] E) → E)
    (hf : ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E']
      (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), IsUnit (ψ u) → IsUnit (ψ v) →
        f E' (θ.comp ψ) = θ (f E ψ)) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ c : D, ∀ (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E),
      IsUnit (ψ u) → IsUnit (ψ v) → f E ψ * (ψ u * ψ v) ^ N = ψ c := by
  classical
  let L := Localization.Away (u * v)
  let ψ₀ : D →ₐ[R] L := IsScalarTower.toAlgHom R D L
  have hψ₀ : IsUnit (ψ₀ u * ψ₀ v) := by
    rw [← map_mul]; exact IsLocalization.Away.algebraMap_isUnit (u * v)
  obtain ⟨⟨a, _, k, rfl⟩, hk⟩ := IsLocalization.surj (Submonoid.powers (u * v)) (f L ψ₀)
  refine ⟨k, fun N hN => ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hN
  refine ⟨a * (u * v) ^ j, fun E _ _ ψ hu hv => ?_⟩
  have huv : IsUnit (ψ (u * v)) := by rw [map_mul]; exact hu.mul hv
  let θ : L →ₐ[R] E := IsLocalization.Away.liftAlgHom (u * v) huv
  have hθ : ∀ x : D, θ (algebraMap D L x) = ψ x := fun x =>
    IsLocalization.Away.lift_eq (u * v) huv x
  have hcomp : θ.comp ψ₀ = ψ := AlgHom.ext fun x => hθ x
  have key := hf L E ψ₀ θ (isUnit_of_mul_isUnit_left hψ₀) (isUnit_of_mul_isUnit_right hψ₀)
  rw [hcomp] at key
  have hk' := congrArg θ hk
  simp only [map_mul, hθ] at hk'
  rw [key, map_mul, ← hk']
  simp only [map_pow, map_mul]
  ring

theorem exists_pow_mul_eq_zero (R : Type) [CommRing R] (D : Type) [CommRing D] [Algebra R D]
    (u x : D)
    (h : ∀ (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E), IsUnit (ψ u) → ψ x = 0) :
    ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → u ^ M * x = 0 := by
  let L := Localization.Away u
  have h0 : algebraMap D L x = 0 :=
    h L (IsScalarTower.toAlgHom R D L) (IsLocalization.Away.algebraMap_isUnit u)
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers u) L x).mp h0
  refine ⟨m, fun M hM => ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hM
  have hm' : u ^ m * x = 0 := hm
  rw [pow_add, mul_comm (u ^ m), mul_assoc, hm', mul_zero]

theorem map_inverse_of_isUnit {E E' : Type} [CommRing E] [CommRing E'] (θ : E →+* E') {x : E}
    (hx : IsUnit x) : Ring.inverse (θ x) = θ (Ring.inverse x) := by
  obtain ⟨w, rfl⟩ := hx
  have hw : θ (w : E) = ((Units.map θ.toMonoidHom w : E'ˣ) : E') := rfl
  rw [Ring.inverse_unit, hw, Ring.inverse_unit]
  rfl

theorem cocycle_is_coboundary (R : Type) [CommRing R] (D : Type) [CommRing D] [Algebra R D]
    (n : ℕ) (s : Fin n → D) (hs : Ideal.span (Set.range s) = ⊤)
    (d : Fin n → Fin n → (E : Type) → [CommRing E] → [Algebra R E] → (D →ₐ[R] E) → E)
    (hnat : ∀ (a b : Fin n) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E']
      [Algebra R E'] (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), IsUnit (ψ (s a)) → IsUnit (ψ (s b)) →
        d a b E' (AlgHom.comp θ ψ) = θ (d a b E ψ))
    (hcoc : ∀ (a b c : Fin n) (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E),
      IsUnit (ψ (s a)) → IsUnit (ψ (s b)) → IsUnit (ψ (s c)) →
        d a b E ψ + d b c E ψ = d a c E ψ) :
    ∃ (e : Fin n → (E : Type) → [CommRing E] → [Algebra R E] → (D →ₐ[R] E) → E),
      (∀ (a : Fin n) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E']
        [Algebra R E'] (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), IsUnit (ψ (s a)) →
          e a E' (AlgHom.comp θ ψ) = θ (e a E ψ)) ∧
      ∀ (a b : Fin n) (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E),
        IsUnit (ψ (s a)) → IsUnit (ψ (s b)) → d a b E ψ = e b E ψ - e a E ψ := by
  classical

  have h1 : ∀ a b : Fin n, ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ c : D, ∀ (E : Type) [CommRing E]
      [Algebra R E] (ψ : D →ₐ[R] E), IsUnit (ψ (s a)) → IsUnit (ψ (s b)) →
        d a b E ψ * (ψ (s a) * ψ (s b)) ^ N = ψ c := fun a b =>
    exists_numerator R D (s a) (s b) (d a b) (fun E _ _ E' _ _ ψ θ ha hb => hnat a b E E' ψ θ ha hb)
  choose N₀ hN₀ using h1
  obtain ⟨N, hN⟩ : ∃ N, ∀ a b, N₀ a b ≤ N :=
    ⟨Finset.univ.sup (fun p : Fin n × Fin n => N₀ p.1 p.2), fun a b =>
      Finset.le_sup (f := fun p : Fin n × Fin n => N₀ p.1 p.2) (Finset.mem_univ (a, b))⟩
  choose c hc using fun a b => hN₀ a b N (hN a b)

  have h2 : ∀ a b k : Fin n, ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → (s a * s b * s k) ^ M *
      (s k ^ N * c a b - s a ^ N * c k b + s b ^ N * c k a) = 0 := by
    intro a b k
    apply exists_pow_mul_eq_zero R D
    intro E _ _ ψ hu
    rw [map_mul, map_mul] at hu
    have ha := isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hu)
    have hb := isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hu)
    have hk := isUnit_of_mul_isUnit_right hu
    have e4 := hcoc k a b E ψ hk ha hb
    simp only [map_add, map_sub, map_mul, map_pow]
    rw [← hc a b E ψ ha hb, ← hc k b E ψ hk hb, ← hc k a E ψ hk ha]
    linear_combination (ψ (s a) * ψ (s b) * ψ (s k)) ^ N * e4
  choose M₀ hM₀ using h2
  obtain ⟨M, hM⟩ : ∃ M, ∀ a b k, M₀ a b k ≤ M :=
    ⟨Finset.univ.sup (fun p : Fin n × Fin n × Fin n => M₀ p.1 p.2.1 p.2.2), fun a b k =>
      Finset.le_sup (f := fun p : Fin n × Fin n × Fin n => M₀ p.1 p.2.1 p.2.2)
        (Finset.mem_univ (a, b, k))⟩

  obtain ⟨K, c', hc', hy⟩ : ∃ (K : ℕ) (c' : Fin n → Fin n → D),
      (∀ (a b : Fin n) (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E),
        IsUnit (ψ (s a)) → IsUnit (ψ (s b)) → d a b E ψ * (ψ (s a) * ψ (s b)) ^ K = ψ (c' a b)) ∧
      ∀ a b k, s k ^ K * c' a b = s a ^ K * c' k b - s b ^ K * c' k a := by
    refine ⟨N + M, fun a b => c a b * (s a * s b) ^ M, fun a b E _ _ ψ ha hb => ?_,
      fun a b k => ?_⟩
    · rw [map_mul, ← hc a b E ψ ha hb, map_pow, map_mul, pow_add]
      ring
    · linear_combination hM₀ a b k M (hM a b k)

  have hsK : Ideal.span (Set.range fun i => s i ^ K) = ⊤ := by
    have h := Ideal.span_pow_eq_top _ hs K
    rw [← Set.range_comp] at h
    exact h
  have h1mem : (1 : D) ∈ Ideal.span (Set.range fun i => s i ^ K) := by
    rw [hsK]; exact Submodule.mem_top
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun D).mp h1mem
  refine ⟨fun a E _ _ ψ => ∑ k, ψ (g k * c' k a) * Ring.inverse (ψ (s a)) ^ K, ?_, ?_⟩
  · intro a E _ _ E' _ _ ψ θ ha
    have hinv : Ring.inverse (θ (ψ (s a))) = θ (Ring.inverse (ψ (s a))) :=
      map_inverse_of_isUnit (θ : E →+* E') ha
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, hinv]
    simp only [map_mul, map_pow]
  · intro a b E _ _ ψ ha hb
    have hAK : ψ (s a) ^ K * Ring.inverse (ψ (s a)) ^ K = 1 := by
      rw [← mul_pow, Ring.mul_inverse_cancel _ ha, one_pow]
    have hBK : ψ (s b) ^ K * Ring.inverse (ψ (s b)) ^ K = 1 := by
      rw [← mul_pow, Ring.mul_inverse_cancel _ hb, one_pow]
    have hab := hc' a b E ψ ha hb
    have hsum : ∑ k, ψ (g k) * ψ (s k) ^ K = 1 := by
      have h := congrArg ψ hg
      simpa only [map_sum, smul_eq_mul, map_mul, map_pow, map_one] using h
    have hd : d a b E ψ = ∑ k, ψ (g k) * ψ (s k) ^ K * d a b E ψ := by
      rw [← Finset.sum_mul, hsum, one_mul]
    rw [hd, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hyk := congrArg ψ (hy a b k)
    simp only [map_mul, map_pow, map_sub] at hyk
    simp only [map_mul]
    linear_combination (ψ (g k)) * ((Ring.inverse (ψ (s a)) ^ K * Ring.inverse (ψ (s b)) ^ K) * hyk
      + (ψ (s k) ^ K * Ring.inverse (ψ (s a)) ^ K * Ring.inverse (ψ (s b)) ^ K) * hab
      + (Ring.inverse (ψ (s b)) ^ K * ψ (c' k b)
          - ψ (s k) ^ K * d a b E ψ * ψ (s b) ^ K * Ring.inverse (ψ (s b)) ^ K) * hAK
      - (Ring.inverse (ψ (s a)) ^ K * ψ (c' k a) + ψ (s k) ^ K * d a b E ψ) * hBK)

end GlobalTheory.CocycleCoboundaryNumerator
