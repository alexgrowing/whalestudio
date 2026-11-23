import Mathlib

namespace GlobalTheory.CompanionTheory.Ar.LocalisedSmooth

def denomMonoid {R : Type} [CommRing R] (c : R) : Submonoid R where
  carrier := {x | ∃ n k : ℕ, n ≠ 0 ∧ x = (n : R) * c ^ k}
  one_mem' := ⟨1, 0, one_ne_zero, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨n, k, hn, rfl⟩ ⟨m, l, hm, rfl⟩
    exact ⟨n * m, k + l, mul_ne_zero hn hm, by push_cast; ring⟩

theorem map_denomMonoid {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (c : R) :
    (denomMonoid c).map f = denomMonoid (f c) := by
  ext x
  constructor
  · rintro ⟨_, ⟨n, k, hn, rfl⟩, rfl⟩
    exact ⟨n, k, hn, by simp⟩
  · rintro ⟨n, k, hn, rfl⟩
    exact ⟨_, ⟨n, k, hn, rfl⟩, by simp⟩

theorem exists_nat_mul_mem {Ω : Type} [Field Ω] [CharZero Ω] (A : Subalgebra ℤ Ω) {x : Ω}
    (hx : x ∈ Algebra.adjoin ℚ (A : Set Ω)) : ∃ N : ℕ, N ≠ 0 ∧ (N : Ω) * x ∈ A := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | algebraMap r =>
    refine ⟨r.den, r.den_nz, ?_⟩
    have : (r.den : Ω) * algebraMap ℚ Ω r = ((r.num : ℤ) : Ω) := by
      have hd : (r.den : Ω) ≠ 0 := Nat.cast_ne_zero.2 r.den_nz
      rw [eq_ratCast, Rat.cast_def]
      field_simp
    rw [this]
    exact intCast_mem A _
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmy⟩ := hy
    refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
    have : ((n * m : ℕ) : Ω) * (x + y) = (m : Ω) * ((n : Ω) * x) + (n : Ω) * ((m : Ω) * y) := by
      push_cast; ring
    rw [this]
    exact add_mem (mul_mem (natCast_mem A _) hnx) (mul_mem (natCast_mem A _) hmy)
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmy⟩ := hy
    refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
    have : ((n * m : ℕ) : Ω) * (x * y) = ((n : Ω) * x) * ((m : Ω) * y) := by
      push_cast; ring
    rw [this]
    exact mul_mem hnx hmy

theorem isLocalization_adjoin {Ω : Type} [Field Ω] [CharZero Ω] (A : Subalgebra ℤ Ω)
    (S : Subalgebra ℚ Ω) [Algebra A S] (hι : ∀ a : A, ((algebraMap A S a : S) : Ω) = a)
    (c : A) (N : ℕ) (hN : N ≠ 0) (h : Ω) (h0 : h ≠ 0) (hc : (c : Ω) = N * h)
    (hS : S = Algebra.adjoin ℚ (insert h⁻¹ (A : Set Ω))) :
    IsLocalization (denomMonoid c) S := by
  have hNΩ : (N : Ω) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hinv : h⁻¹ ∈ S := hS ▸ Algebra.subset_adjoin (Set.mem_insert _ _)
  have hnat : ∀ n : ℕ, n ≠ 0 → IsUnit (algebraMap A S (n : A)) := by
    intro n hn
    have hnΩ : (n : Ω) ≠ 0 := Nat.cast_ne_zero.2 hn
    refine IsUnit.of_mul_eq_one (algebraMap ℚ S (n : ℚ)⁻¹) (Subtype.ext ?_)
    have h1 : ((algebraMap ℚ S (n : ℚ)⁻¹ : S) : Ω) = (n : Ω)⁻¹ := by
      change algebraMap ℚ Ω (n : ℚ)⁻¹ = _
      simp
    rw [Subalgebra.coe_mul, hι, h1]
    simp [hnΩ]
  have hcu : IsUnit (algebraMap A S c) := by
    refine IsUnit.of_mul_eq_one (algebraMap ℚ S (N : ℚ)⁻¹ * ⟨h⁻¹, hinv⟩) (Subtype.ext ?_)
    have h1 : ((algebraMap ℚ S (N : ℚ)⁻¹ : S) : Ω) = (N : Ω)⁻¹ := by
      change algebraMap ℚ Ω (N : ℚ)⁻¹ = _
      simp
    rw [Subalgebra.coe_mul, Subalgebra.coe_mul, hι, h1, hc]
    simp only [Subalgebra.coe_one]
    field_simp
  have hcmem : c ∈ denomMonoid c := ⟨1, 1, one_ne_zero, by simp⟩
  have hnmem : ∀ n : ℕ, n ≠ 0 → (n : A) ∈ denomMonoid c := fun n hn => ⟨n, 0, hn, by simp⟩
  have key : ∀ w ∈ Algebra.adjoin ℚ (insert h⁻¹ (A : Set Ω)),
      ∃ (a : A) (m : denomMonoid c), w * (((m : A)) : Ω) = a := by
    intro w hw
    induction hw using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · refine ⟨(N : A), ⟨c, hcmem⟩, ?_⟩
        simp only [hc]
        push_cast
        field_simp
      · exact ⟨⟨x, hx⟩, 1, by simp⟩
    | algebraMap r =>
      refine ⟨(r.num : A), ⟨(r.den : A), hnmem _ r.den_nz⟩, ?_⟩
      have hd : (r.den : Ω) ≠ 0 := Nat.cast_ne_zero.2 r.den_nz
      push_cast
      rw [eq_ratCast, Rat.cast_def]
      field_simp
    | add x y _ _ hx hy =>
      obtain ⟨a, m, hx⟩ := hx
      obtain ⟨b, l, hy⟩ := hy
      refine ⟨a * (l : A) + b * (m : A), m * l, ?_⟩
      push_cast
      rw [← hx, ← hy]
      ring
    | mul x y _ _ hx hy =>
      obtain ⟨a, m, hx⟩ := hx
      obtain ⟨b, l, hy⟩ := hy
      refine ⟨a * b, m * l, ?_⟩
      push_cast
      rw [← hx, ← hy]
      ring
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, k, hn, rfl⟩
    simp only [map_mul, map_pow]
    exact (hnat n hn).mul (hcu.pow k)
  · intro z
    obtain ⟨a, m, hz⟩ := key z (hS ▸ z.2)
    refine ⟨(a, m), Subtype.ext ?_⟩
    rw [Subalgebra.coe_mul, hι, hι]
    exact hz
  · intro x y hxy
    refine ⟨1, ?_⟩
    have : (x : Ω) = y := by rw [← hι, ← hι, hxy]
    rw [Subtype.ext this]

end GlobalTheory.CompanionTheory.Ar.LocalisedSmooth

open GlobalTheory.CompanionTheory.Ar.LocalisedSmooth in

theorem GlobalTheory.CompanionTheory.Ar.LocalisedSmooth.smooth_localised
    (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω₀] [CharZero Ω] [Algebra Ω₀ Ω]
    (A₀ : Subalgebra ℤ Ω₀) (A₁ : Subalgebra ℤ Ω) (φ : A₀ →+* A₁)
    (hφ : ∀ a, ((φ a : A₁) : Ω) = algebraMap Ω₀ Ω a) (hsm : φ.Smooth)
    (h : Ω₀) (hh : h ∈ Algebra.adjoin ℚ (A₀ : Set Ω₀)) (h0 : h ≠ 0)
    (S : Subalgebra ℚ Ω₀) (T : Subalgebra ℚ Ω)
    (hS : S = Algebra.adjoin ℚ (insert h⁻¹ (A₀ : Set Ω₀)))
    (hT : T = Algebra.adjoin ℚ (insert (algebraMap Ω₀ Ω h)⁻¹ (A₁ : Set Ω))) :
    ∃ ψ : S →+* T, (∀ s, ((ψ s : T) : Ω) = algebraMap Ω₀ Ω s) ∧ ψ.Smooth := by
  obtain ⟨N, hN, hNh⟩ := exists_nat_mul_mem A₀ hh
  let c₀ : A₀ := ⟨(N : Ω₀) * h, hNh⟩
  have hc₀ : (c₀ : Ω₀) = N * h := rfl
  have hc₁ : ((φ c₀ : A₁) : Ω) = N * algebraMap Ω₀ Ω h := by
    rw [hφ, hc₀, map_mul, map_natCast]
  have hAS : ∀ a : A₀, (a : Ω₀) ∈ S := fun a =>
    hS ▸ Algebra.subset_adjoin (Set.mem_insert_of_mem _ a.2)
  have hAT : ∀ a : A₁, (a : Ω) ∈ T := fun a =>
    hT ▸ Algebra.subset_adjoin (Set.mem_insert_of_mem _ a.2)
  let ι₀ : A₀ →+* S := (A₀.val : A₀ →+* Ω₀).codRestrict S.toSubsemiring hAS
  let ι₁ : A₁ →+* T := (A₁.val : A₁ →+* Ω).codRestrict T.toSubsemiring hAT
  letI : Algebra A₀ S := ι₀.toAlgebra
  letI : Algebra A₁ T := ι₁.toAlgebra
  haveI L₀ : IsLocalization (denomMonoid c₀) S :=
    isLocalization_adjoin A₀ S (fun _ => rfl) c₀ N hN h h0 hc₀ hS
  haveI L₁ : IsLocalization (denomMonoid (φ c₀)) T :=
    isLocalization_adjoin A₁ T (fun _ => rfl) (φ c₀) N hN (algebraMap Ω₀ Ω h)
      ((map_ne_zero _).2 h0) hc₁ hT
  have hle : denomMonoid c₀ ≤ (denomMonoid (φ c₀)).comap φ := by
    intro x hx
    rw [Submonoid.mem_comap, ← map_denomMonoid]
    exact ⟨x, hx, rfl⟩
  let ψ : S →+* T := IsLocalization.map T φ hle
  have hψ : ∀ a : A₀, ψ (algebraMap A₀ S a) = algebraMap A₁ T (φ a) := fun a =>
    IsLocalization.map_eq hle a
  refine ⟨ψ, ?_, ?_⟩
  · have : ((T.val : T →+* Ω).comp ψ) = (algebraMap Ω₀ Ω).comp (S.val : S →+* Ω₀) := by
      refine IsLocalization.ringHom_ext (denomMonoid c₀) (RingHom.ext fun a => ?_)
      change ((ψ (algebraMap A₀ S a) : T) : Ω) = algebraMap Ω₀ Ω (a : Ω₀)
      rw [hψ]
      exact hφ a
    exact fun s => RingHom.congr_fun this s
  · letI : Algebra S T := ψ.toAlgebra
    letI : Algebra A₀ A₁ := φ.toAlgebra
    letI : Algebra A₀ T := ((algebraMap A₁ T).comp φ).toAlgebra
    haveI : IsScalarTower A₀ A₁ T := .of_algebraMap_eq' rfl
    haveI : IsScalarTower A₀ S T := .of_algebraMap_eq fun a => (hψ a).symm
    have hsub : Algebra.algebraMapSubmonoid A₁ (denomMonoid c₀) = denomMonoid (φ c₀) :=
      map_denomMonoid φ c₀
    haveI : IsLocalization (Algebra.algebraMapSubmonoid A₁ (denomMonoid c₀)) T := by
      rw [hsub]; exact L₁
    haveI P : Algebra.IsPushout A₀ A₁ S T :=
      Algebra.isPushout_of_isLocalization (denomMonoid c₀) S A₁ T
    exact RingHom.Smooth.isStableUnderBaseChange A₀ A₁ S T hsm
