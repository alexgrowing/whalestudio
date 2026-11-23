import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingCyclotomicTowerLevel
open GlobalTheory.K5

noncomputable section

namespace GlobalTheory.K5.TraceTower

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem zeta_pow (T : Tower p Ω) (m k : ℕ) : T.ζ (m + k) ^ (p ^ k) = T.ζ m := by
  induction k with
  | zero => simp
  | succ k ih => rw [← Nat.add_assoc, pow_succ', pow_mul, T.ζpow, ih]

theorem qq_pow (T : Tower p Ω) (m k : ℕ) : T.qq (m + k) ^ (p ^ k) = T.qq m := by
  induction k with
  | zero => simp
  | succ k ih => rw [← Nat.add_assoc, pow_succ', pow_mul, T.qpow, ih]

theorem zeta_pow' (T : Tower p Ω) {m n : ℕ} (h : m ≤ n) : T.ζ n ^ (p ^ (n - m)) = T.ζ m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  simpa using zeta_pow T m k

theorem qq_pow' (T : Tower p Ω) {m n : ℕ} (h : m ≤ n) : T.qq n ^ (p ^ (n - m)) = T.qq m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  simpa using qq_pow T m k

theorem qq_pow_top (T : Tower p Ω) (n : ℕ) : T.qq n ^ (p ^ n) = algebraMap (O0 p) Ω (qO p) := by
  have := qq_pow' T (Nat.zero_le n)
  simpa [T.q0] using this

theorem geo (ω : Ω) (K : ℕ) (hω : IsPrimitiveRoot ω K) (i : ℕ) :
    ∑ c ∈ Finset.range K, (ω ^ i) ^ c = if K ∣ i then (K : Ω) else 0 := by
  split_ifs with h
  · rw [(hω.pow_eq_one_iff_dvd i).2 h]; simp
  · have h1 : ω ^ i ≠ 1 := fun e => h ((hω.pow_eq_one_iff_dvd i).1 e)
    have h2 := geom_sum_mul (ω ^ i) K
    have h3 : (ω ^ i) ^ K = 1 := by rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
    rw [h3, sub_self] at h2
    exact (mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 h1)

theorem lift_hom {R A S M : Type} [CommRing R] [CommRing A] [IsDomain A] [Algebra R A] [Field S]
    [Algebra R S] [Algebra.IsAlgebraic R S] [Field M] [IsAlgClosed M]
    (hA : Function.Injective (algebraMap R A)) (ι : A →ₐ[R] S) (f : A →+* M)
    (hι : Function.Injective ι) (hf : Function.Injective f) :
    ∃ τ : S →+* M, ∀ x, τ (ι x) = f x := by
  letI : Algebra A S := ι.toRingHom.toAlgebra
  letI : Algebra A M := f.toAlgebra
  haveI : IsScalarTower R A S := IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  haveI : Algebra.IsAlgebraic A S := Algebra.IsAlgebraic.extendScalars (R := R) hA
  haveI : Module.IsTorsionFree A S := Module.isTorsionFree_iff_algebraMap_injective.2 hι
  haveI : Module.IsTorsionFree A M := Module.isTorsionFree_iff_algebraMap_injective.2 hf
  let L : S →ₐ[A] M := IsAlgClosed.lift
  exact ⟨L.toRingHom, fun x => L.commutes x⟩

theorem ext_aut (hΩ : IsClo p Ω) {A : Type} [CommRing A] [IsDomain A] [Algebra (O0 p) A]
    [Algebra.IsIntegral (O0 p) A] (ι f : A →ₐ[O0 p] Ω) :
    ∃ σ : Gal p Ω, ∀ x : A, σ (ι x) = f x := by
  haveI := hΩ.clo
  haveI := hΩ.alg
  haveI : IsDomain (O0 p) := hΩ.inj.isDomain _
  have hinj : ∀ g : A →ₐ[O0 p] Ω, Function.Injective g := by
    intro g
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := O0 p) ?_
    rw [eq_bot_iff]
    intro r hr
    rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes] at hr
    exact hΩ.inj (by rw [hr, map_zero])
  have hA : Function.Injective (algebraMap (O0 p) A) := by
    intro x y hxy
    apply hΩ.inj
    rw [← ι.commutes, ← ι.commutes, hxy]
  obtain ⟨τ, hτ⟩ := lift_hom hA ι f.toRingHom (hinj ι) (hinj f)
  let τ' : Ω →ₐ[O0 p] Ω :=
    { τ with
      commutes' := fun r => by
        show τ _ = _
        rw [← ι.commutes, hτ, ι.commutes]
        exact f.commutes r }
  haveI : Module.IsTorsionFree (O0 p) Ω := Module.isTorsionFree_iff_algebraMap_injective.2 hΩ.inj
  exact ⟨AlgEquiv.ofBijective τ' (Algebra.IsAlgebraic.algHom_bijective τ'), hτ⟩

open Polynomial in

theorem exists_hom (T : Tower p Ω) (n : ℕ) (a b : ℕ) (ha : ¬ p ∣ a) :
    ∃ f : On p n →ₐ[O0 p] Ω, f (xn p n) = T.ζ n ^ a ∧ f (yn p n) = T.ζ n ^ b * T.qq n := by
  classical
  have hp := (Fact.out : p.Prime)
  have hcop : a.Coprime (p ^ n) :=
    Nat.Coprime.pow_right n (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 ha))
  have hprim : IsPrimitiveRoot (T.ζ n ^ a) (p ^ n) := (T.prim n).pow_of_coprime a hcop
  let φ : Polynomial (Polynomial (O0 p)) →ₐ[O0 p] Ω :=
    aevalTower (aeval (T.ζ n ^ a)) (T.ζ n ^ b * T.qq n)
  have hle : towerIdeal p n ≤ RingHom.ker φ := by
    refine Ideal.span_le.2 ?_
    rintro x (rfl | rfl)
    · rw [SetLike.mem_coe, RingHom.mem_ker]
      show aevalTower (aeval (T.ζ n ^ a)) (T.ζ n ^ b * T.qq n) (C (cyclotomic (p ^ n) (O0 p))) = 0
      rw [aevalTower_C, aeval_def, ← eval_map, map_cyclotomic]
      exact hprim.isRoot_cyclotomic (pow_pos hp.pos n)
    · rw [SetLike.mem_coe, RingHom.mem_ker]
      show aevalTower (aeval (T.ζ n ^ a)) (T.ζ n ^ b * T.qq n) (X ^ (p ^ n) - C (C (qO p))) = 0
      rw [map_sub, map_pow, aevalTower_X, aevalTower_C, aeval_C, mul_pow, qq_pow_top, ← pow_mul,
        mul_comm b, pow_mul, (T.prim n).pow_eq_one, one_pow, one_mul, sub_self]
  let f0 : On p n →ₐ[O0 p] Ω := Ideal.Quotient.liftₐ (towerIdeal p n) φ (fun x hx => (RingHom.mem_ker).1 (hle hx))
  have hf0x : f0 (xn p n) = T.ζ n ^ a := by
    show aevalTower (aeval (T.ζ n ^ a)) (T.ζ n ^ b * T.qq n) (C X) = _
    rw [aevalTower_C, aeval_X]
  have hf0y : f0 (yn p n) = T.ζ n ^ b * T.qq n := by
    show aevalTower (aeval (T.ζ n ^ a)) (T.ζ n ^ b * T.qq n) X = _
    rw [aevalTower_X]
  exact ⟨f0, hf0x, hf0y⟩

theorem exists_aut (hΩ : IsClo p Ω) (T : Tower p Ω) (n : ℕ) (hn : 1 ≤ n) (a b : ℕ) (ha : ¬ p ∣ a) :
    ∃ σ : Gal p Ω, σ (T.ζ n) = T.ζ n ^ a ∧ σ (T.qq n) = T.ζ n ^ b * T.qq n := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨ι, hx, hy⟩ := exists_hom T n 1 0 hp.not_dvd_one
  obtain ⟨f, hfx, hfy⟩ := exists_hom T n a b ha
  obtain ⟨_, -⟩ := GlobalTheory.K5.OnDVR.isDVR_On p n hn
  obtain ⟨B, -⟩ := GlobalTheory.K5.OnFree.on_free p n
  haveI : Module.Finite (O0 p) (On p n) := Module.Finite.of_basis B
  haveI : Algebra.IsIntegral (O0 p) (On p n) := Algebra.IsIntegral.of_finite (O0 p) (On p n)
  obtain ⟨σ, key⟩ := ext_aut hΩ ι f
  have k1 := key (xn p n)
  have k2 := key (yn p n)
  rw [hx, hfx, pow_one] at k1
  rw [hy, hfy, pow_zero, one_mul] at k2
  exact ⟨σ, k1, k2⟩

theorem gms_iff {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω] (T : Tower p Ω)
    (m s : ℕ) (g : Gal p Ω) : g ∈ Gms T m s ↔ g (T.ζ m) = T.ζ m ∧ g (T.qq s) = T.qq s := by
  rw [Gms, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff,
    AlgEquiv.smul_def, AlgEquiv.smul_def]

end GlobalTheory.K5.TraceTower
