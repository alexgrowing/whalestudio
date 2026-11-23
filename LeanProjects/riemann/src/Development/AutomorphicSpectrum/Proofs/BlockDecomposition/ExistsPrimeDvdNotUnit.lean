import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPderivNotDvd
set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.CompanionTheory.TraceJac

theorem exists_prime_dvd_not_unit {P A : Type*} [CommRing P] [IsDomain P]
    [UniqueFactorizationMonoid P] [CommRing A] (φ : P →+* A) (g : P) (hg : g ≠ 0)
    (h : ¬ IsUnit (φ g)) : ∃ π, Prime π ∧ π ∣ g ∧ ¬ IsUnit (φ π) := by
  revert hg h
  refine UniqueFactorizationMonoid.induction_on_prime g ?_ ?_ ?_
  · intro h0
    exact absurd rfl h0
  · intro x hx _ hxu
    exact absurd (hx.map φ) hxu
  · intro a p ha hp ih _ hpa
    by_cases hpu : IsUnit (φ p)
    · have hau : ¬ IsUnit (φ a) := fun hau => hpa (by rw [map_mul]; exact hpu.mul hau)
      obtain ⟨π, hπ, hπa, hπu⟩ := ih ha hau
      exact ⟨π, hπ, dvd_mul_of_dvd_right hπa p, hπu⟩
    · exact ⟨p, hp, dvd_mul_right p a, hpu⟩

section
variable {P A F L n : Type*} [CommRing P] [IsDomain P] [UniqueFactorizationMonoid P]
  [IsNoetherianRing P] [CommRing A] [IsDomain A] [Algebra P A] [Field F] [Algebra A F]
  [IsFractionRing A F] [Algebra P F] [IsScalarTower P A F] [Field L] [Algebra F L] [Algebra A L]
  [IsScalarTower A F L] [Algebra P L] [IsScalarTower P F L] [FiniteDimensional F L]
  [Algebra.IsSeparable F L] [Fintype n] [DecidableEq n]

theorem main_abs (hinj : Function.Injective (algebraMap P A))
    (hloc : ∀ a : A, ∃ f g : P, IsUnit (algebraMap P A g) ∧ a * algebraMap P A g = algebraMap P A f)
    (E : n → Derivation ℤ L L) (hE : ∀ k f, ∃ f', E k (algebraMap P L f) = algebraMap P L f')
    (hjac : ∀ π : P, Prime π → ∃ j fj, E j (algebraMap P L π) = algebraMap P L fj ∧ ¬ π ∣ fj)
    (hnat : ∀ m : ℕ, m ≠ 0 → IsUnit (m : P))
    (c : L) (hc : IsIntegral A c) (b : n → L) (hb : ∀ l, IsIntegral A (b l)) :
    ∃ a : A, algebraMap A F a = Algebra.trace F L (c * (Matrix.of fun k l => E k (b l)).det) := by
  classical
  have hPF_inj : Function.Injective (algebraMap P F) := by
    rw [IsScalarTower.algebraMap_eq P A F]
    exact (IsFractionRing.injective A F).comp hinj
  have hne : ∀ g : P, IsUnit (algebraMap P A g) → algebraMap P F g ≠ 0 := by
    intro g hg h0
    have hg0 : g ≠ 0 := by
      rintro rfl
      simp at hg
    exact hg0 (hPF_inj (h0.trans (map_zero _).symm))
  have hloc' : ∀ a : A, ∃ f g : P, algebraMap P F g ≠ 0 ∧
      algebraMap A F a * algebraMap P F g = algebraMap P F f := by
    intro a
    obtain ⟨f, g, hg, hfg⟩ := hloc a
    refine ⟨f, g, hne g hg, ?_⟩
    rw [IsScalarTower.algebraMap_apply P A F g, IsScalarTower.algebraMap_apply P A F f, ← map_mul, hfg]
  haveI : IsFractionRing P F := by
    haveI : FaithfulSMul P F := (faithfulSMul_iff_algebraMap_injective P F).2 hPF_inj
    refine IsFractionRing.of_field P F (fun z => ?_)
    obtain ⟨a, a', -, rfl⟩ := IsFractionRing.div_surjective (A := A) z
    obtain ⟨f, g, hg, e1⟩ := hloc' a
    obtain ⟨f', g', hg', e2⟩ := hloc' a'
    refine ⟨f * g', g * f', ?_⟩
    rw [map_mul, map_mul, ← e1, ← e2]
    rw [show algebraMap A F a * algebraMap P F g * algebraMap P F g' /
        (algebraMap P F g * (algebraMap A F a' * algebraMap P F g')) =
        algebraMap A F a * (algebraMap P F g * algebraMap P F g') /
        (algebraMap A F a' * (algebraMap P F g * algebraMap P F g')) by ring]
    rw [mul_div_mul_right _ _ (mul_ne_zero hg hg')]
  have key : ∀ π : P, Prime π → ¬ IsUnit (algebraMap P A π) →
      ∃ f s : P, ¬ π ∣ s ∧ algebraMap P F s *
        Algebra.trace F L (c * (Matrix.of fun k l => E k (b l)).det) = algebraMap P F f := by
    intro π hπ hπu
    obtain ⟨j, fj, hfj, hj⟩ := hjac π hπ
    set p : Ideal P := Ideal.span {π} with hp
    haveI hpp : p.IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).2 hπ
    let R : Subalgebra P F :=
      Localization.subalgebra.ofField F p.primeCompl p.primeCompl_le_nonZeroDivisors
    haveI : IsScalarTower R F L := inferInstance
    haveI : IsScalarTower P R L := inferInstance
    haveI : IsLocalization.AtPrime R p := inferInstance
    have hr : ∀ a : A, algebraMap A L a ∈ (algebraMap R L).range := by
      intro a
      obtain ⟨f, g, hg, hfg⟩ := hloc a
      have hgp : g ∈ p.primeCompl := by
        intro hgmem
        apply hπu
        obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.1 hgmem
        rw [map_mul] at hg
        exact isUnit_of_mul_isUnit_right hg
      refine ⟨IsLocalization.mk' R f ⟨g, hgp⟩, ?_⟩
      have h1 : algebraMap R F (IsLocalization.mk' R f ⟨g, hgp⟩) * algebraMap P F g = algebraMap P F f := by
        rw [IsScalarTower.algebraMap_apply P R F g, IsScalarTower.algebraMap_apply P R F f, ← map_mul,
          IsLocalization.mk'_spec]
      have h2 : algebraMap A F a * algebraMap P F g = algebraMap P F f := by
        rw [IsScalarTower.algebraMap_apply P A F g, IsScalarTower.algebraMap_apply P A F f, ← map_mul, hfg]
      have h3 : algebraMap R F (IsLocalization.mk' R f ⟨g, hgp⟩) = algebraMap A F a :=
        mul_right_cancel₀ (hne g hg) (h1.trans h2.symm)
      show algebraMap F L (algebraMap R F _) = _
      rw [h3, ← IsScalarTower.algebraMap_apply A F L]
    have hcR := integral_of_range hr c hc
    have hbR : ∀ l, IsIntegral R (b l) := fun l => integral_of_range hr (b l) (hb l)
    have hnatR : ∀ m : ℕ, m ≠ 0 → IsUnit (m : R) := fun m hm => by
      simpa using (hnat m hm).map (algebraMap P R)
    exact at_prime_abs (R := R) π hπ p hp E hE j fj hfj hj hnatR c hcR b hbR
  obtain ⟨n0, d0, hrel, hx0⟩ := IsFractionRing.exists_reduced_fraction (A := P)
    (Algebra.trace F L (c * (Matrix.of fun k l => E k (b l)).det))
  have hd0 : (d0 : P) ≠ 0 := nonZeroDivisors.coe_ne_zero d0
  have hxd : Algebra.trace F L (c * (Matrix.of fun k l => E k (b l)).det) * algebraMap P F d0 =
      algebraMap P F n0 := by
    rw [← hx0]
    exact IsLocalization.mk'_spec F n0 d0
  by_cases hu : IsUnit (algebraMap P A d0)
  · obtain ⟨u, hu'⟩ := hu
    refine ⟨algebraMap P A n0 * ((u⁻¹ : Aˣ) : A), ?_⟩
    have hdF : algebraMap A F (algebraMap P A d0) = algebraMap P F d0 :=
      (IsScalarTower.algebraMap_apply P A F d0).symm
    have hnF : algebraMap A F (algebraMap P A n0) = algebraMap P F n0 :=
      (IsScalarTower.algebraMap_apply P A F n0).symm
    have hinv : algebraMap A F ((u⁻¹ : Aˣ) : A) * algebraMap P F d0 = 1 := by
      rw [← hdF, ← hu', ← map_mul, Units.inv_mul, map_one]
    rw [map_mul, hnF, ← hxd, mul_assoc, mul_comm (algebraMap P F _), hinv, mul_one]
  · obtain ⟨π, hπ, hπd, hπu⟩ := exists_prime_dvd_not_unit (algebraMap P A) (d0 : P) hd0 hu
    obtain ⟨f, s, hs, hfs⟩ := key π hπ hπu
    exfalso
    have h1 : algebraMap P F (s * n0) = algebraMap P F (f * d0) := by
      rw [map_mul, map_mul, ← hxd, ← hfs]
      ring
    have h2 := hPF_inj h1
    have hπn : π ∣ n0 := by
      have : π ∣ s * n0 := by
        rw [h2]
        exact dvd_mul_of_dvd_right hπd f
      exact (hπ.dvd_or_dvd this).resolve_left hs
    exact hπ.not_isUnit (hrel hπn hπd)
end

end GlobalTheory.CompanionTheory.TraceJac

namespace GlobalTheory.CompanionTheory.TraceJac

theorem deriv_aeval_mv {K L : Type*} [Field K] [Field L] [Algebra K L] {d : ℕ} (τ : Fin d → L)
    (D : Derivation K L L) (k : Fin d) (hD : ∀ j, D (τ j) = if k = j then 1 else 0)
    (f : MvPolynomial (Fin d) K) :
    D (MvPolynomial.aeval τ f) = MvPolynomial.aeval τ (MvPolynomial.pderiv k f) := by
  induction f using MvPolynomial.induction_on
  next a =>
    simp [MvPolynomial.aeval_C, MvPolynomial.pderiv_C]
  next p q hp hq =>
    simp only [map_add, hp, hq]
  next p i hp =>
    simp only [map_mul, Derivation.leibniz, hp, MvPolynomial.aeval_X, hD, smul_eq_mul,
      MvPolynomial.pderiv_X, map_add]
    by_cases hki : k = i
    · subst hki
      simp
    · simp [hki, Pi.single_apply, Ne.symm hki]

theorem trace_jacobian_mem : ∀ (K : Type) [Field K] [CharZero K] (d : ℕ) (A : Type) [CommRing A] [IsDomain A] [Algebra K A] (t : Fin d → A), Function.Injective (MvPolynomial.aeval t : MvPolynomial (Fin d) K →ₐ[K] A) → (∀ a : A, ∃ f g : MvPolynomial (Fin d) K, IsUnit (MvPolynomial.aeval t g) ∧ a * MvPolynomial.aeval t g = MvPolynomial.aeval t f) → ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra A B] [Algebra K B] [IsScalarTower K A B] [Module.Finite A B], Function.Injective (algebraMap A B) → ∀ (F L : Type) [Field F] [Field L] [Algebra A F] [IsFractionRing A F] [Algebra B L] [IsFractionRing B L] [Algebra F L] [Algebra A L] [IsScalarTower A F L] [IsScalarTower A B L] [Algebra K L] [IsScalarTower K B L] (D : Fin d → Derivation K L L), (∀ k j, D k (algebraMap A L (t j)) = if k = j then 1 else 0) → ∀ (c : B) (b : Fin d → B), ∃ a : A, algebraMap A F a = Algebra.trace F L (algebraMap B L c * (Matrix.of fun k l => D k (algebraMap B L (b l))).det) := by
  intro K _ _ d A _ _ _ t ht hloc B _ _ _ _ _ _ hAB F L _ _ _ _ _ _ _ _ _ _ _ _ D hD c b
  classical
  letI : Algebra (MvPolynomial (Fin d) K) A := (MvPolynomial.aeval t).toRingHom.toAlgebra
  letI : Algebra (MvPolynomial (Fin d) K) F :=
    ((algebraMap A F).comp (MvPolynomial.aeval t).toRingHom).toAlgebra
  letI : Algebra (MvPolynomial (Fin d) K) L :=
    ((algebraMap A L).comp (MvPolynomial.aeval t).toRingHom).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin d) K) A F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower (MvPolynomial (Fin d) K) F L := IsScalarTower.of_algebraMap_eq (fun x => by
    show algebraMap A L _ = algebraMap F L (algebraMap A F _)
    exact IsScalarTower.algebraMap_apply A F L _)
  haveI : IsScalarTower K A L := IsScalarTower.of_algebraMap_eq (fun x => by
    rw [IsScalarTower.algebraMap_apply K B L, IsScalarTower.algebraMap_apply K A B,
      ← IsScalarTower.algebraMap_apply A B L])
  haveI : FiniteDimensional F L := finite_frac (A := A) (B := B)
  haveI : CharZero A := (RingHom.charZero_iff (algebraMap K A).injective).1 inferInstance
  haveI : CharZero F := (RingHom.charZero_iff (IsFractionRing.injective A F)).1 inferInstance
  haveI : Algebra.IsSeparable F L := inferInstance
  have hτ : ∀ f : MvPolynomial (Fin d) K, algebraMap (MvPolynomial (Fin d) K) L f =
      MvPolynomial.aeval (fun i => algebraMap A L (t i)) f := by
    intro f
    show algebraMap A L (MvPolynomial.aeval t f) = _
    rw [← MvPolynomial.aeval_algebraMap_apply]
    rfl
  have hE : ∀ (k : Fin d) (f : MvPolynomial (Fin d) K), ∃ f',
      ((D k).restrictScalars ℤ) (algebraMap (MvPolynomial (Fin d) K) L f) =
        algebraMap (MvPolynomial (Fin d) K) L f' := by
    intro k f
    refine ⟨MvPolynomial.pderiv k f, ?_⟩
    rw [hτ, hτ]
    exact deriv_aeval_mv _ (D k) k (fun j => hD k j) f
  have hjac : ∀ π : MvPolynomial (Fin d) K, Prime π → ∃ j fj,
      ((D j).restrictScalars ℤ) (algebraMap (MvPolynomial (Fin d) K) L π) =
        algebraMap (MvPolynomial (Fin d) K) L fj ∧ ¬ π ∣ fj := by
    intro π hπ
    obtain ⟨j, hj⟩ := exists_pderiv_not_dvd π hπ
    refine ⟨j, MvPolynomial.pderiv j π, ?_, hj⟩
    rw [hτ, hτ]
    exact deriv_aeval_mv _ (D j) j (fun i => hD j i) π
  have hnat : ∀ m : ℕ, m ≠ 0 → IsUnit (m : MvPolynomial (Fin d) K) := by
    intro m hm
    have hmK : IsUnit (m : K) := (Nat.cast_ne_zero.2 hm).isUnit
    simpa using hmK.map (MvPolynomial.C : K →+* MvPolynomial (Fin d) K)
  have hc : IsIntegral A (algebraMap B L c) :=
    (Algebra.IsIntegral.isIntegral (R := A) c).map (IsScalarTower.toAlgHom A B L)
  have hb : ∀ l, IsIntegral A (algebraMap B L (b l)) := fun l =>
    (Algebra.IsIntegral.isIntegral (R := A) (b l)).map (IsScalarTower.toAlgHom A B L)
  obtain ⟨a, ha⟩ := main_abs (P := MvPolynomial (Fin d) K) (A := A) (F := F) (L := L) (n := Fin d)
    ht hloc (fun k => (D k).restrictScalars ℤ) hE hjac hnat (algebraMap B L c) hc
    (fun l => algebraMap B L (b l)) hb
  exact ⟨a, ha⟩

end GlobalTheory.CompanionTheory.TraceJac
