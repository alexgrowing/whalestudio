import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivCompM

open GlobalTheory.Nef

namespace GlobalTheory.Nef.PathJet

open PowerSeries

theorem ringHom_lift_sqZero {B A O R' : Type} [CommRing B] [CommRing A] [CommRing O] [CommRing R'] (α : B →+* A)
    (hα : α.FormallySmooth) (π : R' →+* O) (hs : Function.Surjective π) (hk : RingHom.ker π ^ 2 = ⊥)
    (β' : B →+* R') (χ : A →+* O) (hc : χ.comp α = π.comp β') :
    ∃ χ' : A →+* R', π.comp χ' = χ ∧ χ'.comp α = β' := by
  letI := α.toAlgebra
  letI := β'.toAlgebra
  letI := (π.comp β').toAlgebra
  haveI : Algebra.FormallySmooth B A := hα
  let π₁ : R' →ₐ[B] O := { π with commutes' := fun _ => rfl }
  let χ₁ : A →ₐ[B] O := { χ with commutes' := fun b => RingHom.congr_fun hc b }
  have hn : IsNilpotent (RingHom.ker (π₁ : R' →+* O)) := ⟨2, hk⟩
  refine ⟨(Algebra.FormallySmooth.liftOfSurjective χ₁ π₁ hs hn : A →+* R'), RingHom.ext fun a => ?_,
    RingHom.ext fun b => (Algebra.FormallySmooth.liftOfSurjective χ₁ π₁ hs hn).commutes b⟩
  exact Algebra.FormallySmooth.liftOfSurjective_apply χ₁ π₁ hs hn a

theorem mk_eq_iff_X_pow_dvd {R : Type} [CommRing R] (k : ℕ) (x y : PowerSeries R) :
    Ideal.Quotient.mk (Ideal.span {(X : PowerSeries R) ^ k}) x =
      Ideal.Quotient.mk (Ideal.span {(X : PowerSeries R) ^ k}) y ↔ (X : PowerSeries R) ^ k ∣ x - y := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]

noncomputable def quotRingHom {A B R : Type} [CommRing A] [CommRing B] [CommRing R] (π : B →+* A) (β : B →+* R) (n : ℕ)
    (φ : A → PowerSeries R) (hφ : IsRingHomMod π β n φ) :
    A →+* PowerSeries R ⧸ Ideal.span {(X : PowerSeries R) ^ n} where
  toFun f := Ideal.Quotient.mk _ (φ f)
  map_one' := by rw [← map_one (Ideal.Quotient.mk _), mk_eq_iff_X_pow_dvd]; exact hφ.2.2.1
  map_mul' f g := by rw [← map_mul, mk_eq_iff_X_pow_dvd]; exact hφ.1 f g
  map_zero' := by
    rw [← map_zero (Ideal.Quotient.mk _), mk_eq_iff_X_pow_dvd]
    have := hφ.2.1 0 0
    simp only [add_zero] at this
    simpa using this
  map_add' f g := by rw [← map_add, mk_eq_iff_X_pow_dvd]; exact hφ.2.1 f g

theorem ker_factor_sq {R : Type} [CommRing R] (n : ℕ) (hn : 1 ≤ n)
    (hle : Ideal.span {(X : PowerSeries R) ^ (n + 1)} ≤ Ideal.span {(X : PowerSeries R) ^ n}) :
    RingHom.ker (Ideal.Quotient.factor hle) ^ 2 = ⊥ := by
  have hker : ∀ z ∈ RingHom.ker (Ideal.Quotient.factor hle), ∃ x, (X : PowerSeries R) ^ n ∣ x ∧
      Ideal.Quotient.mk (Ideal.span {(X : PowerSeries R) ^ (n + 1)}) x = z := by
    intro z hz
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    refine ⟨x, ?_, rfl⟩
    rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, ← map_zero (Ideal.Quotient.mk _), mk_eq_iff_X_pow_dvd,
      sub_zero] at hz
    exact hz
  rw [pow_two, eq_bot_iff]
  refine Ideal.mul_le.2 fun a ha b hb => ?_
  obtain ⟨x, hx, rfl⟩ := hker a ha
  obtain ⟨y, hy, rfl⟩ := hker b hb
  rw [Ideal.mem_bot, ← map_mul, ← map_zero (Ideal.Quotient.mk _), mk_eq_iff_X_pow_dvd, sub_zero]
  have h2 : (X : PowerSeries R) ^ (n + n) ∣ x * y := by rw [pow_add]; exact mul_dvd_mul hx hy
  exact (pow_dvd_pow _ (by omega : n + 1 ≤ n + n)).trans h2

theorem exists_lift_succ : ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] (π : B →+* A) (β : B →+* R), π.FormallySmooth → ∀ n : ℕ, 1 ≤ n → ∀ φ : A → PowerSeries R, GlobalTheory.Nef.PathJet.IsRingHomMod π β n φ → ∃ ψ : A → PowerSeries R, GlobalTheory.Nef.PathJet.IsRingHomMod π β (n + 1) ψ ∧ ∀ f, (PowerSeries.X : PowerSeries R) ^ n ∣ ψ f - φ f := by
  intro A B R _ _ _ π β hπ n hn φ hφ
  have hle : Ideal.span {(X : PowerSeries R) ^ (n + 1)} ≤ Ideal.span {(X : PowerSeries R) ^ n} := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_span_singleton]
    exact pow_dvd_pow _ (Nat.le_succ n)
  have hs : Function.Surjective (Ideal.Quotient.factor hle) := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨_, Ideal.Quotient.factor_mk hle x⟩
  have hc : (quotRingHom π β n φ hφ).comp π =
      (Ideal.Quotient.factor hle).comp ((Ideal.Quotient.mk _).comp ((C : R →+* PowerSeries R).comp β)) := by
    ext b
    change Ideal.Quotient.mk _ (φ (π b)) = Ideal.Quotient.factor hle (Ideal.Quotient.mk _ (C (β b)))
    rw [Ideal.Quotient.factor_mk, mk_eq_iff_X_pow_dvd]
    exact hφ.2.2.2 b
  obtain ⟨χ', h₁, h₂⟩ := ringHom_lift_sqZero π hπ _ hs (ker_factor_sq n hn hle) _ _ hc
  choose ψ hψ using fun f => Ideal.Quotient.mk_surjective (χ' f)
  refine ⟨ψ, ⟨fun f g => ?_, fun f g => ?_, ?_, fun b => ?_⟩, fun f => ?_⟩
  · rw [← mk_eq_iff_X_pow_dvd, map_mul, hψ, hψ, hψ, map_mul]
  · rw [← mk_eq_iff_X_pow_dvd, map_add, hψ, hψ, hψ, map_add]
  · rw [← mk_eq_iff_X_pow_dvd, map_one, hψ, map_one]
  · rw [← mk_eq_iff_X_pow_dvd, hψ, ← RingHom.comp_apply χ' π, h₂]; rfl
  · rw [← mk_eq_iff_X_pow_dvd, ← Ideal.Quotient.factor_mk hle, hψ, ← RingHom.comp_apply, h₁]; rfl

end GlobalTheory.Nef.PathJet
