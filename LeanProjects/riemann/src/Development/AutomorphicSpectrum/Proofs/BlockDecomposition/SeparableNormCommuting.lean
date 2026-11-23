import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyEqPowOfIrreducible

open Polynomial

namespace GlobalTheory.CompanionTheory.Centraliser

variable {K : Type} [Field K] {n : ℕ}

theorem act_mul (γ : Matrix (Fin n) (Fin n) K) (a b : K[X]) (v : Fin n → K) :
    (aeval γ (a * b)).mulVec v = (aeval γ a).mulVec ((aeval γ b).mulVec v) := by
  rw [map_mul, Matrix.mulVec_mulVec]

theorem charpoly_dvd_of_aeval_eq_zero (γ : Matrix (Fin n) (Fin n) K)
    (hs : γ.charpoly.Separable) {p : K[X]} (hp : aeval γ p = 0) : γ.charpoly ∣ p := by
  have h := GlobalTheory.CharpolyPowIrred.charpoly_dvd_pow_of_aeval γ p hp
  rcases Nat.eq_zero_or_pos (Fintype.card (Fin n)) with h0 | h0
  · rw [h0, pow_zero] at h
    exact h.trans (one_dvd p)
  · exact (hs.squarefree.dvd_pow_iff_dvd h0.ne').1 h

theorem exists_vec_ann (γ : Matrix (Fin n) (Fin n) K) (hs : γ.charpoly.Separable) (q : K[X]) :
    q ∣ γ.charpoly → ∃ v : Fin n → K, (aeval γ q).mulVec v = 0 ∧
      ∀ h : K[X], (aeval γ h).mulVec v = 0 → q ∣ h := by
  have hf0 : γ.charpoly ≠ 0 := γ.charpoly_monic.ne_zero
  refine UniqueFactorizationMonoid.induction_on_prime q ?_ ?_ ?_
  · intro h
    exact absurd (zero_dvd_iff.1 h) hf0
  · intro x hx _
    exact ⟨0, by simp, fun h _ => hx.dvd⟩
  · intro a p ha hp ih hd
    obtain ⟨v', hv1, hv2⟩ := ih ((dvd_mul_left a p).trans hd)
    obtain ⟨g, hg⟩ : p ∣ γ.charpoly := (dvd_mul_right p a).trans hd
    have hgne : g ≠ 0 := by
      rintro rfl
      exact hf0 (by simpa using hg)
    have hg0 : aeval γ g ≠ 0 := fun h => by
      obtain ⟨c, hc⟩ := charpoly_dvd_of_aeval_eq_zero γ hs h
      rw [hg] at hc
      have h1 : g * (p * c) = g * 1 := by
        rw [mul_one]
        calc g * (p * c) = p * g * c := by ring
          _ = g := hc.symm
      exact hp.not_unit (IsUnit.of_mul_eq_one _ (mul_left_cancel₀ hgne h1))
    obtain ⟨u, hu⟩ : ∃ u, (aeval γ g).mulVec u ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hg0 (Matrix.mulVec_injective (funext fun u => by simpa using hcon u))
    set w := (aeval γ g).mulVec u with hw
    have hpw : (aeval γ p).mulVec w = 0 := by
      rw [hw, ← act_mul, ← hg, Matrix.aeval_self_charpoly, Matrix.zero_mulVec]
    have hkey : ∀ h : K[X], (aeval γ h).mulVec w = 0 → p ∣ h := by
      intro h hh
      by_contra hnd
      obtain ⟨s, t, hst⟩ := (Prime.coprime_iff_not_dvd hp).2 hnd
      apply hu
      have h1 : (aeval γ (s * p + t * h)).mulVec w = w := by
        rw [hst]; simp
      rw [map_add, Matrix.add_mulVec, act_mul, act_mul, hpw, hh] at h1
      simpa using h1.symm
    have hpa : ¬ p ∣ a := by
      rintro ⟨c, rfl⟩
      exact hp.not_unit (hs.squarefree p
        ((mul_dvd_mul_left p (dvd_mul_right p c)).trans hd))
    have hcop : IsCoprime p a := (Prime.coprime_iff_not_dvd hp).2 hpa
    refine ⟨v' + w, ?_, ?_⟩
    · rw [Matrix.mulVec_add, act_mul, hv1, mul_comm, act_mul, hpw]
      simp
    · intro h hh
      have h1 : (aeval γ (h * p)).mulVec v' = 0 := by
        have h2 : (aeval γ (h * p)).mulVec (v' + w) = 0 := by
          rw [mul_comm, act_mul, hh, Matrix.mulVec_zero]
        rw [Matrix.mulVec_add, act_mul γ h p w, hpw, Matrix.mulVec_zero, add_zero] at h2
        exact h2
      have hah : a ∣ h := hcop.symm.dvd_of_dvd_mul_right (hv2 _ h1)
      obtain ⟨c, rfl⟩ := hah
      have h3 : (aeval γ (a * c)).mulVec v' = 0 := by
        rw [mul_comm, act_mul, hv1]; simp
      rw [Matrix.mulVec_add, h3, zero_add] at hh
      exact hcop.mul_dvd (hkey _ hh) (dvd_mul_right a c)

theorem exists_cyclic_vec (γ : Matrix (Fin n) (Fin n) K) (hs : γ.charpoly.Separable) :
    ∃ v : Fin n → K, ∀ w : Fin n → K, ∃ q : K[X], (aeval γ q).mulVec v = w := by
  obtain ⟨v, -, hv⟩ := exists_vec_ann γ hs γ.charpoly dvd_rfl
  refine ⟨v, ?_⟩
  let L : K[X] →ₗ[K] (Fin n → K) :=
    { toFun := fun p => (aeval γ p).mulVec v
      map_add' := fun a b => by rw [map_add, Matrix.add_mulVec]
      map_smul' := fun c a => by rw [map_smul, Matrix.smul_mulVec]; rfl }
  let φ : degreeLT K n →ₗ[K] (Fin n → K) := L.domRestrict (degreeLT K n)
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨p, hp⟩ h0
    have hd : γ.charpoly ∣ p := hv p h0
    have hlt : p.degree < γ.charpoly.degree := by
      rw [Matrix.charpoly_degree_eq_dim, Fintype.card_fin]
      exact Polynomial.mem_degreeLT.1 hp
    exact Subtype.ext (Polynomial.eq_zero_of_dvd_of_degree_lt hd hlt)
  have hfr : Module.finrank K (degreeLT K n) = Module.finrank K (Fin n → K) :=
    (degreeLTEquiv K n).finrank_eq
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).1 hinj
  intro w
  obtain ⟨⟨q, _⟩, hq⟩ := hsurj w
  exact ⟨q, hq⟩

theorem a1 : PositivityTheory.Rg.Tf.Loc.A1 := by
  intro K _ n γ hs M hM
  obtain ⟨v, hv⟩ := exists_cyclic_vec γ hs
  obtain ⟨p, hp⟩ := hv (M.mulVec v)
  refine ⟨p, Matrix.mulVec_injective (funext fun w => ?_)⟩
  obtain ⟨q, rfl⟩ := hv w
  have hc : Commute M (aeval γ q) := by
    rw [aeval_eq_sum_range]
    exact Commute.sum_right _ _ _ fun i _ => (hM.pow_right i).smul_right _
  rw [Matrix.mulVec_mulVec, hc.eq, ← Matrix.mulVec_mulVec, ← hp, ← act_mul, mul_comm, act_mul]

end GlobalTheory.CompanionTheory.Centraliser
