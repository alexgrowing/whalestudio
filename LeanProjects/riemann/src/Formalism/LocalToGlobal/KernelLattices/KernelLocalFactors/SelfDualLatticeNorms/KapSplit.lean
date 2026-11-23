import Formalism.LocalToGlobal.KernelLattices.KerStd
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.BaseEx
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import Formalism.LocalToGlobal.GlobalTheory.GL3.NormNatCoprime

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.KS

open Formalism.MainNotions Formalism.FrobeniusOrbits

variable {D : D7}

theorem detRel_unitary (γ γ₀ : IsoK D) :
    D.host.φ₀ ((γ.detRel γ₀ : D.host.K) : D.host.E) *
      (starRingEnd ℂ) (D.host.φ₀ ((γ.detRel γ₀ : D.host.K) : D.host.E)) = 1 := by
  set T : (Fin 4 × D.what₂.Tau → D.host.K) →ₗ[D.host.K] (Fin 4 × D.what₂.Tau → D.host.K) :=
    ((γ₀.g.symm.trans γ.g : (Fin 4 × D.what₂.Tau → D.host.K) ≃ₗ[D.host.K] _) :
      (Fin 4 × D.what₂.Tau → D.host.K) →ₗ[D.host.K] (Fin 4 × D.what₂.Tau → D.host.K)) with hT
  let f : D.host.K →+* ℂ := D.host.φ₀.comp (algebraMap D.host.K D.host.E)
  have hform : ∀ v v' : Fin 4 × D.what₂.Tau → D.host.K,
      ∑ w, f (T v w) * conj (f (T v' w)) = ∑ w, f (v w) * conj (f (v' w)) := by
    intro v v'
    have h1 := γ.isom (γ₀.g.symm v) (γ₀.g.symm v')
    have h2 := γ₀.isom (γ₀.g.symm v) (γ₀.g.symm v')
    rw [← h2] at h1
    simp only [LinearEquiv.apply_symm_apply] at h1
    have h3 := congrArg D.host.φ₀ h1
    simp only [map_sum, map_mul, phi_conj] at h3
    exact h3
  set M : Matrix (Fin 4 × D.what₂.Tau) (Fin 4 × D.what₂.Tau) D.host.K := LinearMap.toMatrix' T with hM
  have hdet : f (γ.detRel γ₀) = (f.mapMatrix M).det := by
    rw [← RingHom.map_det, hM, LinearMap.det_toMatrix']
    rfl
  have hone : (f.mapMatrix M).transpose * ((f.mapMatrix M).map (starRingEnd ℂ)) = 1 := by
    ext i j
    rw [Matrix.mul_apply]
    have h := hform (Pi.single i 1) (Pi.single j 1)
    have e1 : ∀ w, (f.mapMatrix M).transpose i w * ((f.mapMatrix M).map (starRingEnd ℂ)) w j =
        f (T (Pi.single i 1) w) * conj (f (T (Pi.single j 1) w)) := by
      intro w
      simp only [Matrix.transpose_apply, Matrix.map_apply, RingHom.mapMatrix_apply, hM, LinearMap.toMatrix'_apply]
    rw [Finset.sum_congr rfl fun w _ => e1 w, h, Matrix.one_apply]
    rw [Finset.sum_eq_single i]
    · by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    · intro w _ hw
      simp [Pi.single_apply, hw]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have h4 := congrArg Matrix.det hone
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h4
  have h5 : ((f.mapMatrix M).map (starRingEnd ℂ)).det = conj ((f.mapMatrix M).det) := by
    rw [RingHom.map_det]; rfl
  rw [h5, ← hdet] at h4
  exact h4

theorem exists_conj (a : 𝓞 D.host.K) :
    ∃ b : 𝓞 D.host.K, ((b : D.host.K) : D.host.E) = D.host.conj ((a : D.host.K) : D.host.E) := by
  have hi : IsIntegral ℤ (D.host.conj ((a : D.host.K) : D.host.E)) := by
    have h1 : IsIntegral ℤ ((a : D.host.K) : D.host.E) :=
      map_isIntegral_int (algebraMap D.host.K D.host.E) (NumberField.RingOfIntegers.isIntegral_coe a)
    exact map_isIntegral_int D.host.conj.toRingEquiv.toRingHom h1
  have hk : IsIntegral ℤ (⟨D.host.conj ((a : D.host.K) : D.host.E), conj_mem_K D.host (a : D.host.K)⟩ : D.host.K) :=
    (isIntegral_algebraMap_iff (A := D.host.K) (B := D.host.E) (algebraMap D.host.K D.host.E).injective).1 hi
  exact ⟨⟨_, hk⟩, rfl⟩

theorem repr_K (x : D.host.K) : ∃ r s : ℚ, (x : D.host.E) =
    algebraMap ℚ D.host.E r + algebraMap ℚ D.host.E s * D.host.sqd := by
  have hsq : D.host.sqd * D.host.sqd = -(D.host.d : D.host.E) := by
    rw [← sq]; exact bE_sq D.host
  refine K_induction D.host (p := fun x => ∃ r s : ℚ, x =
    algebraMap ℚ D.host.E r + algebraMap ℚ D.host.E s * D.host.sqd) ?_ ?_ ?_ ?_ ?_ x
  · exact ⟨0, 1, by simp⟩
  · intro r; exact ⟨r, 0, by simp⟩
  · rintro _ _ ⟨r, s, rfl⟩ ⟨r', s', rfl⟩
    exact ⟨r + r', s + s', by simp only [map_add]; ring⟩
  · rintro _ ⟨r, s, rfl⟩
    by_cases h0 : r = 0 ∧ s = 0
    · exact ⟨0, 0, by rw [h0.1, h0.2]; simp⟩
    · have hd : (0 : ℚ) < D.host.d := by exact_mod_cast d_pos D.host
      have hN : r ^ 2 + (D.host.d : ℚ) * s ^ 2 ≠ 0 := by
        intro h
        apply h0
        have h3 : 0 ≤ (D.host.d : ℚ) * s ^ 2 := mul_nonneg hd.le (sq_nonneg s)
        have h1 : r ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg r)
        have h2 : (D.host.d : ℚ) * s ^ 2 = 0 := by linarith
        have h4 : s ^ 2 = 0 := (mul_eq_zero.1 h2).resolve_left hd.ne'
        exact ⟨by simpa using h1, by simpa using h4⟩
      refine ⟨r / (r ^ 2 + (D.host.d : ℚ) * s ^ 2), -s / (r ^ 2 + (D.host.d : ℚ) * s ^ 2), ?_⟩
      apply inv_eq_of_mul_eq_one_right
      have q1 : r * (r / (r ^ 2 + (D.host.d : ℚ) * s ^ 2)) +
          s * (-s / (r ^ 2 + (D.host.d : ℚ) * s ^ 2)) * (-(D.host.d : ℚ)) = 1 := by
        field_simp
      have q2 : r * (-s / (r ^ 2 + (D.host.d : ℚ) * s ^ 2)) + s * (r / (r ^ 2 + (D.host.d : ℚ) * s ^ 2)) = 0 := by
        field_simp
        ring
      have h1 := congrArg (algebraMap ℚ D.host.E) q1
      have h2 := congrArg (algebraMap ℚ D.host.E) q2
      simp only [map_add, map_mul, map_neg, map_natCast, map_one, map_zero] at h1 h2
      linear_combination (algebraMap ℚ D.host.E s * algebraMap ℚ D.host.E (-s / (r ^ 2 + (D.host.d : ℚ) * s ^ 2))) * hsq + h1 +
        D.host.sqd * h2
  · rintro _ _ ⟨r, s, rfl⟩ ⟨r', s', rfl⟩
    refine ⟨r * r' - (D.host.d : ℚ) * (s * s'), r * s' + s * r', ?_⟩
    simp only [map_add, map_sub, map_mul, map_natCast]
    linear_combination (algebraMap ℚ D.host.E s * algebraMap ℚ D.host.E s') * hsq

theorem norm_int (t t' : 𝓞 D.host.K) (h : ((t' : D.host.K) : D.host.E) = D.host.conj ((t : D.host.K) : D.host.E)) :
    ∃ n : ℤ, t * t' = (n : 𝓞 D.host.K) := by
  have hsq : D.host.sqd * D.host.sqd = -(D.host.d : D.host.E) := by
    rw [← sq]; exact bE_sq D.host
  obtain ⟨r, s, hrs⟩ := repr_K (t : D.host.K)
  have hc : ((t' : D.host.K) : D.host.E) =
      algebraMap ℚ D.host.E r - algebraMap ℚ D.host.E s * D.host.sqd := by
    rw [h, hrs, map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, conj_b]
    ring
  have hprod : (((t * t' : 𝓞 D.host.K) : D.host.K) : D.host.E) = algebraMap ℚ D.host.E (r ^ 2 + (D.host.d : ℚ) * s ^ 2) := by
    have e : (((t * t' : 𝓞 D.host.K) : D.host.K) : D.host.E) = ((t : D.host.K) : D.host.E) * ((t' : D.host.K) : D.host.E) := by
      push_cast; rfl
    rw [e, hrs, hc]
    simp only [map_add, map_mul, map_pow, map_natCast]
    linear_combination (-(algebraMap ℚ D.host.E s * algebraMap ℚ D.host.E s)) * hsq
  have hi : IsIntegral ℤ (algebraMap ℚ D.host.E (r ^ 2 + (D.host.d : ℚ) * s ^ 2)) := by
    rw [← hprod]
    exact map_isIntegral_int (algebraMap D.host.K D.host.E) (NumberField.RingOfIntegers.isIntegral_coe (t * t'))
  have hq : IsIntegral ℤ (r ^ 2 + (D.host.d : ℚ) * s ^ 2) :=
    (isIntegral_algebraMap_iff (A := ℚ) (B := D.host.E) (algebraMap ℚ D.host.E).injective).1 hi
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 hq
  refine ⟨n, ?_⟩
  apply NumberField.RingOfIntegers.coe_injective
  apply Subtype.val_injective
  show (((t * t' : 𝓞 D.host.K) : D.host.K) : D.host.E) = (((n : 𝓞 D.host.K) : D.host.K) : D.host.E)
  rw [hprod, ← hn]
  simp

theorem dvd_of_mem (Q : Ideal (𝓞 D.host.K)) (hQ : Q.IsPrime) (p : ℕ) (hp : p.Prime) (hpQ : ((p : ℕ) : 𝓞 D.host.K) ∈ Q)
    (n : ℤ) (hn : (n : 𝓞 D.host.K) ∈ Q) : (p : ℤ) ∣ n := by
  by_contra hnd
  have hc : IsCoprime (p : ℤ) n := ((Nat.prime_iff_prime_int.1 hp).coprime_iff_not_dvd).2 hnd
  obtain ⟨u, v, huv⟩ := hc
  apply hQ.ne_top
  rw [Ideal.eq_top_iff_one]
  have h1 : ((u : 𝓞 D.host.K)) * ((p : ℕ) : 𝓞 D.host.K) + (v : 𝓞 D.host.K) * (n : 𝓞 D.host.K) = 1 := by
    have := congrArg (Int.cast : ℤ → 𝓞 D.host.K) huv
    push_cast at this
    exact this
  rw [← h1]
  exact Q.add_mem (Q.mul_mem_left _ hpQ) (Q.mul_mem_left _ hn)

section Split

variable {γ₀ : IsoK D} (k : KapChoice γ₀) (p : ℕ) (hp : p.Prime) (hs : SplitK D p)

include hp hs

theorem pi_mem : k.pi p ∈ (k.pp p).asIdeal := by
  have h : k.pi p ∈ Ideal.span {k.pi p} := Ideal.mem_span_singleton_self _
  rw [← k.pi_gen p hp hs] at h
  exact Ideal.pow_le_self (classNumber_ne D) h

theorem pi_dichotomy [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) :
    ‖ι (D.host.φ₀ (((k.pi p : 𝓞 D.host.K) : D.host.K) : D.host.E))‖ < 1 ∨
      ‖ι (D.host.φ₀ (D.host.conj (((k.pi p : 𝓞 D.host.K) : D.host.K) : D.host.E)))‖ < 1 := by
  obtain ⟨b, hb⟩ := exists_conj (k.pi p)
  obtain ⟨n, hn⟩ := norm_int (k.pi p) b hb
  have hmem : (n : 𝓞 D.host.K) ∈ (k.pp p).asIdeal := by
    rw [← hn]; exact Ideal.mul_mem_right _ _ (pi_mem k p hp hs)
  have hdvd := dvd_of_mem (k.pp p).asIdeal (k.pp p).isPrime p hp (k.pp_over p hp hs) n hmem
  have hlt : ‖((n : ℤ) : ℂ_[p])‖ < 1 := by
    obtain ⟨m, hm⟩ := hdvd
    have hp1 : ‖((p : ℕ) : ℂ_[p])‖ < 1 := by
      have e : (((p : ℕ) : ℚ_[p]) : ℂ_[p]) = ((p : ℕ) : ℂ_[p]) := by simp
      rw [← e, PadicComplex.norm_extends']
      exact Padic.norm_p_lt_one
    have hm1 : ‖((m : ℤ) : ℂ_[p])‖ ≤ 1 := by
      have h := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.norm_le_one_of_int
        (map_isIntegral_int (Int.castRingHom ℂ_[p]) (isIntegral_algebraMap (R := ℤ) (A := ℤ) (x := m)))
      simpa using h
    rw [hm]
    push_cast
    rw [norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hp1 hm1
  have hprod : ι (D.host.φ₀ (((k.pi p : 𝓞 D.host.K) : D.host.K) : D.host.E)) *
      ι (D.host.φ₀ (D.host.conj (((k.pi p : 𝓞 D.host.K) : D.host.K) : D.host.E))) = ((n : ℤ) : ℂ_[p]) := by
    rw [← hb, ← map_mul, ← map_mul]
    have e : ((k.pi p : D.host.K) : D.host.E) * ((b : D.host.K) : D.host.E) = (((k.pi p * b : 𝓞 D.host.K) : D.host.K) : D.host.E) := by
      push_cast; rfl
    rw [e, hn]
    simp
  by_contra hcon
  obtain ⟨hc1, hc2⟩ := not_or.1 hcon
  have h3 := mul_le_mul (not_lt.1 hc1) (not_lt.1 hc2) zero_le_one (norm_nonneg _)
  rw [← norm_mul, hprod, one_mul] at h3
  linarith

theorem conj_pi_not_mem (b : 𝓞 D.host.K)
    (hb : ((b : D.host.K) : D.host.E) = D.host.conj (((k.pi p : 𝓞 D.host.K) : D.host.K) : D.host.E)) :
    b ∉ (k.pp p).asIdeal := by
  intro hbm
  have hinj : ∀ x y : 𝓞 D.host.K, ((x : D.host.K) : D.host.E) = ((y : D.host.K) : D.host.E) → x = y := fun x y h =>
    NumberField.RingOfIntegers.coe_injective (Subtype.val_injective h)

  have hstab : ∀ t t' : 𝓞 D.host.K, ((t' : D.host.K) : D.host.E) = D.host.conj ((t : D.host.K) : D.host.E) →
      t ∈ (k.pp p).asIdeal → t' ∈ (k.pp p).asIdeal := by
    intro t t' ht htm
    have h1 : t ^ classNumber D.host.K ∈ Ideal.span {k.pi p} := by
      rw [← k.pi_gen p hp hs]; exact Ideal.pow_mem_pow htm _
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 h1
    obtain ⟨r', hr'⟩ := exists_conj r
    have h2 : t' ^ classNumber D.host.K = r' * b := by
      apply hinj
      have e1 : (((t' ^ classNumber D.host.K : 𝓞 D.host.K) : D.host.K) : D.host.E) = ((t' : D.host.K) : D.host.E) ^ classNumber D.host.K := by
        push_cast; rfl
      have e2 : (((r' * b : 𝓞 D.host.K) : D.host.K) : D.host.E) = ((r' : D.host.K) : D.host.E) * ((b : D.host.K) : D.host.E) := by
        push_cast; rfl
      have e3 : (((r * k.pi p : 𝓞 D.host.K) : D.host.K) : D.host.E) = ((r : D.host.K) : D.host.E) * ((k.pi p : D.host.K) : D.host.E) := by
        push_cast; rfl
      have e4 : (((t ^ classNumber D.host.K : 𝓞 D.host.K) : D.host.K) : D.host.E) = ((t : D.host.K) : D.host.E) ^ classNumber D.host.K := by
        push_cast; rfl
      rw [e1, e2, ht, hr', hb, ← map_pow, ← map_mul, ← e3, ← e4, hr]
    have h3 : t' ^ classNumber D.host.K ∈ (k.pp p).asIdeal := by
      rw [h2]; exact Ideal.mul_mem_left _ _ hbm
    exact (k.pp p).isPrime.mem_of_pow_mem _ h3
  obtain ⟨P, hP, hpP, a₁, b₁, hab, ha₁, hb₁⟩ := splitKSplits D p hp hs
  have hle : P ≤ (k.pp p).asIdeal := by
    intro t ht
    obtain ⟨t', ht'⟩ := exists_conj t
    obtain ⟨n, hn⟩ := norm_int t t' ht'
    have hnP : (n : 𝓞 D.host.K) ∈ P := by rw [← hn]; exact Ideal.mul_mem_right _ _ ht
    obtain ⟨m, hm⟩ := dvd_of_mem P hP p hp hpP n hnP
    have hnp : t * t' ∈ (k.pp p).asIdeal := by
      rw [hn, hm]
      push_cast
      exact Ideal.mul_mem_right _ _ (k.pp_over p hp hs)
    rcases (k.pp p).isPrime.mem_or_mem hnp with h | h
    · exact h
    · refine hstab t' t ?_ h
      rw [ht', conj_conj]
  have hPne : P ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.mem_bot] at hpP
    exact hp.ne_zero (by exact_mod_cast hpP)
  have hmax : P.IsMaximal := hP.isMaximal hPne
  have hPeq : P = (k.pp p).asIdeal := hmax.eq_of_le (k.pp p).isPrime.ne_top hle
  apply hb₁
  rw [hPeq]
  exact hstab a₁ b₁ hab.symm (hPeq ▸ ha₁)

end Split

end Formalism.L2.Ker.KS
