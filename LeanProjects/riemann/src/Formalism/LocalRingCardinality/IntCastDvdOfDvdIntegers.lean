import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

noncomputable section

namespace Formalism.BasicNotions

open NumberField

theorem intCast_dvd_of_dvd_integers (E : Type) [Field E] [NumberField E] (a b : ℤ)
    (h : (b : 𝓞 E) ∣ (a : 𝓞 E)) : b ∣ a := by
  have h1 := map_dvd (Algebra.norm ℤ) h
  have ea : (a : 𝓞 E) = algebraMap ℤ (𝓞 E) a := by simp
  have eb : (b : 𝓞 E) = algebraMap ℤ (𝓞 E) b := by simp
  rw [ea, eb, Algebra.norm_algebraMap, Algebra.norm_algebraMap] at h1
  have hn : Module.finrank ℤ (𝓞 E) ≠ 0 := by
    rw [RingOfIntegers.rank]; exact (Module.finrank_pos).ne'
  exact (Int.pow_dvd_pow_iff hn).1 h1

theorem dvd_norm_sub_one (E : Type) [Field E] [NumberField E] (σ : E ≃ₐ[ℚ] E) (π : 𝓞 E) (T M : ℕ)
    (hT : (π : E) * σ (π : E) = (T : E)) (hπ : (π - 1) ∈ Ideal.span {((M : ℕ) : 𝓞 E)}) :
    (M : ℤ) ∣ (T : ℤ) - 1 := by
  rw [Ideal.mem_span_singleton] at hπ
  obtain ⟨α, hα⟩ := hπ
  have hint : IsIntegral ℤ (σ (α : E)) := map_isIntegral_int σ (RingOfIntegers.isIntegral_coe α)
  set α' : 𝓞 E := ⟨σ (α : E), hint⟩ with hα'
  have e1 : (π : E) = 1 + (M : E) * (α : E) := by
    have := congrArg (fun z : 𝓞 E => (z : E)) hα
    simp only [map_sub, map_one, map_mul, map_natCast] at this
    linear_combination this
  have e2 : σ (π : E) = 1 + (M : E) * (α' : E) := by
    have hc : (α' : E) = σ (α : E) := rfl
    rw [e1, hc]; simp
  have e3 : (T : E) - 1 = (M : E) * ((α : E) + (α' : E) + (M : E) * (α : E) * (α' : E)) := by
    rw [← hT, e2, e1]; ring
  have h5 : ((M : ℤ) : 𝓞 E) ∣ (((T : ℤ) - 1 : ℤ) : 𝓞 E) := by
    refine ⟨α + α' + (M : 𝓞 E) * α * α', ?_⟩
    apply RingOfIntegers.ext
    simp only [map_mul, map_add, map_natCast, map_intCast]
    push_cast
    exact e3
  exact intCast_dvd_of_dvd_integers E _ _ h5

namespace D7

variable (D : D7)

def modT : ℕ := D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2

theorem modT_dvd (u : D.what₂.Word) : (D.modT : ℤ) ∣ ((D.mem u).A.T : ℤ) - 1 := by
  obtain ⟨π, -, hT, hπ⟩ := D.T_norm u
  exact dvd_norm_sub_one D.host.E D.host.conj π _ _ hT hπ

theorem T_modEq (u : D.what₂.Word) : (D.mem u).A.T ≡ 1 [MOD D.modT] :=
  ((Nat.modEq_iff_dvd).2 (by exact_mod_cast D.modT_dvd u)).symm

theorem T_modEq_of_dvd (u : D.what₂.Word) {a : ℕ} (ha : a ∣ D.modT) : (D.mem u).A.T ≡ 1 [MOD a] :=
  (D.T_modEq u).of_dvd ha

theorem T_mod_of_dvd (u : D.what₂.Word) {a : ℕ} (ha : a ∣ D.modT) (h1 : 1 < a) : (D.mem u).A.T % a = 1 := by
  have h := D.T_modEq_of_dvd u ha
  rwa [Nat.ModEq, Nat.mod_eq_of_lt h1] at h

theorem g_dvd_modT (i : Fin 2) : D.host.g i ∣ D.modT := by
  have h : D.host.g i ∣ D.host.g 0 * D.host.g 1 := by
    fin_cases i
    · exact Dvd.intro _ rfl
    · exact Dvd.intro_left _ rfl
  exact Dvd.dvd.mul_left (dvd_pow h two_ne_zero) _

theorem gg_dvd_modT : (D.host.g 0 * D.host.g 1) ^ 2 ∣ D.modT := Dvd.intro_left _ rfl

theorem cond_dvd_modT : D.host.QS * D.host.q * D.host.d ∣ D.modT := Dvd.intro _ rfl

theorem q_prime : D.host.q.Prime := D.host.hyp.1

theorem d_prime : D.host.d.Prime := D.host.hyp.2.1

theorem n_pos : 0 < D.R.n := by unfold Ranks.n; positivity

theorem one_lt_cond : 1 < D.host.QS * D.host.q * D.host.d := by
  have h1 := D.host.QS_pos
  have h2 := D.q_prime.pos
  have h3 := D.d_prime.two_le
  have : 1 * 1 * 2 ≤ D.host.QS * D.host.q * D.host.d := by gcongr <;> omega
  omega

theorem T_mod_g (u : D.what₂.Word) (i : Fin 2) : (D.mem u).A.T % D.host.g i = 1 :=
  D.T_mod_of_dvd u (D.g_dvd_modT i) (D.host.g_prime i).one_lt

theorem T_mod_gg (u : D.what₂.Word) : (D.mem u).A.T % (D.host.g 0 * D.host.g 1) ^ 2 = 1 := by
  refine D.T_mod_of_dvd u D.gg_dvd_modT ?_
  have h0 := (D.host.g_prime 0).two_le
  have h1 := (D.host.g_prime 1).two_le
  have : 2 * 2 ≤ D.host.g 0 * D.host.g 1 := Nat.mul_le_mul h0 h1
  nlinarith

theorem T_mod_cond (u : D.what₂.Word) : (D.mem u).A.T % (D.host.QS * D.host.q * D.host.d) = 1 :=
  D.T_mod_of_dvd u D.cond_dvd_modT D.one_lt_cond

private theorem tower_dvd_modT : 2 ^ (D.R.e + 2) ∣ D.modT :=
  D.host.tower_dvd.trans (dvd_trans ⟨D.host.q * D.host.d, by ring⟩ D.cond_dvd_modT)

theorem T_mod_four (u : D.what₂.Word) : (D.mem u).A.T % 4 = 1 :=
  D.T_mod_of_dvd u (dvd_trans ⟨2 ^ D.R.e, by ring⟩ (tower_dvd_modT D)) (by norm_num)

theorem T_mod_q (u : D.what₂.Word) : (D.mem u).A.T % D.host.q = 1 :=
  D.T_mod_of_dvd u (dvd_trans ⟨D.host.QS * D.host.d, by ring⟩ D.cond_dvd_modT) D.q_prime.one_lt

theorem T_mod_d (u : D.what₂.Word) : (D.mem u).A.T % D.host.d = 1 :=
  D.T_mod_of_dvd u (dvd_trans ⟨D.host.QS * D.host.q, by ring⟩ D.cond_dvd_modT) D.d_prime.one_lt

theorem T_ne_g (u : D.what₂.Word) (i : Fin 2) : (D.mem u).A.T ≠ D.host.g i := by
  intro h
  have h1 := D.T_mod_g u i
  rw [h, Nat.mod_self] at h1
  exact zero_ne_one h1

theorem T_ne_two (u : D.what₂.Word) : (D.mem u).A.T ≠ 2 := by
  have h1 := D.T_mod_four u
  omega

theorem T_ne_q (u : D.what₂.Word) : (D.mem u).A.T ≠ D.host.q := by
  intro h
  have h1 := D.T_mod_q u
  rw [h, Nat.mod_self] at h1
  exact zero_ne_one h1

theorem T_ne_d (u : D.what₂.Word) : (D.mem u).A.T ≠ D.host.d := by
  intro h
  have h1 := D.T_mod_d u
  rw [h, Nat.mod_self] at h1
  exact zero_ne_one h1

end D7

end Formalism.BasicNotions

end
