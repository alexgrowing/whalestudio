import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfEqOnCoprime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannZetaNeZeroOfMemIoo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DirichletLZeroSymmetry
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.HostZeroFree

theorem exists_sq_two_pow (a : ℤ) (ha : a % 8 = 1) (k : ℕ) :
    ∃ b : ℤ, Odd b ∧ (2 : ℤ) ^ (k + 3) ∣ b ^ 2 - a := by
  induction k with
  | zero => exact ⟨1, odd_one, by norm_num; omega⟩
  | succ k ih =>
    obtain ⟨b, hb, t, ht⟩ := ih
    rcases Int.even_or_odd t with ⟨s, hs⟩ | hodd
    · exact ⟨b, hb, s, by rw [ht, hs]; ring⟩
    · obtain ⟨u, hu⟩ := hodd.add_odd hb
      refine ⟨b + 2 ^ (k + 2), hb.add_even ⟨2 ^ (k + 1), by ring⟩, u + 2 ^ k, ?_⟩
      linear_combination ht + 2 ^ (k + 3) * hu

theorem even_quadratic_two_pow (e : ℕ) (ξ : DirichletCharacter ℂ (4 * 2 ^ e)) (hev : ξ.Even)
    (h2 : ξ ^ 2 = 1) :
    (∀ a : ℕ, Odd a → ξ (a : ZMod (4 * 2 ^ e)) = 1) ∨
    (∀ a : ℕ, Odd a → ξ (a : ZMod (4 * 2 ^ e)) = ((ZMod.χ₈ (a : ZMod 8) : ℤ) : ℂ)) := by
  have hsq : ∀ b : ℤ, Odd b → ξ (b : ZMod (4 * 2 ^ e)) ^ 2 = 1 := by
    intro b hb
    have hu : IsUnit (b : ZMod (4 * 2 ^ e)) := by
      rw [ZMod.coe_int_isUnit_iff_isCoprime]
      have : IsCoprime (2 : ℤ) b := by
        obtain ⟨c, rfl⟩ := hb
        exact ⟨-c, 1, by ring⟩
      have h := this.pow_left (m := e + 2)
      convert h using 1
      push_cast; ring
    rw [← MulChar.pow_apply' _ (by norm_num), h2, MulChar.one_apply hu]
  have h1 : ∀ a : ℤ, a % 8 = 1 → ξ (a : ZMod (4 * 2 ^ e)) = 1 := by
    intro a ha
    obtain ⟨b, hb, hd⟩ := exists_sq_two_pow a ha e
    have : (a : ZMod (4 * 2 ^ e)) = (b : ZMod (4 * 2 ^ e)) ^ 2 := by
      rw [← Int.cast_pow, ZMod.intCast_eq_intCast_iff_dvd_sub]
      refine Dvd.dvd.trans ⟨2, ?_⟩ hd
      push_cast; ring
    rw [this, map_pow, hsq b hb]
  have hneg : ∀ a : ℤ, ξ ((-a : ℤ) : ZMod (4 * 2 ^ e)) = ξ (a : ZMod (4 * 2 ^ e)) := by
    intro a
    rw [Int.cast_neg, hev.eval_neg]
  have h7 : ∀ a : ℤ, a % 8 = 7 → ξ (a : ZMod (4 * 2 ^ e)) = 1 := by
    intro a ha
    rw [← hneg]; exact h1 _ (by omega)
  have s5 := hsq 5 (by decide)
  have h5 : ∀ a : ℤ, a % 8 = 5 → ξ (a : ZMod (4 * 2 ^ e)) = ξ ((5 : ℤ) : ZMod (4 * 2 ^ e)) := by
    intro a ha
    have := h1 (a * 5) (by omega)
    rw [Int.cast_mul, map_mul] at this
    linear_combination (-ξ (a : ZMod (4 * 2 ^ e))) * s5 + ξ ((5 : ℤ) : ZMod (4 * 2 ^ e)) * this
  have h3 : ∀ a : ℤ, a % 8 = 3 → ξ (a : ZMod (4 * 2 ^ e)) = ξ ((5 : ℤ) : ZMod (4 * 2 ^ e)) := by
    intro a ha
    rw [← hneg]; exact h5 _ (by omega)
  rcases mul_self_eq_one_iff.mp ((sq _).symm.trans s5) with h | h
  · left
    intro a ha
    obtain ⟨c, hc⟩ := ha
    rw [← Int.cast_natCast]
    have : (a : ℤ) % 8 = 1 ∨ (a : ℤ) % 8 = 3 ∨ (a : ℤ) % 8 = 5 ∨ (a : ℤ) % 8 = 7 := by omega
    rcases this with h' | h' | h' | h'
    · exact h1 _ h'
    · rw [h3 _ h', h]
    · rw [h5 _ h', h]
    · exact h7 _ h'
  · right
    intro a ha
    obtain ⟨c, hc⟩ := ha
    rw [← Int.cast_natCast, ZMod.χ₈_nat_eq_if_mod_eight, if_neg (by omega)]
    have : (a : ℤ) % 8 = 1 ∨ (a : ℤ) % 8 = 3 ∨ (a : ℤ) % 8 = 5 ∨ (a : ℤ) % 8 = 7 := by omega
    rcases this with h' | h' | h' | h'
    · rw [h1 _ h', if_pos (by omega)]; simp
    · rw [h3 _ h', h, if_neg (by omega)]; simp
    · rw [h5 _ h', h, if_neg (by omega)]; simp
    · rw [h7 _ h', if_pos (by omega)]; simp

theorem level_dvd {N M : ℕ} [NeZero N] [NeZero M] (χ : DirichletCharacter ℂ N)
    (ψ : DirichletCharacter ℂ M) (hχ : χ.IsPrimitive)
    (h : ∀ a : ℕ, a.Coprime M → χ (a : ZMod N) = ψ (a : ZMod M)) : N ∣ M := by
  have : NeZero (N * M) := ⟨mul_ne_zero (NeZero.ne N) (NeZero.ne M)⟩
  have key : DirichletCharacter.changeLevel (dvd_mul_right N M) χ =
      DirichletCharacter.changeLevel (dvd_mul_left M N) ψ := by
    apply MulChar.ext
    intro u
    have hu := ZMod.val_coe_unit_coprime u
    rw [← ZMod.natCast_zmod_val (u : ZMod (N * M)), QuadPrim.changeLevel_nat χ _ hu,
      QuadPrim.changeLevel_nat ψ _ hu]
    exact h _ (hu.coprime_dvd_right (dvd_mul_left M _))
  have := congrArg DirichletCharacter.conductor key
  rw [DirichletCharacter.conductor_changeLevel, DirichletCharacter.conductor_changeLevel] at this
  rw [← (hχ : χ.conductor = N), this]
  exact ψ.conductor_dvd_level

theorem kron_inv (D : ℤ) (a : ℕ) : (GlobalTheoryTheory.kron D a)⁻¹ = GlobalTheoryTheory.kron D a := by
  unfold GlobalTheoryTheory.kron GlobalTheoryTheory.kronSym
  push_cast
  rw [mul_inv, ← inv_pow]
  congr 1
  · rcases jacobiSym.trichotomy D (a / 2 ^ a.factorization 2) with h | h | h <;> simp [h]
  · congr 1
    unfold GlobalTheoryTheory.kron2
    split_ifs <;> simp

theorem chi0_inv (q d : ℕ) (i : Fin 4) (a : ℕ) :
    (GlobalTheoryTheory.chi0 q d i a)⁻¹ = GlobalTheoryTheory.chi0 q d i a := by
  fin_cases i <;> simp [GlobalTheoryTheory.chi0, GlobalTheoryTheory.chDir, GlobalTheoryTheory.psDir, kron_inv, mul_comm]

theorem isCharE_inv {n q d N : ℕ} {χ : DirichletCharacter ℂ N} (h : GlobalTheoryTheory.IsCharE n q d χ) :
    GlobalTheoryTheory.IsCharE n q d χ⁻¹ := by
  obtain ⟨hp, i, ξ, hξ, hv⟩ := h
  refine ⟨?_, i, ξ⁻¹, ?_, fun a ha => ?_⟩
  · rw [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_inv]; exact hp
  · rw [DirichletCharacter.Even, MulChar.inv_apply_eq_inv', (hξ : ξ (-1) = 1), inv_one]
  · rw [MulChar.inv_apply_eq_inv', MulChar.inv_apply_eq_inv', hv a ha, mul_inv, chi0_inv]

theorem level_dvd_of_isCharE {n q d N : ℕ} [NeZero N] (hn : n ≠ 0) (hq : q.Prime) (hd : d.Prime)
    (hq4 : q % 4 = 3) (hd4 : d % 4 = 3) {χ : DirichletCharacter ℂ N}
    (h : GlobalTheoryTheory.IsCharE n q d χ) : N ∣ 4 * n * q * d := by
  obtain ⟨hp, i, ξ, hξ, hv⟩ := h
  obtain ⟨hK, -⟩ := GlobalTheory.kronSym_neg_eq_jacobiSym_and_two
  have hM : 4 * n * q * d ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hn) hq.ne_zero) hd.ne_zero
  have : NeZero (4 * n * q * d) := ⟨hM⟩
  obtain ⟨⟨α, -, hα⟩, -⟩ := QuadPrim.isPrimQuad_jacobi hd (by omega)
  obtain ⟨⟨β, -, hβ⟩, -⟩ := QuadPrim.isPrimQuad_jacobi hq (by omega)
  have d1 : d ∣ 4 * n * q * d := dvd_mul_left _ _
  have d2 : q ∣ 4 * n * q * d := (dvd_mul_left _ _).mul_right _
  have d3 : 4 * n ∣ 4 * n * q * d := (dvd_mul_right _ _).mul_right _
  have hpos : ∀ a : ℕ, a.Coprime (4 * n * q * d) → 0 < a := by
    intro a ha
    rcases Nat.eq_zero_or_pos a with rfl | h
    · have := Nat.eq_one_of_dvd_one ((Nat.coprime_zero_left _).mp ha ▸ d1)
      omega
    · exact h
  have hch : ∀ a : ℕ, a.Coprime (4 * n * q * d) →
      GlobalTheoryTheory.chDir d a = DirichletCharacter.changeLevel d1 α (a : ZMod (4 * n * q * d)) := by
    intro a ha
    rw [GlobalTheoryTheory.chDir, GlobalTheoryTheory.kron, hK d a hd4 (hpos a ha), QuadPrim.changeLevel_nat _ _ ha, hα]
  have hps : ∀ a : ℕ, a.Coprime (4 * n * q * d) →
      GlobalTheoryTheory.psDir q a = DirichletCharacter.changeLevel d2 β (a : ZMod (4 * n * q * d)) := by
    intro a ha
    rw [GlobalTheoryTheory.psDir, GlobalTheoryTheory.kron, hK q a hq4 (hpos a ha), QuadPrim.changeLevel_nat _ _ ha, hβ]
  have hex : ∃ ψ : DirichletCharacter ℂ (4 * n * q * d), ∀ a : ℕ, a.Coprime (4 * n * q * d) →
      GlobalTheoryTheory.chi0 q d i a = ψ (a : ZMod (4 * n * q * d)) := by
    fin_cases i
    · exact ⟨1, fun a ha => by
        rw [MulChar.one_apply ((ZMod.isUnit_iff_coprime _ _).mpr ha)]; rfl⟩
    · exact ⟨_, hch⟩
    · exact ⟨_, hps⟩
    · exact ⟨DirichletCharacter.changeLevel d1 α * DirichletCharacter.changeLevel d2 β,
        fun a ha => by rw [MulChar.mul_apply, ← hch a ha, ← hps a ha]; rfl⟩
  obtain ⟨ψ, hψ⟩ := hex
  refine level_dvd χ (ψ * DirichletCharacter.changeLevel d3 ξ) hp fun a ha => ?_
  rw [hv a ha, MulChar.mul_apply, QuadPrim.changeLevel_nat _ _ ha, hψ a ha]

theorem coprime_four_mul_two_pow {e q d a : ℕ} (ha : a.Coprime (8 * q * d)) :
    Odd a ∧ a.Coprime (4 * 2 ^ e * q * d) := by
  rw [Nat.coprime_mul_iff_right, Nat.coprime_mul_iff_right] at ha
  obtain ⟨⟨h8, hq⟩, hd⟩ := ha
  have h2 : a.Coprime 2 := h8.coprime_dvd_right (by norm_num)
  refine ⟨Nat.coprime_two_right.mp h2, Nat.Coprime.mul_right (Nat.Coprime.mul_right
    (Nat.Coprime.mul_right (h8.coprime_dvd_right (by norm_num)) (h2.pow_right e)) hq) hd⟩

theorem real_zero_le {x eps : ℝ} {e q d N : ℕ} [NeZero N] (hq : q ≠ 0) (hd : d ≠ 0)
    (hbox : Boxq x eps q d) {χ : DirichletCharacter ℂ N} (h : GlobalTheoryTheory.IsCharE (2 ^ e) q d χ)
    (hN : N ∣ 4 * 2 ^ e * q * d) (h2 : χ ^ 2 = 1) (h1 : χ ≠ 1) {ρ : ℂ} (h0 : 0 < ρ.re)
    (him : ρ.im = 0) (hz : DirichletCharacter.LFunction χ ρ = 0) : ρ.re ≤ 1 - 1 / 400 := by
  obtain ⟨hp, i, ξ, hξ, hv⟩ := h
  obtain ⟨-, hK2⟩ := GlobalTheory.kronSym_neg_eq_jacobiSym_and_two
  have hM : 4 * 2 ^ e * q * d ≠ 0 := by positivity
  have hM8 : 8 * q * d ≠ 0 := by positivity
  have : NeZero (4 * 2 ^ e * q * d) := ⟨hM⟩
  have d3 : 4 * 2 ^ e ∣ 4 * 2 ^ e * q * d := (dvd_mul_right _ _).mul_right _
  have hξ2 : ξ ^ 2 = 1 := by
    apply DirichletCharacter.changeLevel_injective d3
    rw [map_one, map_pow]
    apply MulChar.ext
    intro u
    have hu := ZMod.val_coe_unit_coprime u
    rw [MulChar.one_apply u.isUnit, MulChar.pow_apply' _ (by norm_num),
      ← ZMod.natCast_zmod_val (u : ZMod (4 * 2 ^ e * q * d)), QuadPrim.changeLevel_nat _ _ hu]
    set a := (u : ZMod (4 * 2 ^ e * q * d)).val
    have e1 : χ (a : ZMod N) ^ 2 = 1 := by
      rw [← MulChar.pow_apply' _ (by norm_num), h2,
        MulChar.one_apply ((ZMod.isUnit_iff_coprime _ _).mpr (hu.coprime_dvd_right hN))]
    rw [hv a hu] at e1
    have hne : GlobalTheoryTheory.chi0 q d i a ≠ 0 := by
      intro h0; rw [h0] at e1; simp at e1
    have e2 : GlobalTheoryTheory.chi0 q d i a * GlobalTheoryTheory.chi0 q d i a = 1 := by
      nth_rewrite 1 [← chi0_inv]
      exact inv_mul_cancel₀ hne
    linear_combination e1 - ξ (a : ZMod (4 * 2 ^ e)) ^ 2 * e2
  have good : ∀ (Q : ℝ) (f : ℕ → ℂ), GoodAllFor Q f (8 * q * d) →
      (∀ a : ℕ, a.Coprime (8 * q * d) → χ (a : ZMod N) = f a) → ρ.re ≤ 1 - 1 / 400 := by
    intro Q f hg hf
    obtain ⟨-, -, hQ, hnz⟩ := hg N χ ⟨hp, hf⟩
    by_contra hlt
    refine hnz ρ (not_le.mp hlt) ?_ hz
    rw [him, abs_zero]
    exact (Nat.cast_nonneg N).trans hQ
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hbox
  rcases even_quadratic_two_pow e ξ hξ hξ2 with hx | hx
  · have hv' : ∀ a : ℕ, a.Coprime (8 * q * d) → χ (a : ZMod N) = GlobalTheoryTheory.chi0 q d i a := by
      intro a ha
      obtain ⟨ho, hc⟩ := coprime_four_mul_two_pow (e := e) ha
      rw [hv a hc, hx a ho, mul_one]
    fin_cases i
    · exfalso
      apply h1
      obtain ⟨hN1, -⟩ := QuadPrim.eq_of_eqOn_coprime hM8 χ (1 : DirichletCharacter ℂ 1) hp
        DirichletCharacter.isPrimitive_one_level_one (fun a ha => by
          rw [hv' a ha, MulChar.one_apply (isUnit_of_subsingleton _)]; rfl)
      rw [DirichletCharacter.eq_one_iff_conductor_eq_one]
      exact (hp : χ.conductor = N).trans hN1
    · exact good _ _ b3 hv'
    · exact good _ _ b1 hv'
    · exact good _ _ b5 hv'
  · have hv' : ∀ a : ℕ, a.Coprime (8 * q * d) →
        χ (a : ZMod N) = GlobalTheoryTheory.chi8 a * GlobalTheoryTheory.chi0 q d i a := by
      intro a ha
      obtain ⟨ho, hc⟩ := coprime_four_mul_two_pow (e := e) ha
      rw [hv a hc, hx a ho, mul_comm, GlobalTheoryTheory.chi8, GlobalTheoryTheory.kron, hK2 a ho]
    fin_cases i
    · exfalso
      obtain ⟨⟨ψ, hψ, hψv⟩, -⟩ := QuadPrim.isPrimQuad_chi8
      obtain ⟨hN8, hval⟩ := QuadPrim.eq_of_eqOn_coprime hM8 χ ψ hp hψ (fun a ha => by
          obtain ⟨ho, -⟩ := coprime_four_mul_two_pow (e := e) ha
          rw [hv' a ha, hψv, GlobalTheoryTheory.chi8, GlobalTheoryTheory.kron, hK2 a ho]
          simp [GlobalTheoryTheory.chi0])
      subst hN8
      refine GlobalTheory.RealZeros.no_real_zero.2 χ (fun a => ?_) ρ.re h0 ?_
      · rw [← ZMod.natCast_zmod_val a, hval, hψv]
      · have : (ρ.re : ℂ) = ρ := Complex.ext (by simp) (by simp [him])
        rw [this]; exact hz
    · exact good _ _ b4 hv'
    · exact good _ _ b2 hv'
    · exact good _ _ b6 (fun a ha => by rw [hv' a ha, mul_assoc]; rfl)

theorem main : Formalism.ZeroFreeDirichlet.ZFRDirichlet → ∃ c : ℝ, 0 < c ∧ ∀ (x eps : ℝ) (e q d : ℕ), Rowq x eps (2 ^ e) q d → Boxq x eps q d → ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), GlobalTheoryTheory.IsCharE (2 ^ e) q d χ → N ∣ 4 * 2 ^ e * q * d ∧ ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → DirichletCharacter.LFunction χ ρ = 0 → c / Real.log (4 * 2 ^ e * q * d * (|ρ.im| + 3)) ≤ ρ.re ∧ ρ.re ≤ 1 - c / Real.log (4 * 2 ^ e * q * d * (|ρ.im| + 3)) := by
  rintro ⟨c₀, hc₀, hZ⟩
  refine ⟨min c₀ (1 / 400), lt_min hc₀ (by norm_num), ?_⟩
  intro x eps e q d hrow hbox N _ χ hχ
  obtain ⟨hq, hq8, -, -, hd, hd16, -⟩ := hrow
  have hdvd : ∀ χ : DirichletCharacter ℂ N, GlobalTheoryTheory.IsCharE (2 ^ e) q d χ →
      N ∣ 4 * 2 ^ e * q * d := fun χ hχ =>
    level_dvd_of_isCharE (by positivity) hq hd (by omega) (by omega) hχ
  have hMpos : 0 < 4 * 2 ^ e * q * d := by
    have := hq.pos; have := hd.pos; positivity
  have hNM : (N : ℝ) ≤ 4 * 2 ^ e * q * d := by
    exact_mod_cast Nat.le_of_dvd hMpos (hdvd χ hχ)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have upper : ∀ χ : DirichletCharacter ℂ N, GlobalTheoryTheory.IsCharE (2 ^ e) q d χ → ∀ ρ : ℂ,
      0 < ρ.re → ρ.re < 1 → DirichletCharacter.LFunction χ ρ = 0 →
      ρ.re ≤ 1 - min c₀ (1 / 400) / Real.log (4 * 2 ^ e * q * d * (|ρ.im| + 3)) := by
    intro χ hχ ρ h0 h1 hz
    set M : ℝ := 4 * 2 ^ e * q * d with hM
    have ht := abs_nonneg ρ.im
    have hmin : 0 < min c₀ (1 / 400 : ℝ) := lt_min hc₀ (by norm_num)
    have hlog1 : 1 ≤ Real.log (M * (|ρ.im| + 3)) := by
      rw [Real.le_log_iff_exp_le (by nlinarith)]
      have := Real.exp_one_lt_d9
      nlinarith
    by_cases hreg : Formalism.ZeroFreeDirichlet.InRegion c₀ N ρ
    · obtain ⟨h2, hne, him, -⟩ := hZ N χ ρ hreg
        ⟨Or.inr (fun h => by rw [h] at h1; simp at h1), hz⟩
      have := real_zero_le hq.ne_zero hd.ne_zero hbox hχ (hdvd χ hχ) h2 hne h0 him hz
      have h3 : min c₀ (1 / 400) / Real.log (M * (|ρ.im| + 3)) ≤ 1 / 400 :=
        (div_le_self hmin.le hlog1).trans (min_le_right _ _)
      linarith
    · unfold Formalism.ZeroFreeDirichlet.InRegion at hreg
      have hpos : 0 < Real.log ((N : ℝ) * (|ρ.im| + 2)) := Real.log_pos (by nlinarith)
      have hle : Real.log ((N : ℝ) * (|ρ.im| + 2)) ≤ Real.log (M * (|ρ.im| + 3)) :=
        Real.log_le_log (by positivity) (by nlinarith)
      have h3 : min c₀ (1 / 400) / Real.log (M * (|ρ.im| + 3)) ≤
          c₀ / Real.log ((N : ℝ) * (|ρ.im| + 2)) :=
        div_le_div₀ hc₀.le (min_le_left _ _) hpos hle
      linarith [not_le.mp hreg]
  refine ⟨hdvd χ hχ, fun ρ h0 h1 hz => ⟨?_, upper χ hχ ρ h0 h1 hz⟩⟩
  have hz' := ((GlobalTheory.Mem.An.zeros_symm_one_sub N χ hχ.1 ρ h0 h1).1).mp hz
  have := upper χ⁻¹ (isCharE_inv hχ) (1 - ρ) (by simp [h1]) (by simp [h0]) hz'
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, zero_sub,
    abs_neg] at this
  linarith

end GlobalTheory.HostZeroFree
