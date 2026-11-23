import Formalism.LocalRingCardinality.DataHost
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.TameInertiaTowers.TowerFieldFoundations
import Formalism.CyclotomicNorms.StatementI
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.NonemptyFieldAxiomsCyclicPow

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition NumberField
open scoped Pointwise

def Rt (s : ℕ) : Ranks where
  toFrame := Formalism.HC.cyclicFrame 2
  k := 8
  m := 2
  t := 2 * s + 15
  k_even := ⟨4, rfl⟩
  m_even := ⟨1, rfl⟩
  t_odd := ⟨s + 7, by ring⟩
  two_le_m := le_refl _
  m_add_three_le_k := by norm_num
  rank_add_five_le := by omega
  three_m_lt_t := by omega
  m_le_f := show 2 ≤ 2 * 2 ^ 2 by norm_num
  f_le_k := show 2 * 2 ^ 2 ≤ 8 by norm_num
  m_sq_le_N := by omega

theorem top_primitive {K : Type} [Field K] [NumberField K] (m : ℕ) (hm : 1 < m) :
    ¬ (⊤ : Ideal (𝓞 K)) ≤ Ideal.span {(m : 𝓞 K)} := by
  intro h
  have hu : IsUnit (m : 𝓞 K) := by
    rw [← Ideal.span_singleton_eq_top]; exact top_le_iff.1 h
  have hn : IsUnit (Algebra.norm ℤ (m : 𝓞 K)) := hu.map _
  rw [show (m : 𝓞 K) = algebraMap ℤ (𝓞 K) (m : ℤ) by simp, Algebra.norm_algebraMap,
    Int.isUnit_iff] at hn
  have hr : 0 < Module.finrank ℤ (𝓞 K) := Module.finrank_pos
  have h2 : (2 : ℤ) ^ Module.finrank ℤ (𝓞 K) ≤ (m : ℤ) ^ Module.finrank ℤ (𝓞 K) :=
    pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hm) _
  have h3 : (2 : ℤ) ≤ 2 ^ Module.finrank ℤ (𝓞 K) := by
    calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ Module.finrank ℤ (𝓞 K) := pow_le_pow_right₀ (by norm_num) hr
  rcases hn with h | h <;> omega

theorem oddProd_odd (B : ℕ) : Odd (∏ i ∈ Finset.range B, (2 * i + 1)) := by
  induction B with
  | zero => simp
  | succ n ih => rw [Finset.prod_range_succ]; exact ih.mul ⟨n, rfl⟩

theorem exists_d (B N : ℕ) : ∃ d : ℕ, N < d ∧ d.Prime ∧ d % 16 = 7 ∧
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ≤ B → jacobiSym (-(d : ℤ)) p = 1 := by
  set P : ℕ := ∏ i ∈ Finset.range B, (2 * i + 1) with hP
  have hodd : Odd P := oddProd_odd B
  have hP0 : P ≠ 0 := by rintro h; rw [h] at hodd; exact absurd hodd (by decide)
  have hco : IsCoprime (8 * (P : ℤ) - 1) ((16 * P : ℕ) : ℤ) :=
    ⟨-(8 * (P : ℤ) + 1), 4 * P, by push_cast; ring⟩
  obtain ⟨d, hdN, hdp, hd⟩ := Nat.forall_exists_prime_gt_and_zmodEq N (q := 16 * P)
    (a := 8 * (P : ℤ) - 1) (by omega) hco
  obtain ⟨c, hc⟩ := hd.symm.dvd
  push_cast at hc
  obtain ⟨s, hs⟩ := hodd
  refine ⟨d, hdN, hdp, ?_, fun p hp h2 hB => ?_⟩
  · have h1 : (d : ℤ) = 16 * (s + P * c) + 7 := by
      have : (P : ℤ) = 2 * s + 1 := by exact_mod_cast hs
      linear_combination hc + 8 * this
    omega
  · obtain ⟨i, hi⟩ := hp.odd_of_ne_two h2
    have hdv : p ∣ P := by
      rw [hi]; exact Finset.dvd_prod_of_mem _ (Finset.mem_range.2 (by omega))
    obtain ⟨e, he⟩ := hdv
    have he' : (P : ℤ) = p * e := by exact_mod_cast he
    have : (-(d : ℤ)) % p = 1 % p := by
      have h3 : (-(d : ℤ)) = 1 + p * (-(8 * e) - 16 * e * c) := by
        linear_combination (-1 : ℤ) * hc + (-8 - 16 * c) * he'
      rw [h3, Int.add_mul_emod_self_left]
    rw [jacobiSym.mod_left' this, jacobiSym.one_left]

theorem exists_q (d N : ℕ) (hd : d % 16 = 7) : ∃ q : ℕ, N < q ∧ q.Prime ∧ q % 8 = 3 ∧
    jacobiSym (-(d : ℤ)) q = 1 := by
  obtain ⟨s, hs⟩ : ∃ s : ℕ, d = 16 * s + 7 := ⟨d / 16, by omega⟩
  have hs' : (d : ℤ) = 16 * s + 7 := by exact_mod_cast hs
  have hco : IsCoprime (1 + 6 * (d : ℤ)) ((8 * d : ℕ) : ℤ) := by
    push_cast
    exact IsCoprime.mul_right ⟨3, -(36 * s + 16), by rw [hs']; ring⟩ ⟨1, -6, by ring⟩
  obtain ⟨q, hqN, hqp, hq⟩ := Nat.forall_exists_prime_gt_and_zmodEq N (q := 8 * d)
    (a := 1 + 6 * (d : ℤ)) (by omega) hco
  obtain ⟨c, hc⟩ := hq.symm.dvd
  push_cast at hc
  have h8 : q % 8 = 3 := by
    have h1 : (q : ℤ) = 8 * (12 * s + 5 + d * c) + 3 := by linear_combination hc + 6 * hs'
    omega
  refine ⟨q, hqN, hqp, h8, ?_⟩
  have hq4 : q % 4 = 3 := by omega
  have hd4 : d % 4 = 3 := by omega
  have hqd : jacobiSym (q : ℤ) d = 1 := by
    have : (q : ℤ) % d = 1 % d := by
      have h3 : (q : ℤ) = 1 + d * (6 + 8 * c) := by linear_combination hc
      rw [h3, Int.add_mul_emod_self_left]
    rw [jacobiSym.mod_left' this, jacobiSym.one_left]
  rw [jacobiSym.neg _ (Nat.odd_iff.2 (by omega)), ZMod.χ₄_nat_three_mod_four hq4,
    jacobiSym.quadratic_reciprocity_three_mod_four hd4 hq4, hqd]
  norm_num

theorem exists_one_mod (M N : ℕ) (hM : M ≠ 0) : ∃ g : ℕ, N < g ∧ g.Prime ∧ g ≡ 1 [MOD M] := by
  obtain ⟨g, h1, h2, h3⟩ := Nat.forall_exists_prime_gt_and_modEq N (q := M) (a := 1) hM (Nat.coprime_one_left M)
  exact ⟨g, h1, h2, h3⟩

theorem exc_dvd_prod {g e l : ℕ} (hg : 1 ≤ g) (h1 : 1 ≤ e) (h9 : e ≤ 9) (h : Formalism.CyclotomicNorms.Exc g e l) :
    l ∣ ∏ i ∈ Finset.range 9, (g ^ (i + 1) - 1) := by
  have hv : padicValNat l (g ^ e - 1) ≠ 0 := by
    intro h0
    have h2 := h.2
    rw [h0, mul_zero, pow_zero] at h2
    have := Nat.one_le_pow e g hg
    omega
  have h3 : g ^ e - 1 ∣ ∏ i ∈ Finset.range 9, (g ^ (i + 1) - 1) := by
    have := Finset.dvd_prod_of_mem (fun i => g ^ (i + 1) - 1) (Finset.mem_range.2 (show e - 1 < 9 by omega))
    rwa [Nat.sub_add_cancel h1] at this
  exact ((dvd_pow_self l hv).trans pow_padicValNat_dvd).trans h3

theorem not_exc_of_cong {M l g e c : ℕ} (hl : l.Prime) (hM : l ^ 4 ∣ M) (hM0 : 0 < M)
    (hg : g = 1 + M + M ^ 2 * c) (hbig : M ^ 7 ≤ g) (h1 : 1 ≤ e) (h9 : e ≤ 9) : ¬ Formalism.CyclotomicNorms.Exc g e l := by
  rintro ⟨-, hlt⟩
  have : Fact l.Prime := ⟨hl⟩
  set x : ℕ := M * (1 + M * c) with hx
  have hgx : g = x + 1 := by rw [hg, hx]; ring
  set S : ℕ := ∑ i ∈ Finset.range e, (x + 1) ^ i with hS
  have hgeo : S * x + 1 = g ^ e := by rw [hgx]; exact geom_sum_mul_add x e
  have hSe : S ≡ e [MOD M] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    rw [hS, hx]
    push_cast
    simp
  have h16 : 16 ≤ l ^ 4 := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ l ^ 4 := Nat.pow_le_pow_left hl.two_le 4
  have hnd : ¬ l ^ 4 ∣ S := by
    intro hd
    have := Nat.le_of_dvd (by omega) ((hSe.dvd_iff hM).1 hd)
    omega
  have hS0 : S ≠ 0 := by rintro h; exact hnd (h ▸ dvd_zero _)
  have hvS : padicValNat l S ≤ 3 := by
    by_contra hc
    exact hnd ((pow_dvd_pow l (by omega)).trans pow_padicValNat_dvd)
  have hlM : l ∣ M := (dvd_pow_self l (by norm_num)).trans hM
  have hv1 : padicValNat l (1 + M * c) = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro hd
    exact hl.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_left (hlM.mul_right c)).1 hd))
  have hval : padicValNat l (g ^ e - 1) = padicValNat l S + padicValNat l M := by
    rw [← hgeo, Nat.add_sub_cancel, hx, padicValNat.mul hS0 (by positivity),
      padicValNat.mul hM0.ne' (by positivity), hv1, add_zero]
  have hle : l ^ (4 * padicValNat l (g ^ e - 1)) ≤ M ^ 7 := by
    have a1 : l ^ padicValNat l M ≤ M := Nat.le_of_dvd hM0 pow_padicValNat_dvd
    have a2 : l ^ 4 ≤ M := Nat.le_of_dvd hM0 hM
    calc l ^ (4 * padicValNat l (g ^ e - 1)) ≤ l ^ (4 * 3 + 4 * padicValNat l M) :=
          Nat.pow_le_pow_right hl.pos (by rw [hval]; omega)
      _ = (l ^ 4) ^ 3 * (l ^ padicValNat l M) ^ 4 := by rw [pow_add, ← pow_mul, ← pow_mul, mul_comm 4 (padicValNat l M)]
      _ ≤ M ^ 3 * M ^ 4 := Nat.mul_le_mul (Nat.pow_le_pow_left a2 3) (Nat.pow_le_pow_left a1 4)
      _ = M ^ 7 := by ring
  have hge : g ≤ g ^ e := Nat.le_self_pow (by omega) g
  omega

theorem exists_bb_disjoint (m g0 : ℕ) (hm : m ≠ 0) (hg0 : g0.Prime) : ∃ g1 : ℕ, g0 < g1 ∧ g1.Prime ∧
    g1 ≡ 1 [MOD m] ∧ Disjoint (Formalism.CyclotomicNorms.BB 9 g0) (Formalism.CyclotomicNorms.BB 9 g1) := by
  set P : ℕ := g0 * ∏ i ∈ Finset.range 9, (g0 ^ (i + 1) - 1) with hP
  have hP0 : 0 < P := by
    refine Nat.mul_pos hg0.pos (Finset.prod_pos fun i _ => ?_)
    exact Nat.sub_pos_of_lt (Nat.one_lt_pow (Nat.succ_ne_zero i) hg0.one_lt)
  set M : ℕ := (m * P) ^ 4 with hM
  have hmP : 0 < m * P := Nat.mul_pos (Nat.pos_of_ne_zero hm) hP0
  have hM0 : 0 < M := pow_pos hmP 4
  have hPM : P ≤ M := by
    calc P ≤ m * P := Nat.le_mul_of_pos_left P (Nat.pos_of_ne_zero hm)
      _ ≤ (m * P) ^ 4 := Nat.le_self_pow (by norm_num) _
  have hco : (1 + M).Coprime (M ^ 2) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_add_self_left]
    exact Nat.coprime_one_left M
  obtain ⟨g1, hgt, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq (M ^ 7 + M + 1 + g0) (q := M ^ 2) (a := 1 + M)
    (pow_ne_zero 2 hM0.ne') hco
  obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd' (show 1 + M ≤ g1 by omega)).1 hmod.symm
  have hg1 : g1 = 1 + M + M ^ 2 * c := by omega
  have hbig : M ^ 7 ≤ g1 := by omega
  have hmM : m ∣ M := (Dvd.intro P rfl).trans (dvd_pow_self _ (by norm_num))
  refine ⟨g1, by omega, hp, ?_, ?_⟩
  · have h1 : g1 ≡ 1 + M [MOD m] := hmod.of_dvd (hmM.trans (dvd_pow_self M (by norm_num)))
    have h2 : 1 + M ≡ 1 + 0 [MOD m] := Nat.ModEq.add_left 1 ((Nat.modEq_zero_iff_dvd).2 hmM)
    exact h1.trans h2
  · rw [Set.disjoint_left]
    intro l hl0 hl1
    have hlP : l.Prime ∧ l ∣ P := by
      rcases hl0 with h | ⟨e, h1, h9, h⟩
      · rw [Set.mem_singleton_iff.1 h]; exact ⟨hg0, Dvd.intro _ rfl⟩
      · exact ⟨h.1, (exc_dvd_prod hg0.pos h1 h9 h).trans (Dvd.intro_left _ rfl)⟩
    rcases hl1 with h | ⟨e, h1, h9, h⟩
    · have := Nat.le_of_dvd hP0 hlP.2
      rw [Set.mem_singleton_iff.1 h] at this
      have : M ≤ M ^ 7 := Nat.le_self_pow (by norm_num) _
      omega
    · exact not_exc_of_cong hlP.1 (pow_dvd_pow_of_dvd (hlP.2.trans (Dvd.intro_left _ rfl)) 4) hM0 hg1 hbig h1 h9 h

structure Arith (B N : ℕ) where
  q : ℕ
  d : ℕ
  hyp : HostHyp q d
  q_gt : N < q
  d_gt : N < d
  split : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≤ B → jacobiSym (-(d : ℤ)) p = 1
  g0 : ℕ
  g1 : ℕ
  first_prime_isPrime : g0.Prime
  second_prime_isPrime : g1.Prime
  sixty_one_lt_first_prime : 61 < g0
  first_prime_lt_second : g0 < g1
  first_prime_modEq_one : g0 ≡ 1 [MOD 16 * q * d]
  second_prime_modEq_one : g1 ≡ 1 [MOD 16 * q * d]
  bb : Disjoint (Formalism.CyclotomicNorms.BB 9 g0) (Formalism.CyclotomicNorms.BB 9 g1)
  L : Type
  [instField : Field L]
  [instNF : NumberField L]
  ζ : L
  a : L
  b : L
  layer : IsLayer 4 q d ζ a b

attribute [instance] Arith.instField Arith.instNF

theorem arith_nonempty (B N : ℕ) : Nonempty (Arith B N) := by
  obtain ⟨d, hdN, hdp, hd16, hsp⟩ := exists_d B N
  obtain ⟨q, hqN, hqp, hq8, hj⟩ := exists_q d N hd16
  have hM : 16 * q * d ≠ 0 := Nat.mul_ne_zero (Nat.mul_ne_zero (by norm_num) hqp.ne_zero) hdp.ne_zero
  obtain ⟨g0, h0, h0p, h0m⟩ := exists_one_mod (16 * q * d) 61 hM
  obtain ⟨g1, h1, h1p, h1m, hbb⟩ := exists_bb_disjoint (16 * q * d) g0 hM h0p
  obtain ⟨L, iF, iN, ζ, a, b, hl⟩ := Formalism.TwoAdicCyclotomicDecomposition.layerExists 4 q d
  exact ⟨⟨q, d, ⟨hqp, hdp, hq8, hd16, hj⟩, hqN, hdN, hsp, g0, g1, h0p, h1p, h0, h1, h0m, h1m, hbb, L, ζ, a, b, hl⟩⟩

theorem frame2_inj : Function.Injective (Formalism.HC.cyclicFrame 2).h := Formalism.HC.frameCyc_h_injective 2 1

theorem Rt_h_injective (s : ℕ) : Function.Injective (Rt s).toFrame.h := frame2_inj

abbrev Arith.QS {B N : ℕ} (_ : Arith B N) : ℕ := 16

def Arith.ax {B N : ℕ} (A : Arith B N) : Formalism.HC.HostAx (Formalism.HC.cyclicFrame 2) :=
  Formalism.HC.D7.hostAx (Formalism.HC.cyclicFrame 2) frame2_inj A.hyp le_rfl A.layer

theorem Arith.ax_QS {B N : ℕ} (A : Arith B N) : A.ax.QS = A.QS := rfl

private theorem coprime_sixteen_of_mod {g q d : ℕ} (h : g ≡ 1 [MOD 16 * q * d]) : Nat.Coprime g 16 := by
  have h1 : g ≡ 1 [MOD 16] := (h.of_mul_right _).of_mul_right _
  rw [Nat.Coprime, h1.gcd_eq, Nat.gcd_one_left]

variable {s B : ℕ} (A : Arith B (4 * (2 * s + 15) * 9 + 1))

theorem Arith.cm_nonempty : A.ax.cmType.Nonempty := by
  apply Set.nonempty_of_ncard_ne_zero
  rw [A.ax.der.cmType.2.1]
  have := (Formalism.HC.cyclicFrame 2).ord_pos
  omega

theorem Arith.ax_cm_nonempty : A.ax.toHostRaw.cmType.Nonempty := A.cm_nonempty

theorem Arith.bb_ex : ∃ 𝔟 : Ideal (𝓞 A.ax.E),
    differentIdeal (𝓞 A.ax.K) (𝓞 A.ax.E) = 𝔟 * (A.ax.conj • 𝔟) ∧ 𝔟 ⊔ A.ax.conj • 𝔟 = ⊤ ∧
    ∀ σ : A.ax.E ≃ₐ[ℚ] A.ax.E, A.ax.gal σ ∈ (Formalism.HC.cyclicFrame 2).Psi → σ • 𝔟 = 𝔟 :=
  A.ax.der.principal

private theorem gal_sqq_ax (φ : Formalism.HC.Frame) (hinj : Function.Injective φ.h) {q d : ℕ} (hH : HostHyp q d)
    (he : 2 ≤ φ.e) {L : Type} [Field L] [NumberField L] {ζ a b : L} (h : IsLayer (φ.e + 2) q d ζ a b)
    (σ : (Formalism.HC.D7.hostRaw φ hinj hH he h).E ≃ₐ[ℚ] (Formalism.HC.D7.hostRaw φ hinj hH he h).E) :
    σ (Formalism.HC.D7.sqq φ hinj hH he h) =
      (((((Formalism.HC.D7.hostRaw φ hinj hH he h).gal σ).1.1 : ℤˣ) : ℤ) : (Formalism.HC.D7.hostRaw φ hinj hH he h).E) *
        Formalism.HC.D7.sqq φ hinj hH he h :=
  Formalism.HC.D7.gal_sqq φ hH h σ

def hostOf (u0 : (Rt s).A) (T Lw : ℕ) : Host (Rt s) where
  toHostAx := A.ax
  flPS := Formalism.HC.D7.psQ (Formalism.HC.cyclicFrame 2) frame2_inj A.hyp le_rfl A.layer
  sqq := Formalism.HC.D7.sqq (Formalism.HC.cyclicFrame 2) frame2_inj A.hyp le_rfl A.layer
  sqq_sq := Formalism.HC.D7.sqq_sq (Formalism.HC.cyclicFrame 2) frame2_inj A.hyp le_rfl A.layer
  gal_sqq := gal_sqq_ax (Formalism.HC.cyclicFrame 2) frame2_inj A.hyp le_rfl A.layer
  QS_exact := Formalism.HC.D7.exact (Formalism.HC.cyclicFrame 2) frame2_inj A.hyp le_rfl A.layer
  QS_le := show 2 ^ (2 + 2) ≤ (2 ^ 2) ^ 2 by norm_num
  o_pow := (congrArg (· ^ 64) (Formalism.HC.cyclicFrame_index 2)).trans_le ((one_pow 64).trans_le Nat.one_le_two_pow)
  q_ne_three := by have := A.q_gt; show A.q ≠ 3; omega
  qd_big := ⟨A.q_gt, A.d_gt⟩
  splitBound := B
  split_small := A.split
  small_le := fun l hl h2 hd =>
    absurd ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (hl.dvd_of_dvd_pow (n := 2 + 2) hd)) h2
  φ₀ := A.cm_nonempty.some
  φ₀_mem := A.cm_nonempty.some_mem
  𝔟 := A.bb_ex.choose
  𝔟_spec := ⟨A.bb_ex.choose_spec.1, A.bb_ex.choose_spec.2.1⟩
  𝔟_stable := A.bb_ex.choose_spec.2.2
  levelPrimes := {31, 61, A.g0, A.g1} ∪ ({T} : Finset ℕ).filter (fun p => Nat.Coprime p 16)
  g := ![A.g0, A.g1]
  g_prime := by intro i; fin_cases i; exacts [A.first_prime_isPrime, A.second_prime_isPrime]
  g_ne := by simpa using A.first_prime_lt_second.ne
  g_level := by intro i; fin_cases i <;> simp
  pde := 31
  pde' := 61
  pde_prime := by norm_num
  pde'_prime := by norm_num
  pde_ne := by norm_num
  pde_level := by simp
  pde_mod := by norm_num
  pde_ne_g := by
    have := A.sixty_one_lt_first_prime; have := A.first_prime_lt_second
    intro i; fin_cases i <;> simp <;> omega
  ccK := ⊤
  ccK_ne_bot := top_ne_bot
  ccK_primitive := fun m hm => top_primitive m hm
  ccK_split := fun P hP hle => absurd (top_le_iff.1 hle) hP.ne_top
  ccK_coprime := fun p _ => by rw [Ideal.absNorm_top]; exact Nat.coprime_one_left p
  ccK_coprimeS := by rw [Ideal.absNorm_top]; exact Nat.coprime_one_left _
  level_coprimeS := by
    intro p hp
    show Nat.Coprime p 16
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter] at hp
    rcases hp with (rfl | rfl | rfl | rfl) | h
    · norm_num
    · norm_num
    · exact coprime_sixteen_of_mod A.first_prime_modEq_one
    · exact coprime_sixteen_of_mod A.second_prime_modEq_one
    · exact h.2
  TT := ∅
  T2 := {0}
  u0 := u0
  Lw := Lw + 4
  two_le_Lw := by omega
  second_set_range := by intro j hs; simp at hs; subst hs; rw [show (Rt s).toFrame.n0 = 2 ^ 2 from Formalism.HC.cyclicFrame_order 2]; simp
  second_set_no_relation := by
    intro s₁ h₁ s₂ h₂ _ _ h12
    simp at h₁ h₂
    exact absurd (h₁.trans h₂.symm) h12
  CT2 := 0

theorem hostOf_levelPrimes (u0 : (Rt s).A) (T Lw : ℕ) : (hostOf A u0 T Lw).levelPrimes =
    {31, 61, A.g0, A.g1} ∪ ({T} : Finset ℕ).filter (fun p => Nat.Coprime p 16) := rfl

theorem hostOf_T_level (u0 : (Rt s).A) {T : ℕ} (Lw : ℕ) (hT : Odd T) : T ∈ (hostOf A u0 T Lw).levelPrimes :=
  Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_singleton_self T,
    Nat.Coprime.pow_right 4 (Nat.coprime_two_right.2 hT)⟩)

theorem hostOf_levelPrimes_of_odd (u0 : (Rt s).A) {T : ℕ} (Lw : ℕ) (hT : Odd T) :
    (hostOf A u0 T Lw).levelPrimes = {31, 61, A.g0, A.g1, T} := by
  have hc : Nat.Coprime T 16 := Nat.Coprime.pow_right 4 (Nat.coprime_two_right.2 hT)
  rw [hostOf_levelPrimes, Finset.filter_singleton, if_pos hc]
  ext p
  simp [or_assoc]

theorem hostOf_mem_level (u0 : (Rt s).A) {T : ℕ} (Lw : ℕ) (hT : Odd T) :
    T ∈ (hostOf A u0 T Lw).levelPrimes := hostOf_T_level A u0 Lw hT

end Formalism.MainNotions.Inhab

end
