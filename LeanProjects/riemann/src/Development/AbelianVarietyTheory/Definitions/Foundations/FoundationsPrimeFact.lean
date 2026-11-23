import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Development.AbelianVarietyTheory.Definitions.Foundations.AuxiliaryFrameNormalizedSpaces
import Formalism.LocalRingCardinality.ConjSqrtMinusD
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.NonemptyFieldAxiomsCyclicPow
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts

noncomputable section

namespace GlobalTheory.Mem.Cert

noncomputable def powMod (a m k : ℕ) : ℕ → ℕ :=
  Nat.rec (fun _ => 1) (fun _ ih e => (ih (e / 2) ^ 2 * a ^ (e % 2)) % m) k

theorem powMod_succ (a m k e : ℕ) : powMod a m (k + 1) e = (powMod a m k (e / 2) ^ 2 * a ^ (e % 2)) % m := rfl

theorem powMod_cast (a m k : ℕ) : ∀ e : ℕ, e < 2 ^ k → ((powMod a m k e : ℕ) : ZMod m) = (a : ZMod m) ^ e := by
  induction k with
  | zero =>
    intro e h
    obtain rfl : e = 0 := by omega
    simp [powMod]
  | succ k ih =>
    intro e h
    rw [powMod_succ, ZMod.natCast_mod, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow,
      ih (e / 2) (by rw [pow_succ] at h; omega), ← pow_mul, ← pow_add]
    congr 1
    omega

theorem mem_of_dvd_prod_pow {l : List ℕ} (hl : ∀ q ∈ l, q.Prime) {n N q : ℕ} (hn : n ∣ l.prod ^ N) (hq : q.Prime)
    (h : q ∣ n) : q ∈ l := by
  obtain ⟨x, hx, hqx⟩ := hq.prime.dvd_prod_iff.1 (hq.dvd_of_dvd_pow (h.trans hn))
  rwa [(Nat.prime_dvd_prime_iff_eq hq (hl x hx)).1 hqx]

theorem prime_of_cert (p a k N : ℕ) (l : List ℕ) (hl : ∀ q ∈ l, q.Prime) (hp : 1 < p) (hk : p < 2 ^ k)
    (hN : p - 1 ∣ l.prod ^ N) (h1 : powMod a p k (p - 1) % p = 1)
    (h2 : ∀ q ∈ l, powMod a p k ((p - 1) / q) % p ≠ 1) : p.Prime := by
  have key : ∀ e, e ≤ p - 1 → ((a : ZMod p) ^ e = 1 ↔ powMod a p k e % p = 1) := fun e he => by
    rw [← powMod_cast a p k e (by omega), ← Nat.cast_one, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hp]
  refine lucas_primality p a ((key _ le_rfl).2 h1) fun q hq hd h => ?_
  exact h2 q (mem_of_dvd_prod_pow hl hN hq hd) ((key _ (Nat.div_le_self _ _)).1 h)

theorem foundations_prime_fact_ter : Nat.Prime 10944929 :=
  prime_of_cert _ 3 24 5 [2, 571, 599] (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem prime_128860109809 : Nat.Prime 128860109809 :=
  prime_of_cert _ 13 40 4 [2, 3, 47, 167, 571, 599] (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem foundations_prime_fact : Nat.Prime 328347841 :=
  prime_of_cert _ 11 32 6 [2, 3, 5, 571, 599] (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem foundations_prime_fact_bis : Nat.Prime 1395478321 :=
  prime_of_cert _ 11 32 4 [2, 3, 5, 17, 571, 599] (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem siteGood_prime_torsion : Nat.Prime (1 + 599 * (123 * (16 * 571 * 599 * (10944929 * 128860109809) ^ 2)) ^ 2) :=
  prime_of_cert _ 5 320 8 [2, 3, 41, 571, 599, 10944929, 128860109809]
    (by
      have h0 := foundations_prime_fact_ter
      have h1 := prime_128860109809
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, h0, h1⟩)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem not_exc {g e l k : ℕ} (hl : 1 < l) (he : 1 ≤ e) (hg : l ^ (4 * k) ≤ g) (h : ¬ l ^ (k + 1) ∣ g ^ e - 1) :
    ¬ Formalism.CyclotomicNorms.Exc g e l := by
  rintro ⟨-, hlt⟩
  have hv : padicValNat l (g ^ e - 1) ≤ k := by
    by_contra hc
    exact h ((pow_dvd_pow l (by omega)).trans pow_padicValNat_dvd)
  have h1 : l ^ (4 * padicValNat l (g ^ e - 1)) ≤ l ^ (4 * k) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : g ≤ g ^ e := Nat.le_self_pow (by omega) g
  omega

theorem bb_disjoint : Disjoint (Formalism.CyclotomicNorms.BB 9 10944929) (Formalism.CyclotomicNorms.BB 9 128860109809) := by
  have key : ∀ g l : ℕ, g.Prime → l ∈ Formalism.CyclotomicNorms.BB 9 g → l.Prime ∧ l ∣ g * ∏ i ∈ Finset.range 9, (g ^ (i + 1) - 1) := by
    rintro g l hg (h | ⟨e, h1, h9, h⟩)
    · rw [Set.mem_singleton_iff.1 h]; exact ⟨hg, Dvd.intro _ rfl⟩
    · exact ⟨h.1, (Formalism.MainNotions.Inhab.exc_dvd_prod hg.pos h1 h9 h).trans (Dvd.intro_left _ rfl)⟩
  rw [Set.disjoint_left]
  intro l h0 h1
  obtain ⟨hl, d0⟩ := key _ _ foundations_prime_fact_ter h0
  have hmem : l ∈ [2, 3, 5, 7, 19, 571, 599] :=
    mem_of_dvd_prod_pow (N := 43) (by norm_num) (by decide +kernel) hl (Nat.dvd_gcd d0 (key _ _ prime_128860109809 h1).2)
  rcases h1 with h | ⟨e, h1, h9, h⟩
  · rw [Set.mem_singleton_iff.1 h] at hmem
    exact absurd hmem (by decide +kernel)
  · have hall : ∀ x ∈ [(2, 7), (3, 3), (5, 1), (7, 2), (19, 1), (571, 1), (599, 1)], 1 < x.1 ∧
        x.1 ^ (4 * x.2) ≤ 128860109809 ∧ ∀ e < 10, 1 ≤ e → ¬ x.1 ^ (x.2 + 1) ∣ 128860109809 ^ e - 1 := by
      decide +kernel
    obtain ⟨k, hk⟩ : ∃ k, (l, k) ∈ [(2, 7), (3, 3), (5, 1), (7, 2), (19, 1), (571, 1), (599, 1)] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    obtain ⟨a1, a2, a3⟩ := hall _ hk
    exact not_exc a1 h1 a2 (a3 e (by omega) h1) h

end GlobalTheory.Mem.Cert

namespace GlobalTheory.Mem.Explicit

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition NumberField GlobalTheory.Mem.Cert
open scoped Pointwise

theorem hyp : HostHyp 571 599 := ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

def modulus : ℕ := 16 * 571 * 599 * (10944929 * 128860109809) ^ 2

def level : ℕ := 1 + 599 * (123 * modulus) ^ 2

theorem level_prime : level.Prime := siteGood_prime_torsion

section

variable {L : Type} [Field L] [NumberField L] {ζ a b : L} (hl : IsLayer (R0.e + 2) 571 599 ζ a b)

def ax : Formalism.HC.HostAx R0.toFrame := Formalism.HC.D7.hostAx R0.toFrame exampleRanks_h_injective hyp le_rfl hl

theorem cm_nonempty : (ax hl).cmType.Nonempty := by
  apply Set.nonempty_of_ncard_ne_zero
  rw [(ax hl).der.cmType.2.1]
  simp

theorem half_exists : ∃ 𝔟 : Ideal (𝓞 (ax hl).E),
    differentIdeal (𝓞 (ax hl).K) (𝓞 (ax hl).E) = 𝔟 * ((ax hl).conj • 𝔟) ∧ 𝔟 ⊔ (ax hl).conj • 𝔟 = ⊤ ∧
    ∀ σ : (ax hl).E ≃ₐ[ℚ] (ax hl).E, (ax hl).gal σ ∈ R0.Psi → σ • 𝔟 = 𝔟 :=
  (ax hl).der.principal

def host : Host R0 where
  toHostAx := ax hl
  flPS := Formalism.HC.D7.psQ R0.toFrame exampleRanks_h_injective hyp le_rfl hl
  sqq := Formalism.HC.D7.sqq R0.toFrame exampleRanks_h_injective hyp le_rfl hl
  sqq_sq := Formalism.HC.D7.sqq_sq R0.toFrame exampleRanks_h_injective hyp le_rfl hl
  gal_sqq := Formalism.HC.D7.gal_sqq R0.toFrame hyp hl
  QS_exact := Formalism.HC.D7.exact R0.toFrame exampleRanks_h_injective hyp le_rfl hl
  QS_le := (by norm_num : 16 ≤ 4 ^ 2)
  o_pow := by rw [exampleRanks_o]; simp
  q_ne_three := (by norm_num : 571 ≠ 3)
  qd_big := (by norm_num : 4 * 15 * 9 + 1 < 571 ∧ 4 * 15 * 9 + 1 < 599)
  splitBound := 5
  split_small := by
    intro p hp h2 h5
    change jacobiSym (-((599 : ℕ) : ℤ)) p = 1
    have := hp.two_le
    interval_cases p
    · exact absurd rfl h2
    · norm_num
    · exact absurd hp (by norm_num)
    · norm_num
  small_le := fun l hp h2 hd =>
    absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow (show l ∣ 2 ^ 4 from hd))) h2
  φ₀ := (cm_nonempty hl).some
  φ₀_mem := (cm_nonempty hl).some_mem
  𝔟 := (half_exists hl).choose
  𝔟_spec := ⟨(half_exists hl).choose_spec.1, (half_exists hl).choose_spec.2.1⟩
  𝔟_stable := (half_exists hl).choose_spec.2.2
  levelPrimes := {10944929, 128860109809, 328347841, 1395478321, level}
  level_coprimeS := by
    intro p hp
    change Nat.Coprime p 16
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  g := ![10944929, 128860109809]
  g_prime := by intro i; fin_cases i; exacts [foundations_prime_fact_ter, prime_128860109809]
  g_ne := by simp
  g_level := by intro i; fin_cases i <;> simp
  pde := 328347841
  pde' := 1395478321
  pde_prime := foundations_prime_fact
  pde'_prime := foundations_prime_fact_bis
  pde_ne := by norm_num
  pde_level := by simp
  pde_mod := by norm_num
  pde_ne_g := by intro i; fin_cases i <;> simp
  ccK := ⊤
  ccK_ne_bot := top_ne_bot
  ccK_primitive := fun m hm => Formalism.MainNotions.Inhab.top_primitive m hm
  ccK_split := fun P hP hle => absurd (top_le_iff.1 hle) hP.ne_top
  ccK_coprime := fun p _ => by rw [Ideal.absNorm_top]; exact Nat.coprime_one_left p
  ccK_coprimeS := by rw [Ideal.absNorm_top]; exact Nat.coprime_one_left _
  TT := {0}
  T2 := {0}
  u0 := 0
  Lw := 2
  two_le_Lw := le_rfl
  second_set_range := by intro s hs; simp at hs; subst hs; simp [exampleRanks_baseRank]
  second_set_no_relation := by
    intro s₁ h₁ s₂ h₂ _ _ h12
    simp at h₁ h₂
    exact absurd (h₁.trans h₂.symm) h12
  CT2 := 0

end

def rootInt {R : Ranks} (H : Host R) : 𝓞 H.E :=
  ⟨H.sqrtMinusD, IsIntegral.of_pow two_pos (by
    rw [show H.sqrtMinusD ^ 2 = -(H.d : H.E) from H.sqd_sq]
    exact (isIntegral_natCast _).neg)⟩

theorem norm_one_add {R : Ranks} (H : Host R) (c : ℕ) :
    ((1 + c * rootInt H : 𝓞 H.E) : H.E) * H.conj ((1 + c * rootInt H : 𝓞 H.E) : H.E) = ((1 + H.d * c ^ 2 : ℕ) : H.E) := by
  have h : ((1 + c * rootInt H : 𝓞 H.E) : H.E) = 1 + c * H.sqrtMinusD := by
    simp only [RingOfIntegers.coe_eq_algebraMap, map_add, map_one, map_mul, map_natCast]
    rfl
  have h1 : H.conj H.sqrtMinusD = -H.sqrtMinusD := H.conj_sqd
  have h2 : H.sqrtMinusD ^ 2 = -(H.d : H.E) := H.sqd_sq
  rw [h, map_add, map_one, map_mul, map_natCast, h1]
  push_cast
  linear_combination (-(c : H.E) ^ 2) * h2

theorem one_add_mem {R : Ranks} (H : Host R) (c : ℕ) : ((1 + c * rootInt H : 𝓞 H.E) : H.E) ∈ H.K := by
  have h : ((1 + c * rootInt H : 𝓞 H.E) : H.E) = 1 + c * H.sqrtMinusD := by
    simp only [RingOfIntegers.coe_eq_algebraMap, map_add, map_one, map_mul, map_natCast]
    rfl
  rw [h]
  exact add_mem (one_mem _) (mul_mem (natCast_mem _ _) (IntermediateField.mem_adjoin_simple_self ℚ _))

theorem window {x s : ℝ} (hx : 0 < x) (hs : 0 < s) :
    (4 * x ^ s / ((1 : ℕ) : ℝ)) ^ ((1 : ℝ) / s) * (2 : ℝ) ^ (-(2 : ℝ) / s) = x := by
  rw [Nat.cast_one, div_one, Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hx.le,
    mul_one_div_cancel hs.ne', Real.rpow_one, show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num,
    ← Real.rpow_mul (by norm_num), mul_right_comm, ← Real.rpow_add (by norm_num)]
  rw [show (2 : ℝ) * (1 / s) + -2 / s = 0 by ring, Real.rpow_zero, one_mul]

section

variable {L : Type} [Field L] [NumberField L] {ζ a b : L} (hl : IsLayer (R0.e + 2) 571 599 ζ a b)

theorem gen_norm : letI := (host hl).cmStar;
    star ((1 + (123 * modulus : ℕ) * rootInt (host hl) : 𝓞 (host hl).E) : (host hl).E) *
      ((1 + (123 * modulus : ℕ) * rootInt (host hl) : 𝓞 (host hl).E) : (host hl).E) = (level : (host hl).E) := by
  rw [mul_comm, bridge_star_holds R0 (host hl)]
  exact norm_one_add (host hl) _

def pre : Pre where
  R := R0
  host := host hl
  ccK_top := rfl
  level_cond := by
    intro p hp
    change p.Prime ∧ p % (16 * 571 * 599) = 1
    simp only [host, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    exacts [⟨foundations_prime_fact_ter, by norm_num⟩, ⟨prime_128860109809, by norm_num⟩, ⟨foundations_prime_fact, by norm_num⟩, ⟨foundations_prime_fact_bis, by norm_num⟩,
      ⟨level_prime, by decide +kernel⟩]
  BB_disj := bb_disjoint
  sp := letI := (host hl).cmStar
    spacesNorm R0 (host_cmData R0 (host hl)) level level_prime _ (gen_norm hl)
  Y_sigval := letI := (host hl).cmStar; fun j _ τ => spacesNorm_Y_sig R0 _ _ _ _ _ j τ
  auxiliaryFrame := letI := (host hl).cmStar; fun j _ hj => auxiliary_frame_normalized_spaces R0 _ _ _ _ _ j hj
  V_pos := fun _ _ _ => rfl
  z_norm := letI := (host hl).cmStar; spacesNorm_z_norm R0 _ _ _ _ _
  Word := Bool
  u₀ := false
  hc := fun _ => hcParamOfCodeWord R0 2 0 18 le_rfl le_rfl fun _ => false
  hcW := fun u _ => hcParamOfCodeWord R0 2 0 18 le_rfl le_rfl fun _ => u
  hcW_base := rfl
  hcW_v := fun _ _ => rfl
  hcW_b := fun _ _ => rfl
  hcW_e := fun _ _ => rfl
  hcW_first := fun _ _ _ => rfl
  hcW_last := fun _ _ _ => by simp [hcParamOfCodeWord]
  T := fun _ => level
  T_level := fun _ => by simp [host]
  T_norm := fun _ => ⟨1 + (123 * modulus : ℕ) * rootInt (host hl), one_add_mem _ _, norm_one_add (host hl) _, by
    rw [add_sub_cancel_left, Ideal.mem_span_singleton]
    refine Dvd.dvd.mul_right (Nat.cast_dvd_cast ?_) _
    exact Dvd.intro_left 123 rfl⟩
  sp_T := rfl
  cOf := fun _ => 1
  cOf_ne := fun _ => one_ne_zero
  cOf_eq := fun _ => by simp
  T_ne_pde := fun _ => by
    change level ≠ 328347841 ∧ level ≠ 1395478321
    decide +kernel
  duStar := fun _ => 1
  duStar_pos := fun _ => one_pos
  Dstar := 4 * (level : ℝ) ^ ((R0.f : ℝ) * R0.k)
  Dstar_pos := by
    have : (0 : ℝ) < level := by exact_mod_cast level_prime.pos
    positivity
  GamP := 2
  one_lt_gammaP := one_lt_two
  T_win := fun _ => by
    have h : (0 : ℝ) < level := by exact_mod_cast level_prime.pos
    have hs : (0 : ℝ) < (R0.f : ℝ) * R0.k := by simp
    rw [window h hs]
    refine ⟨le_rfl, le_mul_of_one_le_left h.le ?_⟩
    have := one_div_pos.2 hs
    linarith

theorem pre_hcW_injective : Function.Injective (pre hl).hcW := by
  have hne : Nonempty (Tau R0) := ⟨1⟩
  obtain ⟨τ⟩ := hne
  intro u u' h
  have h1 := congrArg (fun x => (x τ).u ⟨1, (by norm_num : 1 < 8)⟩) h
  revert h1
  change Bool at u u'
  cases u <;> cases u' <;> simp [pre, hcParamOfCodeWord] <;> norm_num

end

end GlobalTheory.Mem.Explicit

theorem GlobalTheory.Mem.exists_pre : ∃ B : GlobalTheory.Mem.Pre, Fintype.card B.Word = 2 ∧ Function.Injective B.hcW := by
  obtain ⟨L, _, _, ζ, a, b, hl⟩ := Formalism.TwoAdicCyclotomicDecomposition.layerExists (Formalism.BasicNotions.Examples₂.R0.e + 2) 571 599
  exact ⟨GlobalTheory.Mem.Explicit.pre hl, rfl, GlobalTheory.Mem.Explicit.pre_hcW_injective hl⟩

end
