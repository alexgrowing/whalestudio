import Formalism.LocalRingCardinality.DataHost
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ExplicitFormulaErrorOfHostConditions
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts

open NumberField Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition Formalism.HC Formalism.BasicNotions
open scoped Pointwise

noncomputable section

namespace HostParam.Seam

structure FieldRows {φ : Frame} (H : HostRaw φ) (b : ℕ) : Prop where
  psQ : H.PsQ
  sqq : ∃ s : H.E, s ^ 2 = -(H.q : H.E) ∧ ∀ σ : H.E ≃ₐ[ℚ] H.E, σ s = ((((H.gal σ).1.1 : ℤˣ) : ℤ) : H.E) * s
  QS_exact : H.Exact
  QS_le : H.QS ≤ φ.ord ^ 2
  o_pow : φ.o ^ 64 ≤ 2 ^ φ.e
  q_ne_three : H.q ≠ 3
  split_small : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≤ b → jacobiSym (-(H.d : ℤ)) p = 1
  small_le : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ H.QS → 4 * l ≤ b

structure Choices (φ : Frame) (H : HostRaw φ) where
  levelPrimes : Finset ℕ
  g : Fin 2 → ℕ
  g_prime : ∀ i, (g i).Prime
  g_ne : g 0 ≠ g 1
  g_level : ∀ i, g i ∈ levelPrimes
  pde : ℕ
  pde' : ℕ
  pde_prime : pde.Prime
  pde'_prime : pde'.Prime
  pde_ne : pde ≠ pde'
  pde_level : pde ∈ levelPrimes ∧ pde' ∈ levelPrimes
  pde_mod : pde % 15 = 1 ∧ pde' % 15 = 1
  pde_ne_g : ∀ i, pde ≠ g i ∧ pde' ≠ g i
  ccK : Ideal (𝓞 H.K)
  ccK_ne_bot : ccK ≠ ⊥
  ccK_primitive : ∀ m : ℕ, 1 < m → ¬ ccK ≤ Ideal.span {(m : 𝓞 H.K)}
  ccK_split : ∀ P : Ideal (𝓞 H.K), P.IsPrime → ccK ≤ P →
    (Ideal.absNorm P).Prime ∧ jacobiSym (-(H.d : ℤ)) (Ideal.absNorm P) = 1
  ccK_coprime : ∀ p ∈ insert 2 (insert 3 (insert 5 (insert H.q (insert H.d levelPrimes)))),
    Nat.Coprime (Ideal.absNorm ccK) p
  ccK_coprimeS : Nat.Coprime (Ideal.absNorm ccK) H.QS
  level_coprimeS : ∀ p ∈ levelPrimes, Nat.Coprime p H.QS
  TT : Finset φ.A
  T2 : Finset ℕ
  u0 : φ.A
  Lw : ℕ
  two_le_Lw : 2 ≤ Lw
  second_set_range : ∀ s ∈ T2, 4 * Lw * s < φ.n0
  second_set_no_relation : NoRel T2 Lw
  CT2 : ℝ

structure HostNF (R : Ranks) where
  ax : HostAx R.toFrame
  splitBound : ℕ
  what₂ : FieldRows ax.toHostRaw splitBound
  qd_big : 4 * R.t * R.r + 1 < ax.q ∧ 4 * R.t * R.r + 1 < ax.d
  sqq : ax.E
  sqq_sq : sqq ^ 2 = -(ax.q : ax.E)
  gal_sqq : ∀ σ : ax.E ≃ₐ[ℚ] ax.E, σ sqq = ((((ax.gal σ).1.1 : ℤˣ) : ℤ) : ax.E) * sqq
  φ₀ : ax.E →+* ℂ
  φ₀_mem : φ₀ ∈ ax.toHostRaw.cmType
  𝔟 : Ideal (𝓞 ax.E)
  𝔟_spec : differentIdeal (𝓞 ax.toHostRaw.K) (𝓞 ax.E) = 𝔟 * (ax.toHostRaw.conj • 𝔟) ∧ 𝔟 ⊔ ax.toHostRaw.conj • 𝔟 = ⊤
  𝔟_stable : ∀ σ : ax.E ≃ₐ[ℚ] ax.E, ax.gal σ ∈ R.Psi → σ • 𝔟 = 𝔟
  ch : Choices R.toFrame ax.toHostRaw

def HostNF.toHost {R : Ranks} (N : HostNF R) : Formalism.BasicNotions.Host R :=
  { N.ax, N.ch with
    flPS := N.what₂.psQ, sqq := N.sqq, sqq_sq := N.sqq_sq, gal_sqq := N.gal_sqq
    QS_exact := N.what₂.QS_exact, QS_le := N.what₂.QS_le, o_pow := N.what₂.o_pow, q_ne_three := N.what₂.q_ne_three
    qd_big := N.qd_big, splitBound := N.splitBound, split_small := N.what₂.split_small, small_le := N.what₂.small_le
    φ₀ := N.φ₀, φ₀_mem := N.φ₀_mem, 𝔟 := N.𝔟, 𝔟_spec := N.𝔟_spec, 𝔟_stable := N.𝔟_stable }

def HostNF.ofHost {R : Ranks} (H : Formalism.BasicNotions.Host R) : HostNF R :=
  { ax := H.toHostAx, splitBound := H.splitBound
    what₂ := ⟨H.flPS, ⟨H.sqq, H.sqq_sq, H.gal_sqq⟩, H.QS_exact, H.QS_le, H.o_pow, H.q_ne_three, H.split_small, H.small_le⟩
    qd_big := H.qd_big, sqq := H.sqq, sqq_sq := H.sqq_sq, gal_sqq := H.gal_sqq, φ₀ := H.φ₀, φ₀_mem := H.φ₀_mem
    𝔟 := H.𝔟, 𝔟_spec := H.𝔟_spec, 𝔟_stable := H.𝔟_stable, ch := { H with } }

theorem HostNF.toHost_ofHost {R : Ranks} (H : Formalism.BasicNotions.Host R) : (HostNF.ofHost H).toHost = H := rfl

theorem HostNF.ofHost_toHost {R : Ranks} (N : HostNF R) : HostNF.ofHost N.toHost = N := rfl

theorem exists_cmType {φ : Frame} (H : HostAx φ) : ∃ ψ : H.E →+* ℂ, ψ ∈ H.toHostRaw.cmType := by
  have h := H.der.cmType.2.1
  have := φ.ord_pos
  exact Set.nonempty_of_ncard_ne_zero (by omega)

theorem exists_hostNF (R : Ranks) (H : HostAx R.toFrame) {b : ℕ} (h : FieldRows H.toHostRaw b)
    (hq : 4 * R.t * R.r + 1 < H.q ∧ 4 * R.t * R.r + 1 < H.d) (c : Choices R.toFrame H.toHostRaw) :
    ∃ N : HostNF R, N.ax = H ∧ N.splitBound = b ∧ HEq N.ch c := by
  obtain ⟨s, hs1, hs2⟩ := h.sqq
  obtain ⟨ψ, hψ⟩ := exists_cmType H
  obtain ⟨𝔟, h1, h2, h3⟩ := H.der.principal
  exact ⟨⟨H, b, h, hq, s, hs1, hs2, ψ, hψ, 𝔟, ⟨h1, h2⟩, h3, c⟩, rfl, rfl, HEq.rfl⟩

theorem exists_host (R : Ranks) (H : HostAx R.toFrame) {b : ℕ} (h : FieldRows H.toHostRaw b)
    (hq : 4 * R.t * R.r + 1 < H.q ∧ 4 * R.t * R.r + 1 < H.d) (c : Choices R.toFrame H.toHostRaw) :
    ∃ D : Formalism.BasicNotions.Host R, D.toHostAx = H ∧ D.splitBound = b ∧ HEq (HostNF.ofHost D).ch c := by
  obtain ⟨N, hN1, hN2, hN3⟩ := exists_hostNF R H h hq c
  exact ⟨N.toHost, hN1, hN2, hN3⟩

private theorem span_natCast_ne_whole_of_one_lt (K : Type) [Field K] [NumberField K] (m : ℕ) (hm : 1 < m) :
    ¬ (⊤ : Ideal (𝓞 K)) ≤ Ideal.span {(m : 𝓞 K)} := by
  intro h
  have hu : IsUnit (m : 𝓞 K) := Ideal.span_singleton_eq_top.mp (top_le_iff.mp h)
  have hn := hu.map (Algebra.norm ℤ (S := 𝓞 K))
  rw [show ((m : 𝓞 K)) = algebraMap ℤ (𝓞 K) (m : ℤ) by simp, Algebra.norm_algebraMap] at hn
  have hd : Module.finrank ℤ (𝓞 K) ≠ 0 := Module.finrank_pos.ne'
  rw [isUnit_pow_iff hd, Int.isUnit_iff] at hn
  omega

theorem nonempty_choices {φ : Frame} (H : HostRaw φ) : Nonempty (Choices φ H) := by
  classical
  obtain ⟨a, hla, ha⟩ := Nat.exists_infinite_primes (H.QS + 1)
  obtain ⟨b, hlb, hb⟩ := Nat.exists_infinite_primes (a + 1)
  obtain ⟨c, hc, hbc, hc1⟩ := Nat.exists_prime_gt_modEq_one (k := 15) b (by norm_num)
  obtain ⟨d, hd, hcd, hd1⟩ := Nat.exists_prime_gt_modEq_one (k := 15) c (by norm_num)
  have cop : ∀ p : ℕ, p.Prime → H.QS < p → Nat.Coprime p H.QS := fun p hp hlt =>
    (Nat.Prime.coprime_iff_not_dvd hp).2 (fun hdv => absurd (Nat.le_of_dvd H.QS_pos hdv) (by omega))
  refine ⟨{
      levelPrimes := {a, b, c, d}
      g := ![a, b]
      g_prime := fun i => by fin_cases i <;> simpa
      g_ne := by simp; omega
      g_level := fun i => by fin_cases i <;> simp
      pde := c
      pde' := d
      pde_prime := hc
      pde'_prime := hd
      pde_ne := by omega
      pde_level := by simp
      pde_mod := ⟨by simpa [Nat.ModEq] using hc1, by simpa [Nat.ModEq] using hd1⟩
      pde_ne_g := fun i => by fin_cases i <;> simp <;> omega
      ccK := ⊤
      ccK_ne_bot := top_ne_bot
      ccK_primitive := fun m hm => span_natCast_ne_whole_of_one_lt _ m hm
      ccK_split := fun P hP hle => absurd (top_le_iff.mp hle) hP.ne_top
      ccK_coprime := by simp
      ccK_coprimeS := by simp
      level_coprimeS := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rintro p (rfl | rfl | rfl | rfl) <;> apply cop <;> first | assumption | omega
      TT := ∅
      T2 := ∅
      u0 := Classical.arbitrary _
      Lw := 2
      two_le_Lw := le_rfl
      second_set_range := by simp
      second_set_no_relation := by simp [NoRel]
      CT2 := 0 }⟩

structure PairAt (T : HType) (X : ℝ) (q d : ℕ) : Prop where
  hyp : HostHyp q d
  log_q : T.z X / 2 < Real.log q ∧ Real.log q ≤ T.z X
  log_d : T.z' X / 2 < Real.log d ∧ Real.log d ≤ T.z' X
  split : ∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℝ) ≤ T.z X → jacobiSym (-(d : ℤ)) p = 1

end HostParam.Seam

end
