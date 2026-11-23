import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalEmbeddingRangeEqField
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniformizerGaloisAction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormSubLeOfNear
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

namespace GlobalTheory.CompanionTheory.LTPer.Tilt.GalDiv

variable {l : ℕ} [Fact l.Prime]

theorem continuous_omC : Continuous (omC (l := l)) :=
  (AddMonoidHomClass.isometry_of_norm (omC (l := l)) norm_omC).continuous

theorem tail_le (K : FinExt l) (c : ℕ → ↥(OL K)) (y x : Om l) (hy : ‖omC y‖ ≤ 1)
    (hs : HasSum (fun k : ℕ => ((c k : ↥K.1) : Om l) * y ^ k) x) (D : ℕ) :
    ‖omC x - ∑ i ∈ Finset.range D, oc K (c i) * omC y ^ i‖ ≤ ‖omC y‖ ^ D := by
  have ht : Filter.Tendsto (fun N => ∑ i ∈ Finset.range N, oc K (c i) * omC y ^ i)
      Filter.atTop (nhds (omC x)) := by
    have h1 := (continuous_omC (l := l)).continuousAt.tendsto.comp hs.tendsto_sum_nat
    refine h1.congr fun N => ?_
    simp only [Function.comp, map_sum, map_mul, map_pow]
    rfl
  have h2 := (ht.sub_const (∑ i ∈ Finset.range D, oc K (c i) * omC y ^ i)).norm
  refine le_of_tendsto h2 ?_
  filter_upwards [Filter.eventually_ge_atTop D] with N hN
  rw [← Finset.sum_Ico_eq_sub _ hN]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k hk => ?_
  rw [norm_mul, norm_pow]
  exact (mul_le_of_le_one_left (by positivity) (norm_oc_le_one K _)).trans
    (pow_le_pow_of_le_one (norm_nonneg _) hy (Finset.mem_Ico.1 hk).1)

theorem norm_read {ρ : ℝ} (hρ : ‖(l : ℂ_[l])‖ ≤ ρ) (a y : Tl l) (b : ℕ → Tl l)
    (A Y : ℂ_[l]) (B : ℕ → ℂ_[l]) (D : ℕ) (hY : ‖Y‖ ≤ 1) (hA : ‖sh a - A‖ ≤ ρ)
    (hy : ‖sh y - Y‖ ≤ ρ) (hb : ∀ i, ‖sh (b i) - B i‖ ≤ ρ) :
    ‖a - ∑ i ∈ Finset.range D, b i * y ^ i‖ ≤
      max ρ ‖A - ∑ i ∈ Finset.range D, B i * Y ^ i‖ := by
  have h1 : ‖sh (∑ i ∈ Finset.range D, b i * y ^ i) - ∑ i ∈ Finset.range D, B i * Y ^ i‖ ≤ ρ :=
    near_sum hρ _ fun i _ => near_mul (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hY)
      (hb i) (near_pow hρ hY hy i)
  have h2 := near_sub hρ hA h1
  rw [norm_eq_norm_sh]
  set x := a - ∑ i ∈ Finset.range D, b i * y ^ i
  set W := A - ∑ i ∈ Finset.range D, B i * Y ^ i
  have e : sh x = (sh x - W) + W := by ring
  rw [e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max h2 le_rfl)

theorem pow_read (N : ℕ) (a y : Tl l) (b : ℕ → Tl l) (D : ℕ) :
    (a - ∑ i ∈ Finset.range D, b i * y ^ i) ^ l ^ N =
      a ^ l ^ N - ∑ i ∈ Finset.range D, b i ^ l ^ N * (y ^ l ^ N) ^ i := by
  rw [sub_pow_char_pow, sum_pow_char_pow]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm i]

theorem pow_compat {f : ℕ} {u : ℕ → Tl l} (hu : ∀ n, u (n + 1) ^ l ^ f = u n) (n m : ℕ) :
    u (n + m) ^ l ^ (f * m) = u n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← add_assoc, mul_add, mul_one, add_comm (f * m) f, pow_add, pow_mul, hu, ih]

theorem pow_fixed {f : ℕ} {x : Tl l} (hx : x ^ l ^ f = x) (m : ℕ) : x ^ l ^ (f * m) = x := by
  induction m with
  | zero => simp
  | succ m ih => rw [mul_add, mul_one, add_comm (f * m) f, pow_add, pow_mul, hx, ih]

theorem exists_pow_le {f : ℕ} (hf : 0 < f) {ρ ε : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) (hε : 0 < ε) :
    ∃ m, 2 ≤ m ∧ ρ ^ l ^ (f * m) ≤ ε := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε h1
  refine ⟨N + 2, by omega, (pow_le_pow_of_le_one h0 h1.le ?_).trans hN.le⟩
  have h2 : N + 2 < l ^ (N + 2) := Nat.lt_pow_self (Fact.out : l.Prime).one_lt
  have h3 : l ^ (N + 2) ≤ l ^ (f * (N + 2)) :=
    Nat.pow_le_pow_right (Fact.out : l.Prime).pos (Nat.le_mul_of_pos_left _ hf)
  omega

theorem galdiv : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)) (z : ℕ → Om l) (f : ℕ), 0 < f →
    ‖(l : ℂ_[l])‖ ≤ ‖oc K π‖ → ‖oc K π‖ < 1 →
    (∀ n, ‖omC (z n)‖ < 1) → (∀ n, 2 ≤ n → ‖oc K π‖ < ‖omC (z n)‖) →
    ∀ (u : ℕ → Tl l), (∀ n, u (n + 1) ^ l ^ f = u n) → (∀ n, ‖sh (u n) - omC (z n)‖ ≤ ‖oc K π‖) →
    ∀ (r₀ : ↥(OL K) →+* Tl l), (∀ c, r₀ c ^ l ^ f = r₀ c) → (∀ c, ‖sh (r₀ c) - oc K c‖ ≤ ‖oc K π‖) →
    (∀ n, u n ≠ 0) → ∀ (g : GQ l) (c : ℕ → ↥(OL K)),
    (∀ n, HasSum (fun k : ℕ => ((c k : ↥K.1) : Om l) * z n ^ k) (g (z n))) → ∀ n D : ℕ,
    u n ^ D ∣ actT g (u n) - ∑ i ∈ Finset.range D, r₀ (c i) * u n ^ i := by
  intro l _ K π z f hf hl hπ hz1 hz2 u hu hun r₀ hr hrn hu0 g c hs n D
  rw [GroundTheory.PAdicHodge.preTilt_dvd_iff_norm_le, norm_pow]
  set ρ := ‖oc K π‖ with hρdef
  have hρ0 : 0 ≤ ρ := norm_nonneg _
  have hε : 0 < ‖u n‖ ^ D := pow_pos (norm_pos_iff.2 (hu0 n)) D
  obtain ⟨m, hm, hmρ⟩ := exists_pow_le (l := l) hf hρ0 hπ hε
  set k := n + m with hk
  have hk2 : 2 ≤ k := by omega
  have hzk : ‖omC (z k)‖ ≤ 1 := (hz1 k).le
  have hnorm : ‖omC (z k)‖ ≤ ‖u k‖ := by
    by_contra hlt
    push_neg at hlt
    have e : omC (z k) = sh (u k) - (sh (u k) - omC (z k)) := by ring
    have h3 : ‖omC (z k)‖ ≤ max ‖sh (u k)‖ ρ := by
      conv_lhs => rw [e, sub_eq_add_neg]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans
        (max_le_max le_rfl (by rw [norm_neg]; exact hun k))
    rcases le_max_iff.1 h3 with h4 | h4
    · rw [← norm_eq_norm_sh] at h4; linarith
    · linarith [hz2 k hk2]
  have hA : ‖sh (actT g (u k)) - omC (g (z k))‖ ≤ ρ := by
    rw [sh_actT, ← galCp_omC, ← map_sub, norm_galCp]
    exact hun k
  have hread := norm_read hl (actT g (u k)) (u k) (fun i => r₀ (c i)) (omC (g (z k))) (omC (z k))
    (fun i => oc K (c i)) D hzk hA (hun k) (fun i => hrn _)
  have htail := tail_le K c (z k) (g (z k)) hzk (hs k) D
  have hx : ‖actT g (u k) - ∑ i ∈ Finset.range D, r₀ (c i) * u k ^ i‖ ≤ max ρ (‖u k‖ ^ D) :=
    hread.trans (max_le_max le_rfl (htail.trans (pow_le_pow_left₀ (norm_nonneg _) hnorm D)))
  have hpow := pow_read (f * m) (actT g (u k)) (u k) (fun i => r₀ (c i)) D
  have hc : u k ^ l ^ (f * m) = u n := pow_compat hu n m
  have ha : actT g (u k) ^ l ^ (f * m) = actT g (u n) := by rw [← map_pow, hc]
  simp only [pow_fixed (hr _) m, hc, ha] at hpow
  rw [← hpow, norm_pow]
  have hun' : ‖u k‖ ^ l ^ (f * m) = ‖u n‖ := by rw [← norm_pow, hc]
  refine (pow_le_pow_left₀ (norm_nonneg _) hx _).trans ?_
  rcases le_total ρ (‖u k‖ ^ D) with h | h
  · rw [max_eq_right h, ← pow_mul, mul_comm, pow_mul, hun']
  · rw [max_eq_left h]; exact hmρ

end GlobalTheory.CompanionTheory.LTPer.Tilt.GalDiv
