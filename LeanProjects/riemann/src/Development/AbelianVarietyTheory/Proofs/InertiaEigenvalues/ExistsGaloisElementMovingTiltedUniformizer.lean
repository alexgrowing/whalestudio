import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanOfPowMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPowRamifiedUniformizerFieldZpow
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.KummerMove

section
variable {l : ℕ} [hl : Fact l.Prime]

theorem comm_root (σ τ : GQ l) (n : ℕ) (y : Om l) (hy : y ^ l ^ n = 1) : σ (τ y) = τ (σ y) := by
  have hpos : 0 < l ^ n := pow_pos hl.out.pos n
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic (restrictRootsOfUnity σ (l ^ n))
  have hr : ∀ w : Om l, w ^ l ^ n = 1 → σ w = w ^ m := by
    intro w hw
    have hw0 : w ≠ 0 := by rintro rfl; simp [zero_pow hpos.ne'] at hw
    let u : rootsOfUnity (l ^ n) (Om l) := ⟨Units.mk0 w hw0, by
      rw [mem_rootsOfUnity]; ext; simpa using hw⟩
    have h1 := congrArg (fun v : rootsOfUnity (l ^ n) (Om l) => ((v : (Om l)ˣ) : Om l)) (hm u)
    simpa [u] using h1
  have hτ : (τ y) ^ l ^ n = 1 := by rw [← map_pow, hy, map_one]
  rw [hr _ hτ, hr _ hy, map_zpow₀]

variable {e : ℕ} [NeZero e]

theorem ratio_pow (ϖ : PiSys l e) (g : GQ l) (h0 : g (ϖ.seq 0) = ϖ.seq 0)
    (hroot : ∀ (n : ℕ) (y : Om l), y ^ l ^ n = 1 → g y = y) (k n : ℕ) :
    ϖ.ratio (g ^ k) n = ϖ.ratio g n ^ k := by
  set r := g (ϖ.seq n) / ϖ.seq n with hrdef
  have hs0 := ϖ.seq_ne_zero n
  have hr : r ^ l ^ n = 1 := by
    rw [hrdef, div_pow, ← map_pow, ϖ.seq_pow, h0, div_self (ϖ.seq_ne_zero 0)]
  have hgr : g r = r := hroot n r hr
  have hg : g (ϖ.seq n) = r * ϖ.seq n := by rw [hrdef, div_mul_cancel₀ _ hs0]
  have hk : ∀ k : ℕ, (g ^ k) (ϖ.seq n) = r ^ k * ϖ.seq n := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_pow, hgr, hg, pow_succ]
      ring
  refine Subtype.ext ?_
  rw [PiSys.coe_ratio, SubmonoidClass.coe_pow, PiSys.coe_ratio, ← map_pow, hk, mul_div_cancel_right₀ _ hs0]

theorem kummer_pow (ϖ : PiSys l e) (g : GQ l) (h0 : g (ϖ.seq 0) = ϖ.seq 0)
    (hroot : ∀ (n : ℕ) (y : Om l), y ^ l ^ n = 1 → g y = y) (k : ℕ) :
    ϖ.kummer (g ^ k) = ϖ.kummer g ^ k :=
  Perfection.ext fun n => by
    have h1 := PiSys.coeff_kummer ϖ (g ^ k) n
    rw [ratio_pow ϖ g h0 hroot, map_pow, ← PiSys.coeff_kummer, ← map_pow] at h1
    exact h1

theorem untilt_root_kummer (ϖ : PiSys l e) (g : GQ l) (j : ℕ) :
    ((frobeniusEquiv (OCb l) l).symm^[j] (ϖ.kummer g)).untilt = ϖ.ratio g j := by
  refine Perfection.teichmuller_spec (I := Ideal.span {((l : ℕ) : OC l)}) fun n => ⟨ϖ.ratio g (n + j), ?_, ?_⟩
  · rw [← PreTilt.coeff_def, PreTilt.coeff_iterate_frobeniusEquiv_symm, PiSys.coeff_kummer]
  · have : ϖ.ratio g (n + j) ^ l ^ n = ϖ.ratio g j := by
      clear * -
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', pow_mul, show n + 1 + j = (n + j) + 1 by omega, PiSys.ratio_succ, ih]
    rw [this]

theorem ratio_eq_one_iff (ϖ : PiSys l e) (g : GQ l) (j : ℕ) : ϖ.ratio g j = 1 ↔ g (ϖ.seq j) = ϖ.seq j := by
  constructor
  · intro h
    have h1 := congrArg Subtype.val h
    rw [PiSys.coe_ratio, OneMemClass.coe_one, ← map_one (algebraMap (Om l) ℂ_[l])] at h1
    have h2 := (algebraMap (Om l) ℂ_[l]).injective h1
    rwa [div_eq_one_iff_eq (ϖ.seq_ne_zero j)] at h2
  · intro h
    refine Subtype.ext ?_
    rw [PiSys.coe_ratio, h, div_self (ϖ.seq_ne_zero j), map_one, OneMemClass.coe_one]

theorem tilt_step (ϖ : PiSys l e) (g : GQ l) (h0 : g (ϖ.seq 0) = ϖ.seq 0)
    (hroot : ∀ (n : ℕ) (y : Om l), y ^ l ^ n = 1 → g y = y) (hmove : ∃ n, g (ϖ.seq n) ≠ ϖ.seq n) :
    ∃ (ε : OCb l) (c : ℕ), IsEps ε ∧ c ≠ 0 ∧ ∀ k : ℕ, ϖ.kummer (g ^ k) = ε ^ (c * k) := by
  classical
  set N := Nat.find hmove with hN
  have hNm : g (ϖ.seq N) ≠ ϖ.seq N := Nat.find_spec hmove
  have hN0 : N ≠ 0 := fun h => hNm (by rw [h]; exact h0)
  obtain ⟨s, hs⟩ : ∃ s, N = s + 1 := ⟨N - 1, by omega⟩
  have hfix : g (ϖ.seq s) = ϖ.seq s := by
    by_contra h
    exact Nat.find_min hmove (show s < N by omega) h
  set φ := (frobeniusEquiv (OCb l) l).symm with hφ
  refine ⟨φ^[s] (ϖ.kummer g), l ^ s, ⟨?_, φ^[s + 1] (ϖ.kummer g), ?_, ?_⟩, pow_ne_zero _ hl.out.ne_zero, ?_⟩
  · rw [untilt_root_kummer, ratio_eq_one_iff]; exact hfix
  · rw [Function.iterate_succ_apply', hφ, frobeniusEquiv_symm_pow_p]
  · rw [untilt_root_kummer, Ne, ratio_eq_one_iff, ← hs]; exact hNm
  · intro k
    have hp : ∀ j : ℕ, (φ^[j] (ϖ.kummer g)) ^ l ^ j = ϖ.kummer g := by
      intro j
      induction j with
      | zero => simp
      | succ j ih => rw [pow_succ', pow_mul, Function.iterate_succ_apply', hφ, frobeniusEquiv_symm_pow_p, ih]
    rw [kummer_pow ϖ g h0 hroot, pow_mul, hp]

theorem not_mem_field (a : ℕ) [NeZero a] (ϖ : PiSys l e) (z : Om l) (n : ℕ) (hz : z ^ l ^ n = 1) :
    ϖ.seq 1 * z ∉ (ϖ.field a).1 := by
  intro hmem
  have hz0 : z ≠ 0 := by rintro rfl; simp [zero_pow (pow_pos hl.out.pos n).ne'] at hz
  have hnz : ‖z‖ = 1 := by
    have h := congrArg norm hz
    rw [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (pow_pos hl.out.pos n).ne').1 h
  obtain ⟨j, hj⟩ := GlobalTheory.ValGroupKprime.norm_pow_field l a e ϖ _ hmem (mul_ne_zero (ϖ.seq_ne_zero 1) hz0)
  rw [norm_mul, hnz, mul_one] at hj
  have h1 : ‖ϖ.seq 0‖ ^ e = (l : ℝ)⁻¹ := by
    rw [← norm_pow, ϖ.seq_zero, norm_neg, GlobalTheory.ValGroupKprime.norm_natCast_l]
  have h2 : ‖ϖ.seq 1‖ ^ l = ‖ϖ.seq 0‖ := by rw [← norm_pow, ϖ.seq_succ 0]
  have h3 : ((l : ℝ) ^ j) ^ l = (l : ℝ)⁻¹ := by rw [← hj, ← pow_mul, mul_comm, pow_mul, h2, h1]
  rw [← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_neg_one] at h3
  have h4 := zpow_right_injective₀ (by exact_mod_cast hl.out.pos : (0 : ℝ) < l)
    (by exact_mod_cast hl.out.one_lt.ne' : (l : ℝ) ≠ 1) h3
  have h5 : (l : ℤ) ∣ 1 := ⟨-j, by linear_combination h4⟩
  exact hl.out.not_dvd_one (Int.natCast_dvd_natCast.1 (by simpa using h5))

theorem seq_add_pow (ϖ : PiSys l e) (n k : ℕ) : ϖ.seq (n + k) ^ l ^ k = ϖ.seq n := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_mul, show n + (k + 1) = (n + k) + 1 by omega, ϖ.seq_succ, ih]

theorem fixed_twist (ϖ : PiSys l e) (H : Subgroup (GQ l))
    (h0 : ∀ σ ∈ H, σ (ϖ.seq 0) = ϖ.seq 0)
    (hcomm : ∀ σ ∈ H, ∀ τ ∈ H, ∀ n : ℕ, σ (τ (ϖ.seq n)) = τ (σ (ϖ.seq n)))
    (hfix : ∀ σ ∈ H, (∀ (n : ℕ) (y : Om l), y ^ l ^ n = 1 → σ y = y) → ∀ n : ℕ, σ (ϖ.seq n) = ϖ.seq n) :
    ∃ (z : Om l) (n : ℕ), z ^ l ^ n = 1 ∧ ∀ σ ∈ H, σ (ϖ.seq 1 * z) = ϖ.seq 1 * z := by
  classical
  by_cases hA : ∀ σ ∈ H, ∀ (n : ℕ) (y : Om l), y ^ l ^ n = 1 → σ y = y
  · exact ⟨1, 0, by simp, fun σ hσ => by rw [mul_one]; exact hfix σ hσ (hA σ hσ) 1⟩
  have hex : ∃ N : ℕ, ∃ σ ∈ H, ∃ y : Om l, y ^ l ^ N = 1 ∧ σ y ≠ y := by
    push_neg at hA
    obtain ⟨σ, hσ, n, y, hy, hne⟩ := hA
    exact ⟨n, σ, hσ, y, hy, hne⟩
  set N := Nat.find hex with hN
  obtain ⟨τ₀, hτ₀, y₀, hy₀, hne₀⟩ : ∃ σ ∈ H, ∃ y : Om l, y ^ l ^ N = 1 ∧ σ y ≠ y := Nat.find_spec hex
  have hN0 : N ≠ 0 := by
    intro h
    rw [h, pow_zero, pow_one] at hy₀
    rw [hy₀, map_one] at hne₀
    exact hne₀ rfl
  obtain ⟨s, hs⟩ : ∃ s, N = s + 1 := ⟨N - 1, by omega⟩
  have hP : ∀ σ ∈ H, ∀ y : Om l, y ^ l ^ s = 1 → σ y = y := by
    intro σ hσ y hy
    by_contra h
    exact Nat.find_min hex (show s < N by omega) ⟨σ, hσ, y, hy, h⟩
  have hlN : 0 < l ^ N := pow_pos hl.out.pos N
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ N)
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hlN.ne'
  have hpowζ : ∀ y : Om l, y ^ l ^ N = 1 → ∃ i : ℕ, ζ ^ i = y := fun y hy =>
    (hζ.eq_pow_of_pow_eq_one hy).imp fun _ h => h.2
  have heq : ∀ a b : ℤ, ζ ^ a = ζ ^ b ↔ ((l : ℤ) ^ N) ∣ a - b := by
    intro a b
    constructor
    · intro h
      have := (hζ.zpow_eq_one_iff_dvd (a - b)).1 (by rw [zpow_sub₀ hζ0, h, div_self (zpow_ne_zero _ hζ0)])
      simpa using this
    · intro h
      have := (hζ.zpow_eq_one_iff_dvd (a - b)).2 (by simpa using h)
      rwa [zpow_sub₀ hζ0, div_eq_one_iff_eq (zpow_ne_zero _ hζ0)] at this
  have hχ : ∀ σ : GQ l, ∃ c : ℕ, σ ζ = ζ ^ c := fun σ => by
    obtain ⟨i, hi⟩ := hpowζ (σ ζ) (by rw [← map_pow, hζ.pow_eq_one, map_one])
    exact ⟨i, hi.symm⟩
  choose χ hχ using hχ
  have hα : ∀ σ : GQ l, σ ∈ H → ∃ c : ℕ, σ (ϖ.seq N) = ζ ^ c * ϖ.seq N := fun σ hσ => by
    obtain ⟨i, hi⟩ := hpowζ (σ (ϖ.seq N) / ϖ.seq N) (by
      rw [div_pow, ← map_pow, ϖ.seq_pow, h0 σ hσ, div_self (ϖ.seq_ne_zero 0)])
    exact ⟨i, by rw [hi, div_mul_cancel₀ _ (ϖ.seq_ne_zero N)]⟩
  choose α hα using hα
  have hσn : ∀ σ : GQ l, ∀ n : ℕ, σ (ζ ^ n) = ζ ^ (χ σ * n) := fun σ n => by
    rw [map_pow, hχ, ← pow_mul]
  have hσz : ∀ σ : GQ l, ∀ c : ℤ, σ (ζ ^ c) = ζ ^ ((χ σ : ℤ) * c) := fun σ c => by
    rw [map_zpow₀, hχ, _root_.zpow_mul, zpow_natCast]
  have hrel : ∀ σ (hσ : σ ∈ H) τ (hτ : τ ∈ H),
      ((l : ℤ) ^ N) ∣ ((χ σ : ℤ) * α τ hτ + α σ hσ) - ((χ τ : ℤ) * α σ hσ + α τ hτ) := by
    intro σ hσ τ hτ
    have h := hcomm σ hσ τ hτ N
    simp only [hα _ hσ, hα _ hτ, map_mul, hσn] at h
    have h' : ζ ^ (χ σ * α τ hτ + α σ hσ) = ζ ^ (χ τ * α σ hσ + α τ hτ) := by
      rw [pow_add, pow_add]
      apply mul_right_cancel₀ (ϖ.seq_ne_zero N)
      rw [mul_assoc, h, mul_assoc]
    have := (heq ((χ σ * α τ hτ + α σ hσ : ℕ) : ℤ) ((χ τ * α σ hσ + α τ hτ : ℕ) : ℤ)).1
      (by rw [zpow_natCast, zpow_natCast]; exact h')
    push_cast at this
    exact this
  have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  have hχs : ∀ σ ∈ H, ((l : ℤ) ^ s) ∣ (χ σ : ℤ) - 1 := by
    intro σ hσ
    have h1 : σ (ζ ^ l) = ζ ^ l := hP σ hσ _ (by rw [← pow_mul, ← pow_succ', ← hs, hζ.pow_eq_one])
    rw [hσn] at h1
    have h2 := (heq ((χ σ * l : ℕ) : ℤ) ((l : ℕ) : ℤ)).1 (by rw [zpow_natCast, zpow_natCast]; exact h1)
    rw [hs, pow_succ'] at h2
    push_cast at h2
    have h3 : (l : ℤ) * (l : ℤ) ^ s ∣ (l : ℤ) * ((χ σ : ℤ) - 1) := by
      convert h2 using 1
      ring
    exact (mul_dvd_mul_iff_left hl0).1 h3
  have hτζ : ¬ ((l : ℤ) ^ N) ∣ (χ τ₀ : ℤ) - 1 := by
    intro h
    have h1 : τ₀ ζ = ζ := by
      rw [hχ]
      have := (heq (χ τ₀ : ℤ) 1).2 h
      rwa [zpow_natCast, zpow_one] at this
    obtain ⟨i, rfl⟩ := hpowζ y₀ hy₀
    exact hne₀ (by rw [map_pow, h1])
  obtain ⟨u, hu⟩ := hχs τ₀ hτ₀
  have hlu : ¬ (l : ℤ) ∣ u := by
    rintro ⟨v, rfl⟩
    exact hτζ ⟨v, by rw [hu, hs, pow_succ]; ring⟩
  have hpz : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl.out
  obtain ⟨a', b', hab⟩ := (Irreducible.coprime_iff_not_dvd hpz.irreducible).2 hlu
  set A₀ : ℤ := (α τ₀ hτ₀ : ℤ) with hA₀
  refine ⟨ζ ^ (-(b' * A₀)), N, ?_, fun σ hσ => ?_⟩
  · rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hζ.pow_eq_one, _root_.one_zpow]
  · obtain ⟨w, hw⟩ := hχs σ hσ
    have hr := hrel σ hσ τ₀ hτ₀
    have h1 : (l : ℤ) ∣ w * A₀ - u * α σ hσ := by
      have h3 : (l : ℤ) ^ s * (l : ℤ) ∣ (l : ℤ) ^ s * (w * A₀ - u * α σ hσ) := by
        rw [← pow_succ, ← hs]
        convert hr using 1
        linear_combination (-A₀) * hw + ((α σ hσ : ℕ) : ℤ) * hu
      exact (mul_dvd_mul_iff_left (pow_ne_zero _ hl0)).1 h3
    obtain ⟨q, hq⟩ := h1
    have hseq : ϖ.seq N ^ l ^ s = ϖ.seq 1 := by rw [hs, add_comm]; exact seq_add_pow ϖ 1 s
    have hσ1 : σ (ϖ.seq 1) = ζ ^ ((α σ hσ : ℤ) * (l : ℤ) ^ s) * ϖ.seq 1 := by
      have hc : ((α σ hσ * l ^ s : ℕ) : ℤ) = (α σ hσ : ℤ) * (l : ℤ) ^ s := by push_cast; ring
      rw [← hseq, map_pow, hα σ hσ, mul_pow, ← pow_mul, ← hc, zpow_natCast]
    have h2 : ζ ^ ((α σ hσ : ℤ) * (l : ℤ) ^ s + (χ σ : ℤ) * (-(b' * A₀))) = ζ ^ (-(b' * A₀)) := by
      rw [heq, hs, pow_succ]
      exact ⟨a' * α σ hσ - b' * q, by
        linear_combination (-b' * A₀) * hw + (-((l : ℤ) ^ s) * α σ hσ) * hab + (-((l : ℤ) ^ s) * b') * hq⟩
    rw [map_mul, hσ1, hσz, ← h2, zpow_add₀ hζ0]
    ring

theorem exists_move (a : ℕ) [NeZero a] (ϖ : PiSys l e) :
    ∃ g : GQ l, g ∈ GK (ϖ.field a) ∧ (∀ (n : ℕ) (y : Om l), y ^ l ^ n = 1 → g y = y) ∧
      ∃ n, g (ϖ.seq n) ≠ ϖ.seq n := by
  by_contra hno
  push_neg at hno
  have h0 : ∀ σ ∈ GK (ϖ.field a), σ (ϖ.seq 0) = ϖ.seq 0 := fun σ hσ => ϖ.gal_pi a ⟨σ, hσ⟩
  have hcomm : ∀ σ ∈ GK (ϖ.field a), ∀ τ ∈ GK (ϖ.field a), ∀ n : ℕ, σ (τ (ϖ.seq n)) = τ (σ (ϖ.seq n)) := by
    intro σ hσ τ hτ n
    have hg : (σ * τ)⁻¹ * (τ * σ) ∈ GK (ϖ.field a) := mul_mem (inv_mem (mul_mem hσ hτ)) (mul_mem hτ hσ)
    have hgr : ∀ (m : ℕ) (y : Om l), y ^ l ^ m = 1 → ((σ * τ)⁻¹ * (τ * σ)) y = y := by
      intro m y hy
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply τ σ, ← comm_root σ τ m y hy, ← AlgEquiv.mul_apply σ τ,
        ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    have h1 := congrArg (σ * τ) (hno _ hg hgr n)
    rw [← AlgEquiv.mul_apply, mul_inv_cancel_left] at h1
    simpa [AlgEquiv.mul_apply] using h1.symm
  obtain ⟨z, n, hz, hfix⟩ := fixed_twist ϖ (GK (ϖ.field a)) h0 hcomm hno
  exact not_mem_field a ϖ z n hz (by
    rw [← InfiniteGalois.fixedField_fixingSubgroup (ϖ.field a).1]
    exact (IntermediateField.mem_fixedField_iff _ _).2 fun σ hσ => hfix σ hσ)

end

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e), l ≠ 2 →
    ∃ (g : Gl l) (ε : OCb l) (c : ℕ), IsEps ε ∧ c ≠ 0 ∧ sQ l g ∈ GK (ϖ.field a) ∧
      ∀ k : ℕ, ϖ.kummer (sQ l (g ^ k)) = ε ^ (c * k) := by
  intro l _ a e _ _ ϖ _
  obtain ⟨g, hgK, hroot, hmove⟩ := exists_move a ϖ
  obtain ⟨ε, c, hε, hc, hk⟩ := tilt_step ϖ g (ϖ.gal_pi a ⟨g, hgK⟩) hroot hmove
  refine ⟨⟨g, GK_le (K := Formalism.MainNotions.ElementDenominator.qlExt l) (K' := ϖ.field a) bot_le hgK⟩, ε, c, hε, hc, hgK, fun k => ?_⟩
  rw [map_pow]
  exact hk k

end GlobalTheory.KummerMove
