import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Acris0TorsionFree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorGaussNormUltrametricStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorGaussNormMulStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltNormUltrametricEqZeroStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

noncomputable section
namespace GlobalTheory.GaussExt
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc Filter Topology
open scoped Formalism.Per

theorem exists_ext_loc {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (M : Submonoid R)
    [IsLocalization M S] (N : R → ℝ) (h0 : ∀ x, 0 ≤ N x)
    (hadd : ∀ x y, N (x + y) ≤ max (N x) (N y)) (hneg : ∀ x, N (-x) = N x)
    (hmul : ∀ x y, N (x * y) = N x * N y) (hM : ∀ m ∈ M, N m ≠ 0) :
    ∃ N' : S → ℝ, (∀ x, 0 ≤ N' x) ∧ (∀ x y, N' (x + y) ≤ max (N' x) (N' y)) ∧ (∀ x, N' (-x) = N' x) ∧
      (∀ x y, N' (x * y) = N' x * N' y) ∧ ∀ a, N' (algebraMap R S a) = N a := by
  have hpos : ∀ m : M, 0 < N m := fun m => lt_of_le_of_ne (h0 _) (hM m m.2).symm
  have hinj : ∀ a b : R, algebraMap R S a = algebraMap R S b → N a = N b := by
    intro a b h
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists M S).1 h
    have := congrArg N hc
    rw [hmul, hmul] at this
    exact mul_left_cancel₀ (hpos c).ne' this
  let N' : S → ℝ := fun z => N (IsLocalization.sec M z).1 / N (IsLocalization.sec M z).2
  have key : ∀ (z : S) (a : R) (b : M), z * algebraMap R S b = algebraMap R S a → N' z = N a / N b := by
    intro z a b h
    have h1 := IsLocalization.sec_spec M z
    have h2 : algebraMap R S ((IsLocalization.sec M z).1 * b) =
        algebraMap R S (a * (IsLocalization.sec M z).2) := by
      rw [map_mul, map_mul, ← h1, ← h]; ring
    have h3 := hinj _ _ h2
    rw [hmul, hmul] at h3
    simp only [N']
    rw [div_eq_div_iff (hpos _).ne' (hpos _).ne', h3]
  refine ⟨N', fun x => div_nonneg (h0 _) (h0 _), fun x y => ?_, fun x => ?_, fun x y => ?_, fun a => ?_⟩
  · obtain ⟨⟨a, b⟩, hx⟩ := IsLocalization.surj M x
    obtain ⟨⟨c, d⟩, hy⟩ := IsLocalization.surj M y
    simp only at hx hy
    rw [key x (a * d) (b * d) (by simp only [Submonoid.coe_mul, map_mul, ← hx]; ring),
      key y (c * b) (b * d) (by simp only [Submonoid.coe_mul, map_mul, ← hy]; ring),
      key (x + y) (a * d + c * b) (b * d)
        (by simp only [Submonoid.coe_mul, map_mul, map_add, ← hx, ← hy]; ring),
      max_div_div_right (h0 _)]
    exact div_le_div_of_nonneg_right (hadd _ _) (h0 _)
  · obtain ⟨⟨a, b⟩, hx⟩ := IsLocalization.surj M x
    simp only at hx
    rw [key x a b hx, key (-x) (-a) b (by rw [map_neg, ← hx]; ring), hneg]
  · obtain ⟨⟨a, b⟩, hx⟩ := IsLocalization.surj M x
    obtain ⟨⟨c, d⟩, hy⟩ := IsLocalization.surj M y
    simp only at hx hy
    rw [key x a b hx, key y c d hy, key (x * y) (a * c) (b * d)
        (by simp only [Submonoid.coe_mul, map_mul, ← hx, ← hy]; ring), Submonoid.coe_mul, hmul, hmul,
      mul_div_mul_comm]
  · have h1 : N 1 = 1 := by
      have := hmul 1 1
      rw [mul_one] at this
      exact (mul_left_cancel₀ (hM 1 M.one_mem) (by rw [mul_one]; exact this)).symm
    rw [key _ a 1 (by simp), Submonoid.coe_one, h1, div_one]

theorem exists_ext_compl {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (p : ℕ) (N : A → ℝ)
    (h0 : ∀ x, 0 ≤ N x ∧ N x ≤ 1)
    (hadd : ∀ x y, N (x + y) ≤ max (N x) (N y)) (hneg : ∀ x, N (-x) = N x)
    (hmul : ∀ x y, N (x * y) = N x * N y) (hp : N p < 1)
    (hd : ∀ (x : B) (k : ℕ), ∃ (s : A) (z : B), x = f s + (p : B) ^ k * z)
    (hr : ∀ (s : A) (k : ℕ), (p : B) ^ k ∣ f s → (p : A) ^ k ∣ s) :
    ∃ N' : B → ℝ, (∀ x, 0 ≤ N' x ∧ N' x ≤ 1) ∧ (∀ x y, N' (x + y) ≤ max (N' x) (N' y)) ∧
      (∀ x, N' (-x) = N' x) ∧ (∀ x y, N' (x * y) = N' x * N' y) ∧ ∀ a, N' (f a) = N a := by
  have hpow : ∀ (k : ℕ) (z : A), N ((p : A) ^ k * z) ≤ N p ^ k := by
    intro k
    induction k with
    | zero => intro z; simpa using (h0 z).2
    | succ k ih =>
      intro z
      rw [pow_succ', mul_assoc, hmul, pow_succ']
      exact mul_le_mul_of_nonneg_left (ih z) (h0 _).1
  have hle : ∀ (k : ℕ) (s t : A), (p : B) ^ k ∣ f s - f t → N s ≤ N t + N p ^ k := by
    intro k s t h
    rw [← map_sub] at h
    obtain ⟨z, hz⟩ := hr _ _ h
    have h1 : s = t + (p : A) ^ k * z := by rw [← hz]; ring
    have h2 := hadd t ((p : A) ^ k * z)
    rw [← h1] at h2
    have h3 := hpow k z
    have h4 := (h0 t).1
    have h5 := pow_nonneg (h0 p).1 k
    exact h2.trans (max_le (by linarith) (by linarith))
  have hdist : ∀ (k : ℕ) (s t : A), (p : B) ^ k ∣ f s - f t → dist (N s) (N t) ≤ N p ^ k := by
    intro k s t h
    have h1 := hle k s t h
    have h2 := hle k t s (by rw [← neg_sub]; exact h.neg_right)
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith
  have hlim : Tendsto (fun k : ℕ => N p ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (h0 _).1 hp
  have hs : ∀ x : B, ∃ s : ℕ → A, ∀ k, (p : B) ^ k ∣ x - f (s k) := by
    intro x
    choose s z h using hd x
    exact ⟨s, fun k => ⟨z k, by rw [sub_eq_iff_eq_add', ← h k]⟩⟩
  have hex : ∀ x : B, ∃ t : ℝ, ∀ s : ℕ → A, (∀ k, (p : B) ^ k ∣ x - f (s k)) →
      Tendsto (fun k => N (s k)) atTop (𝓝 t) := by
    intro x
    obtain ⟨s, hs⟩ := hs x
    have hc : CauchySeq fun k => N (s k) :=
      cauchySeq_of_le_tendsto_0' (fun k => N p ^ k) (fun n m h => hdist n _ _ (by
        have := ((pow_dvd_pow _ h).trans (hs m)).sub (hs n)
        convert this using 1; ring)) hlim
    obtain ⟨t, ht⟩ := cauchySeq_tendsto_of_complete hc
    refine ⟨t, fun s' hs' => ht.congr_dist (squeeze_zero (fun _ => dist_nonneg) (fun k => hdist k _ _ ?_) hlim)⟩
    have := (hs' k).sub (hs k)
    convert this using 1; ring
  choose N' hN' using hex
  refine ⟨N', fun x => ?_, fun x y => ?_, fun x => ?_, fun x y => ?_, fun a => ?_⟩
  · obtain ⟨s, hs⟩ := hs x
    exact ⟨ge_of_tendsto' (hN' x s hs) fun k => (h0 _).1, le_of_tendsto' (hN' x s hs) fun k => (h0 _).2⟩
  · obtain ⟨s, hx⟩ := hs x
    obtain ⟨t, hy⟩ := hs y
    refine le_of_tendsto_of_tendsto' (hN' (x + y) (fun k => s k + t k) fun k => ?_)
      ((hN' x s hx).max (hN' y t hy)) fun k => hadd _ _
    have := (hx k).add (hy k)
    convert this using 1; rw [map_add]; ring
  · obtain ⟨s, hx⟩ := hs x
    refine tendsto_nhds_unique (hN' (-x) (fun k => -s k) fun k => ?_) (by simpa only [hneg] using hN' x s hx)
    have := (hx k).neg_right
    convert this using 1; rw [map_neg]; ring
  · obtain ⟨s, hx⟩ := hs x
    obtain ⟨t, hy⟩ := hs y
    refine tendsto_nhds_unique (hN' (x * y) (fun k => s k * t k) fun k => ?_)
      (by simpa only [hmul] using (hN' x s hx).mul (hN' y t hy))
    have := ((hx k).mul_right y).add ((hy k).mul_left (f (s k)))
    convert this using 1; rw [map_mul]; ring
  · exact tendsto_nhds_unique (hN' (f a) (fun _ => a) fun k => by simp) tendsto_const_nhds

theorem pow_le_factorial {R : Type} [CommRing R] (p : ℕ) [Fact p.Prime] (N : R → ℝ)
    (h0 : ∀ x, 0 ≤ N x ∧ N x ≤ 1) (h1 : N 1 = 1)
    (hadd : ∀ x y, N (x + y) ≤ max (N x) (N y))
    (hmul : ∀ x y, N (x * y) = N x * N y) (hp : N p < 1) (n : ℕ) :
    N p ^ n ≤ N (n.factorial : R) := by
  have hpow : ∀ k : ℕ, N ((p : R) ^ k) = N p ^ k := by
    intro k
    induction k with
    | zero => simpa using h1
    | succ k ih => rw [pow_succ, hmul, ih, pow_succ]
  have hcop : ∀ m : ℕ, ¬ p ∣ m → 1 ≤ N m := by
    intro m hm
    have hc : IsCoprime (p : R) (m : R) :=
      Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hm)
    obtain ⟨a, b, hab⟩ := hc
    have h2 := hadd (a * p) (b * m)
    rw [hab, h1, hmul, hmul] at h2
    rcases le_max_iff.1 h2 with h | h
    · nlinarith [h0 a, h0 p]
    · nlinarith [h0 b, h0 m]
  obtain ⟨e, m, hm, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd n.factorial_ne_zero p
    (Fact.out : p.Prime).ne_one
  have hen : e ≤ n := by
    have h2 : e ≤ padicValNat p n.factorial :=
      (padicValNat_dvd_iff_le n.factorial_ne_zero).1 ⟨m, he⟩
    have h3 := sub_one_mul_padicValNat_factorial (p := p) n
    have h4 : 1 ≤ p - 1 := by have := (Fact.out : p.Prime).two_le; omega
    have h5 := Nat.mul_le_mul_right (padicValNat p n.factorial) h4
    omega
  rw [he, Nat.cast_mul, Nat.cast_pow, hmul, hpow]
  exact (pow_le_pow_of_le_one (h0 _).1 (h0 _).2 hen).trans
    (le_mul_of_one_le_right (pow_nonneg (h0 _).1 _) (hcop m hm))

variable {l : ℕ} [Fact l.Prime]

theorem untilt_zero : (0 : Per.Fl l).untilt = 0 := by
  rw [← WittVector.fontaineTheta_teichmuller, WittVector.teichmuller_zero, map_zero]

theorem norm_l : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  rw [GlobalTheory.RingBasics.norm_eq_val, PadicComplex.valuation_p]
  simp

theorem norm_coeff_zero_le (x : Per.Ainf l) (hx : Per.θ l x = 0) :
    ‖(((x.coeff 0).untilt : Per.OC l) : ℂ_[l])‖ ≤ (l : ℝ)⁻¹ := by
  have h := WittVector.mk_fontaineTheta x
  rw [← PreTilt.mk_untilt_eq_coeff_zero, show WittVector.fontaineTheta (Per.OC l) l x = 0 from hx,
    map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem, ← pow_one (Ideal.span _),
    GlobalTheory.RingBasics.mem_span_pow_OC, pow_one, norm_l] at h
  exact h

theorem exists_gauss_acris (l : ℕ) [Fact l.Prime] (r : ℝ) (hr : (l : ℝ)⁻¹ ≤ r) (hr1 : r < 1) :
    ∃ N : Per.Acris l → ℝ, (∀ x, 0 ≤ N x ∧ N x ≤ 1) ∧ (∀ x y, N (x + y) ≤ max (N x) (N y)) ∧
      (∀ x, N (-x) = N x) ∧ (∀ x y, N (x * y) = N x * N y) ∧
      ∀ a : Per.Ainf l, N (algebraMap (Per.Ainf l) (Per.Acris l) a) =
        ⨆ n : ℕ, ‖(((a.coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n := by
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hr0 : 0 < r := (inv_pos.2 hl).trans_le hr
  let a : Per.Fl l → ℝ := fun x => ‖((x.untilt : Per.OC l) : ℂ_[l])‖
  have a01 : ∀ x, 0 ≤ a x ∧ a x ≤ 1 := fun x => ⟨norm_nonneg _, (GlobalTheory.RingBasics.mem_OC _).1 (x.untilt).2⟩
  have a0 : a 0 = 0 := by simp only [a, untilt_zero]; simp
  have a1 : a 1 = 1 := by simp [a]
  have amul : ∀ x y, a (x * y) = a x * a y := by intro x y; simp [a]
  have aadd : ∀ x y, a (x + y) ≤ max (a x) (a y) := fun x y => (GlobalTheory.T.untilt_norm_ultrametric_eq_zero l x y).1
  obtain ⟨N, hN⟩ : ∃ N : Per.Ainf l → ℝ,
      ∀ x, N x = ⨆ n : ℕ, a (x.coeff n) ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n := ⟨_, fun _ => rfl⟩
  obtain ⟨Nadd, Nneg, -⟩ := GlobalTheory.T.witt_vector_gauss_norm_ultrametric l (Per.Fl l) a a01 a0 a1 amul aadd r hr0 hr1 N hN
  have Nmul := GlobalTheory.T.wittVector_gaussNorm_mul l (Per.Fl l) a a01 a0 a1 amul aadd r hr0 hr1 N hN
  have he : ∀ n : ℕ, (0 : ℝ) < 1 / (l : ℝ) ^ n := fun n => by positivity
  have ht0 : ∀ (y : Per.Fl l) (n : ℕ), 0 ≤ a y ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n := fun y n =>
    mul_nonneg (Real.rpow_nonneg (a01 y).1 _) (pow_nonneg hr0.le _)
  have ht1 : ∀ (y : Per.Fl l) (n : ℕ), a y ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n ≤ r ^ n := fun y n =>
    mul_le_of_le_one_left (pow_nonneg hr0.le _) (Real.rpow_le_one (a01 y).1 (a01 y).2 (he n).le)
  have rank_lt_alt : ∀ x, 0 ≤ N x ∧ N x ≤ 1 := fun x => by
    rw [hN]
    exact ⟨Real.iSup_nonneg fun n => ht0 _ n,
      ciSup_le fun n => (ht1 _ n).trans (pow_le_one₀ hr0.le hr1.le)⟩
  have Nker : ∀ x, Per.θ l x = 0 → N x ≤ r := fun x hx => by
    rw [hN]
    refine ciSup_le fun n => ?_
    rcases n with _ | n
    · simpa using (norm_coeff_zero_le x hx).trans hr
    · exact (ht1 _ _).trans (pow_le_of_le_one hr0.le hr1.le n.succ_ne_zero)
  have Nl : N (l : Per.Ainf l) = r := by
    rw [hN]
    have hterm : ∀ n : ℕ, a ((l : Per.Ainf l).coeff n) ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n =
        if n = 1 then r else 0 := by
      intro n
      rw [WittVector.coeff_p]
      split_ifs with h
      · rw [a1, h, Real.one_rpow, one_mul, pow_one]
      · rw [a0, Real.zero_rpow (he n).ne', zero_mul]
    simp only [hterm]
    refine le_antisymm (ciSup_le fun n => by split_ifs; exacts [le_rfl, hr0.le]) ?_
    refine le_ciSup_of_le ⟨r, ?_⟩ 1 (by simp)
    rintro _ ⟨n, rfl⟩
    dsimp only
    split_ifs
    exacts [le_rfl, hr0.le]
  have N1 : N 1 = 1 := by
    have := Nmul l 1
    rw [mul_one, Nl] at this
    exact (mul_left_cancel₀ hr0.ne' (by rw [mul_one]; exact this)).symm
  have Npow : ∀ (x : Per.Ainf l) (k : ℕ), N (x ^ k) = N x ^ k := by
    intro x k
    induction k with
    | zero => simpa using N1
    | succ k ih => rw [pow_succ, Nmul, ih, pow_succ]
  obtain ⟨M, M0, Madd, Mneg, Mmul, MN⟩ := exists_ext_loc (S := Per.AinfP l)
    (Submonoid.powers (l : Per.Ainf l)) N (fun x => (rank_lt_alt x).1) Nadd Nneg Nmul (by
      rintro _ ⟨k, rfl⟩
      dsimp only
      rw [Npow, Nl]
      exact pow_ne_zero _ hr0.ne')
  have M1 : ∀ s ∈ Per.Acris0 l, M s ≤ 1 := by
    let B : Subalgebra (Per.Ainf l) (Per.AinfP l) :=
      { carrier := {s | M s ≤ 1}
        mul_mem' := fun {x y} hx hy => by
          have hx' : M x ≤ 1 := hx
          have hy' : M y ≤ 1 := hy
          have : M (x * y) ≤ 1 := by rw [Mmul]; exact mul_le_one₀ hx' (M0 y) hy'
          exact this
        add_mem' := fun {x y} hx hy => by
          have hx' : M x ≤ 1 := hx
          have hy' : M y ≤ 1 := hy
          exact (Madd x y).trans (max_le hx' hy')
        algebraMap_mem' := fun y => by
          have : M (algebraMap (Per.Ainf l) (Per.AinfP l) y) ≤ 1 := by rw [MN]; exact (rank_lt_alt y).2
          exact this }
    have hB : Per.Acris0 l ≤ B := by
      refine GlobalTheory.RingIface.Acris0_le_of_dividedPowers l B fun x n y hx h => ?_
      have h1 := congrArg M h
      rw [Mmul, ← map_natCast (algebraMap (Per.Ainf l) (Per.AinfP l)), ← map_pow, MN, MN, Npow] at h1
      have h2 := pow_le_factorial l N rank_lt_alt N1 Nadd Nmul (by rw [Nl]; exact hr1) n
      rw [Nl] at h2
      have h3 : N x ^ n ≤ r ^ n := pow_le_pow_left₀ (rank_lt_alt x).1 (Nker x hx) n
      have h4 : 0 < r ^ n := pow_pos hr0 n
      have h6 : M y ≤ 1 := by
        by_contra h5
        push Not at h5
        nlinarith
      exact h6
    exact fun s hs => hB hs
  obtain ⟨-, -, hd, hv⟩ := acris_basic l
  obtain ⟨Q, Q01, Qadd, Qneg, Qmul, QM⟩ := exists_ext_compl
    (algebraMap (Per.Acris0 l) (Per.Acris l)) l (fun s : Per.Acris0 l => M (s : Per.AinfP l))
    (fun s => ⟨M0 _, M1 _ s.2⟩) (fun x y => Madd _ _) (fun x => Mneg _) (fun x y => Mmul _ _)
    (by
      have : ((l : Per.Acris0 l) : Per.AinfP l) = algebraMap (Per.Ainf l) (Per.AinfP l) l := by simp
      rw [this, MN, Nl]
      exact hr1) hd (fun s k => (hv s k).1)
  refine ⟨Q, Q01, Qadd, Qneg, Qmul, fun x => ?_⟩
  have h : algebraMap (Per.Ainf l) (Per.Acris l) x =
      algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) x) :=
    GlobalTheory.RingIface.tower l x
  rw [h, QM, Subalgebra.coe_algebraMap, MN, hN]

end GlobalTheory.GaussExt
