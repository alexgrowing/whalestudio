import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EchEqOneIff
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SummableNormSiegelThetaSeriesTerms
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SymplecticSiegelActionMemUpperHalfSpaceAndCocyclStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SchwartzBruhatIntegralEqSumResidueRepresentativeStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TsumSchwartzBruhatLevelEqSumResidueCosetsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PoissonSummationThetaSeriesRowTermCosetStatement

open Matrix Complex GlobalTheory.SW GlobalTheory.SW.FourierJ
open scoped ComplexConjugate Real

namespace GlobalTheory.SW.FourierJ

noncomputable section

theorem prodsum_fin (α : Type) (n : ℕ) (f : Fin n → α → ℂ) (hf : ∀ k, Summable fun a => ‖f k a‖) :
    (Summable fun m : Fin n → α => ‖∏ k, f k (m k)‖) ∧
      ∑' m : Fin n → α, ∏ k, f k (m k) = ∏ k, ∑' a, f k a := by
  induction n with
  | zero => exact ⟨Summable.of_finite, by simp⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih (fun k => f k.succ) fun k => hf _
    have e : ∀ q : α × (Fin n → α), ∏ k, f k ((Fin.consEquiv fun _ => α) q k) =
        f 0 q.1 * ∏ k : Fin n, f k.succ (q.2 k) := by
      intro q; rw [Fin.prod_univ_succ]; rfl
    constructor
    · rw [← (Fin.consEquiv fun _ : Fin (n + 1) => α).summable_iff]
      have := (hf 0).mul_norm h1
      simpa only [Function.comp_def, e] using this
    · rw [← (Fin.consEquiv fun _ : Fin (n + 1) => α).tsum_eq, Fin.prod_univ_succ, ← h2,
        tsum_mul_tsum_of_summable_norm (hf 0) h1]
      simp only [e]

theorem tsum_pi_prod : ∀ (κ α : Type) [Fintype κ] (f : κ → α → ℂ), (∀ k, Summable fun a => ‖f k a‖) → (Summable fun m : κ → α => ‖∏ k, f k (m k)‖) ∧ ∑' m : κ → α, ∏ k, f k (m k) = ∏ k, ∑' a, f k a := by
  intro κ α _ f hf
  set e := (Fintype.equivFin κ).symm
  obtain ⟨h1, h2⟩ := prodsum_fin α _ (fun k => f (e k)) fun k => hf _
  have h : ∀ m : Fin (Fintype.card κ) → α, ∏ k, f k ((e.arrowCongr (Equiv.refl α)) m k) =
      ∏ k, f (e k) (m k) := by
    intro m; rw [← e.prod_comp]; simp
  constructor
  · rw [← (e.arrowCongr (Equiv.refl α)).summable_iff]
    simpa only [Function.comp_def, h] using h1
  · rw [← (e.arrowCongr (Equiv.refl α)).tsum_eq, ← e.prod_comp, ← h2]
    simp only [h]

theorem orth_one {R : ℕ} (hR : 0 < R) (a b : Fin (R * R)) :
    ∑ n : Fin (R * R), ech ((((a : ℕ) : ℚ) / R - ((b : ℕ) : ℚ) / R) * (((n : ℕ) : ℚ) / R)) =
      if a = b then (R : ℂ) ^ 2 else 0 := by
  have hR0 : (R : ℚ) ≠ 0 := by exact_mod_cast hR.ne'
  split_ifs with h
  · simp [h, ech_zero, sq]
  · set t : ℚ := (((a : ℕ) : ℚ) - (b : ℕ)) / (R * R) with ht
    have hpow : ∀ n : ℕ, ech (t * n) = ech t ^ n := by
      intro n; simp only [ech, ← Complex.exp_nat_mul]; push_cast; ring_nf
    have h1 : ∀ n : Fin (R * R), ech ((((a : ℕ) : ℚ) / R - ((b : ℕ) : ℚ) / R) *
        (((n : ℕ) : ℚ) / R)) = ech t ^ (n : ℕ) := by
      intro n; rw [← hpow, ht]; congr 1; field_simp
    have hne : ech t ≠ 1 := by
      intro h1
      obtain ⟨m, hm⟩ := (ech_eq_one_iff _).1 h1
      rw [ht, div_eq_iff (mul_ne_zero hR0 hR0)] at hm
      have hm' : ((a : ℕ) : ℤ) - (b : ℕ) = m * ((R * R : ℕ) : ℤ) := by exact_mod_cast hm
      have ha := a.2
      have hb := b.2
      have : ((a : ℕ) : ℤ) - (b : ℕ) = 0 :=
        Int.eq_zero_of_abs_lt_dvd (m := ((R * R : ℕ) : ℤ)) ⟨m, by rw [hm', mul_comm]⟩
          (by rw [abs_lt]; omega)
      exact h (Fin.ext (by omega))
    have hN : ech t ^ (R * R) = 1 := by
      rw [← hpow]
      exact (ech_eq_one_iff _).2 ⟨((a : ℕ) : ℤ) - (b : ℕ), by rw [ht]; push_cast; field_simp⟩
    simp only [h1]
    rw [Fin.sum_univ_eq_sum_range (fun n => ech t ^ n), geom_sum_eq hne, hN]; simp

theorem sum_ech_rep : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι] (R : ℕ), 0 < R → ∀ a b : κ → ι → Fin (R * R), ∑ n : κ → ι → Fin (R * R), ech (∑ k, (rep R a k - rep R b k) ⬝ᵥ rep R n k) = if a = b then ((R : ℂ) ^ (Fintype.card κ * Fintype.card ι)) ^ 2 else 0 := by
  intro κ ι _ _ _ _ R hR a b
  have h : ∀ n : κ → ι → Fin (R * R), ech (∑ k, (rep R a k - rep R b k) ⬝ᵥ rep R n k) =
      ∏ k, ∏ i, ech ((((a k i : ℕ) : ℚ) / R - ((b k i : ℕ) : ℚ) / R) *
        (((n k i : ℕ) : ℚ) / R)) := by
    intro n; simp only [dotProduct, ech_sum]; rfl
  simp only [h]
  rw [← Fintype.prod_sum (fun k (v : ι → Fin (R * R)) => ∏ i, ech ((((a k i : ℕ) : ℚ) / R -
    ((b k i : ℕ) : ℚ) / R) * (((v i : ℕ) : ℚ) / R)))]
  have h2 : ∀ k, ∑ v : ι → Fin (R * R), ∏ i, ech ((((a k i : ℕ) : ℚ) / R -
      ((b k i : ℕ) : ℚ) / R) * (((v i : ℕ) : ℚ) / R)) =
      ∏ i, if a k i = b k i then (R : ℂ) ^ 2 else 0 := by
    intro k
    rw [← Fintype.prod_sum (fun i (v : Fin (R * R)) => ech ((((a k i : ℕ) : ℚ) / R -
      ((b k i : ℕ) : ℚ) / R) * (((v : ℕ) : ℚ) / R)))]
    simp only [orth_one hR]
  simp only [h2]
  split_ifs with hab
  · simp [hab, ← pow_mul]; ring_nf
  · obtain ⟨k, hk⟩ := Function.ne_iff.1 hab
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hk
    exact Finset.prod_eq_zero (Finset.mem_univ k)
      (Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi))

variable {κ ι : Type} [Fintype κ] [Fintype ι]

def pr (x y : Matrix κ ι ℚ) : ℚ := ∑ k, x k ⬝ᵥ y k

theorem pr_add_left (x x' y : Matrix κ ι ℚ) : pr (x + x') y = pr x y + pr x' y := by
  simp only [pr, ← Finset.sum_add_distrib, ← add_dotProduct]; rfl

theorem pr_sub_left (x x' y : Matrix κ ι ℚ) : pr (x - x') y = pr x y - pr x' y := by
  simp only [pr, ← Finset.sum_sub_distrib, ← sub_dotProduct]; rfl

theorem pr_comm (x y : Matrix κ ι ℚ) : pr x y = pr y x := by
  simp only [pr, dotProduct_comm]

theorem pr_smul_left (t : ℚ) (x y : Matrix κ ι ℚ) : pr (t • x) y = t * pr x y := by
  simp only [pr, dotProduct, Finset.mul_sum, Matrix.smul_apply, smul_eq_mul, mul_assoc]

theorem pr_smul_swap (t : ℚ) (x y : Matrix κ ι ℚ) : pr (t • x) y = pr x (t • y) := by
  rw [pr_smul_left, pr_comm x (t • y), pr_smul_left, pr_comm]

theorem ech_pr_int {x y : Matrix κ ι ℚ} (hx : IntM x) (hy : IntM y) : ech (pr x y) = 1 := by
  obtain ⟨a, rfl⟩ := (intM_iff x).1 hx
  obtain ⟨b, rfl⟩ := (intM_iff y).1 hy
  refine (ech_eq_one_iff _).2 ⟨∑ k, ∑ i, a k i * b k i, ?_⟩
  simp [pr, zm, dotProduct]

theorem intM_nsmul {x : Matrix κ ι ℚ} (hx : IntM x) (S : ℕ) : IntM ((S : ℚ) • x) := by
  obtain ⟨a, rfl⟩ := (intM_iff x).1 hx
  exact (intM_iff _).2 ⟨fun k i => S * a k i, by ext k i; simp [zm]⟩

theorem level_mul {R : ℕ} {φ : Matrix κ ι ℚ → ℂ} (h : HasLevel R φ) (S : ℕ) :
    HasLevel (R * S) φ := by
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · have := intM_nsmul (h.1 x hx) S
    rwa [smul_smul, mul_comm, ← Nat.cast_mul] at this
  · rw [Nat.cast_mul, ← smul_smul]; exact h.2 x _ (intM_nsmul hy S)

theorem exists_den (y : Matrix κ ι ℚ) : ∃ S : ℕ, 0 < S ∧ IntM ((S : ℚ) • y) := by
  classical
  refine ⟨∏ p : κ × ι, (y p.1 p.2).den, Finset.prod_pos fun p _ => (y p.1 p.2).den_pos, ?_⟩
  intro k i
  obtain ⟨d, hd⟩ : (y k i).den ∣ ∏ p : κ × ι, (y p.1 p.2).den :=
    Finset.dvd_prod_of_mem (fun p : κ × ι => (y p.1 p.2).den) (Finset.mem_univ (k, i))
  have : (((∏ p : κ × ι, (y p.1 p.2).den : ℕ) : ℚ) • y) k i = ((d * (y k i).num : ℤ) : ℚ) := by
    rw [hd, Matrix.smul_apply, smul_eq_mul]; push_cast
    rw [← Rat.den_mul_eq_num]; ring
  rw [this]
  exact isIntegral_algebraMap (R := ℤ) (x := d * (y k i).num)

theorem level_ch {R : ℕ} {φ : Matrix κ ι ℚ → ℂ} (h : HasLevel R φ) {y : Matrix κ ι ℚ}
    (hy : IntM ((R : ℚ) • y)) : HasLevel R fun x => φ x * ech (pr x y) := by
  refine ⟨fun x hx => h.1 x (left_ne_zero_of_mul hx), fun x z hz => ?_⟩
  simp only
  rw [h.2 x z hz, pr_add_left, ech_add, pr_smul_swap, ech_pr_int hz hy, mul_one]

def ft (φ : Matrix κ ι ℚ → ℂ) (y : Matrix κ ι ℚ) : ℂ := haar fun x => φ x * ech (pr x y)

theorem ft_eq [DecidableEq κ] [DecidableEq ι] {R : ℕ} (hR : 0 < R) {φ : Matrix κ ι ℚ → ℂ}
    (h : HasLevel R φ) {y : Matrix κ ι ℚ} (hy : IntM ((R : ℚ) • y)) :
    ft φ y = ((R : ℂ) ^ (Fintype.card κ * Fintype.card ι))⁻¹ *
      ∑ n : κ → ι → Fin (R * R), φ (rep R n) * ech (pr (rep R n) y) :=
  GlobalTheory.T.schwartzBruhatIntegral_eq_sum_residueRepresentatives κ ι R _ hR (level_ch h hy)

theorem ft_supp {R : ℕ} (hR : 0 < R) {φ : Matrix κ ι ℚ → ℂ}
    (h : HasLevel R φ) (y : Matrix κ ι ℚ) (hy : ft φ y ≠ 0) : IntM ((R : ℚ) • y) := by
  classical
  intro k i
  obtain ⟨S, hS, hSy⟩ := exists_den y
  have hsb : IsSB fun x => φ x * ech (pr x y) := by
    refine ⟨R * S, Nat.mul_pos hR hS, level_ch (level_mul h S) ?_⟩
    rw [Nat.cast_mul, ← smul_smul]; exact intM_nsmul hSy R
  obtain ⟨-, -, -, -, -, hsm, -, htr⟩ := GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ κ ι _ _ hsb hsb
  set z : Matrix κ ι ℚ := -Matrix.single k i 1 with hz
  have hzi : IntM (-z) := by
    intro k' i'
    simp only [hz, neg_neg, Matrix.single_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  have h1 := (htr ((R : ℚ) • z)).2
  have h2 : (fun x => φ (x - (R : ℚ) • z) * ech (pr (x - (R : ℚ) • z) y)) =
      ech (((R : ℚ) • y) k i) • fun x => φ x * ech (pr x y) := by
    ext x
    have h3 : pr (-z) ((R : ℚ) • y) = ((R : ℚ) • y) k i := by
      generalize (R : ℚ) • y = w
      rw [hz, neg_neg]
      simp [pr, dotProduct, Matrix.single_apply, ite_and]
    rw [sub_eq_add_neg, ← smul_neg, h.2 x _ hzi, pr_add_left, ech_add, pr_smul_swap, h3]
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  beta_reduce at h1
  rw [h2, hsm] at h1
  have h4 : ech (((R : ℚ) • y) k i) = 1 := by
    have : ech (((R : ℚ) • y) k i) * ft φ y = 1 * ft φ y := by rw [one_mul]; exact h1
    exact mul_right_cancel₀ hy this
  obtain ⟨m, hm⟩ := (ech_eq_one_iff _).1 h4
  rw [hm]
  exact isIntegral_algebraMap (R := ℤ) (x := m)

theorem ft_level {R : ℕ} (hR : 0 < R) {φ : Matrix κ ι ℚ → ℂ} (h : HasLevel R φ) (c : ℂ) :
    HasLevel R fun y => c * ft φ y := by
  refine ⟨fun y hy => ft_supp hR h y (right_ne_zero_of_mul hy), fun y z hz => ?_⟩
  simp only [ft]
  congr 2
  ext x
  by_cases hx : φ x = 0
  · simp [hx]
  · rw [pr_comm, pr_add_left, ech_add, pr_smul_swap, ech_pr_int hz (h.1 x hx), mul_one, pr_comm]

theorem level_mul_conj {R : ℕ} {φ ψ : Matrix κ ι ℚ → ℂ} (h : HasLevel R φ) (h' : HasLevel R ψ) :
    HasLevel R fun x => φ x * conj (ψ x) :=
  ⟨fun x hx => h.1 x (left_ne_zero_of_mul hx), fun x z hz => by simp only [h.2 x z hz, h'.2 x z hz]⟩

theorem intM_rep {R : ℕ} (hR : 0 < R) (n : κ → ι → Fin (R * R)) : IntM ((R : ℚ) • rep R n) := by
  refine (intM_iff _).2 ⟨fun k i => ((n k i : ℕ) : ℤ), ?_⟩
  have : (R : ℚ) ≠ 0 := by exact_mod_cast hR.ne'
  ext k i; simp [rep, zm]; field_simp

theorem plancherel {R : ℕ} (hR : 0 < R) {φ ψ : Matrix κ ι ℚ → ℂ} (h : HasLevel R φ)
    (h' : HasLevel R ψ) (c : ℂ) (hc : c * conj c = 1) :
    ip (fun y => c * ft φ y) (fun y => c * ft ψ y) = ip φ ψ := by
  classical
  unfold ip
  rw [GlobalTheory.T.schwartzBruhatIntegral_eq_sum_residueRepresentatives κ ι R _ hR (level_mul_conj (ft_level hR h c) (ft_level hR h' c)),
    GlobalTheory.T.schwartzBruhatIntegral_eq_sum_residueRepresentatives κ ι R _ hR (level_mul_conj h h')]
  congr 1
  set V : ℂ := (R : ℂ) ^ (Fintype.card κ * Fintype.card ι) with hV
  have hV0 : V ≠ 0 := pow_ne_zero _ (by exact_mod_cast hR.ne')
  have hVc : conj V = V := by simp [hV]
  have key : ∀ n : κ → ι → Fin (R * R), c * ft φ (rep R n) * conj (c * ft ψ (rep R n)) =
      ∑ a : κ → ι → Fin (R * R), ∑ b : κ → ι → Fin (R * R),
        (V ^ 2)⁻¹ * (φ (rep R a) * conj (ψ (rep R b))) *
          ech (∑ k, (rep R a k - rep R b k) ⬝ᵥ rep R n k) := by
    intro n
    rw [ft_eq hR h (intM_rep hR n), ft_eq hR h' (intM_rep hR n), ← hV, map_mul, map_mul, map_inv₀,
      hVc, map_sum]
    have e : ∀ A B : ℂ, c * (V⁻¹ * A) * (conj c * (V⁻¹ * B)) = (V ^ 2)⁻¹ * (A * B) := by
      intro A B
      calc _ = (c * conj c) * ((V ^ 2)⁻¹ * (A * B)) := by rw [sq, mul_inv]; ring
        _ = _ := by rw [hc, one_mul]
    rw [e, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    have : (∑ k, (rep R a k - rep R b k) ⬝ᵥ rep R n k) =
        pr (rep R a) (rep R n) + -pr (rep R b) (rep R n) := by
      rw [← sub_eq_add_neg, ← pr_sub_left]; rfl
    rw [this, ech_add, map_mul, conj_ech]; ring
  simp only [key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, sum_ech_rep κ ι R hR, ← hV, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  field_simp

theorem thS_eq [DecidableEq ι] (φ : Matrix κ ι ℚ → ℂ) (τ : Matrix ι ι ℂ) (ζ : κ → ι → ℂ) :
    thS φ τ ζ = ∑' x : Matrix κ ι ℚ, φ x * ∏ k, gs τ (ζ k) (x k) := by
  simp only [thS, gs, ← Complex.exp_sum, Finset.mul_sum]

theorem tsum_supp {R : ℕ} (hR : 0 < R) {ψ : Matrix κ ι ℚ → ℂ} (h : HasLevel R ψ)
    (G : Matrix κ ι ℚ → ℂ) :
    ∑' y, ψ y * G y = ∑' m : κ → ι → ℤ, ψ ((R : ℚ)⁻¹ • zm m) * G ((R : ℚ)⁻¹ • zm m) := by
  have hR0 : (R : ℚ) ≠ 0 := by exact_mod_cast hR.ne'
  have hinj : Function.Injective fun m : κ → ι → ℤ => (R : ℚ)⁻¹ • zm m := by
    intro m m' hm
    ext k i
    have := congrFun (congrFun hm k) i
    simpa [zm, hR.ne'] using this
  refine (hinj.tsum_eq (f := fun y => ψ y * G y) ?_).symm
  intro y hy
  obtain ⟨m, hm⟩ := (intM_iff _).1 (h.1 y (left_ne_zero_of_mul hy))
  exact ⟨m, by simp only [← hm, smul_smul, inv_mul_cancel₀ hR0, one_smul]⟩

theorem spDen_J [DecidableEq ι] (τ : Matrix ι ι ℂ) : spDen (Matrix.J ι ℚ) τ = τ := by
  have h1 : qm (1 : Matrix ι ι ℚ) = 1 := by
    ext i j; simp [qm, Matrix.one_apply]; split_ifs <;> simp
  have h0 : qm (0 : Matrix ι ι ℚ) = 0 := by ext i j; simp [qm]
  simp [spDen, Matrix.J, h1, h0]

theorem qm_J [DecidableEq ι] : qm (Matrix.J ι ℚ).toBlocks₂₁ = 1 := by
  ext i j; simp [qm, Matrix.J, Matrix.one_apply]; split_ifs <;> simp

theorem spAct_J [DecidableEq ι] (τ : Matrix ι ι ℂ) : spAct (Matrix.J ι ℚ) τ = -τ⁻¹ := by
  have h1 : qm (-1 : Matrix ι ι ℚ) = -1 := by
    ext i j; simp [qm, Matrix.one_apply]; split_ifs <;> simp
  have h0 : qm (0 : Matrix ι ι ℚ) = 0 := by ext i j; simp [qm]
  rw [spAct, spDen_J]
  simp [Matrix.J, h1, h0]

theorem trans_J [DecidableEq ι] {p : ℕ} (hp : Fintype.card κ = p + p) {R : ℕ} (hR : 0 < R)
    {φ : Matrix κ ι ℚ → ℂ} (h : HasLevel R φ) :
    TransS (Matrix.J ι ℚ) φ fun y => I ^ (Fintype.card ι * p) * ft φ y := by
  classical
  intro τ hτ ζ
  have hR0 : (R : ℚ) ≠ 0 := by exact_mod_cast hR.ne'
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  obtain ⟨hd, hs, -⟩ := GlobalTheory.T.symplecticSiegelAction_mem_upperHalfSpace_and_cocycle ι _ (SymplecticGroup.J_mem ι ℚ) τ hτ
  rw [spAct_J] at hs
  rw [spDen_J] at hd
  obtain ⟨c, hc, hrow⟩ := GlobalTheory.T.poisson_summation_thetaSeriesRowTerm_coset ι R hR τ hτ hs (Ne.isUnit hd)
  rw [spAct_J, spDen_J, qm_J, Matrix.mul_one, thS_eq, thS_eq,
    tsum_supp hR (ft_level hR h _)]
  have hsum : Summable fun x : Matrix κ ι ℚ => φ x * ∏ k, gs τ (ζ k) (x k) := by
    have := (GlobalTheory.SW.SiegelSum.summable_norm_thetaTerm κ ι φ ⟨R, hR, h⟩ τ hτ ζ).of_norm
    simpa only [gs, ← Complex.exp_sum, Finset.mul_sum] using this
  rw [GlobalTheory.T.tsum_schwartzBruhatLevel_eq_sum_residueCosets κ ι R φ _ hR h hsum]
  set V : ℂ := (R : ℂ) ^ (Fintype.card κ * Fintype.card ι) with hV
  set T : (κ → ι → Fin (R * R)) → κ → (ι → ℤ) → ℂ := fun n k m =>
    ech (rep R n k ⬝ᵥ ((R : ℚ)⁻¹ • zv m)) * gs (-τ⁻¹) (ζ k ᵥ* τ⁻¹) ((R : ℚ)⁻¹ • zv m) with hT
  have hTs : ∀ n k, Summable fun m => ‖T n k m‖ := fun n k => by
    simpa only [hT, norm_mul, norm_ech, one_mul] using (hrow 0 (ζ k)).2.1
  have hconst : τ.det ^ p * c ^ (p + p) = I ^ (Fintype.card ι * p) * V⁻¹ := by
    have hV0 : V ≠ 0 := pow_ne_zero _ hRc
    have h1 : (c ^ 2 * (((-I) * (R : ℂ) ^ 2) ^ Fintype.card ι * τ.det)) ^ p = 1 := by
      rw [hc, one_pow]
    have h2 : ((-I) * I) ^ (Fintype.card ι * p) = 1 := by simp
    rw [eq_mul_inv_iff_mul_eq₀ hV0, hV, hp]
    calc _ = τ.det ^ p * c ^ (p + p) * (R : ℂ) ^ ((p + p) * Fintype.card ι) *
          ((-I) * I) ^ (Fintype.card ι * p) := by rw [h2, mul_one]
      _ = I ^ (Fintype.card ι * p) *
          (c ^ 2 * (((-I) * (R : ℂ) ^ 2) ^ Fintype.card ι * τ.det)) ^ p := by
        simp only [mul_pow, ← pow_mul]; ring
      _ = _ := by rw [h1, mul_one]
  have hl : ∀ m : κ → ι → ℤ, I ^ (Fintype.card ι * p) * ft φ ((R : ℚ)⁻¹ • zm m) *
      ∏ k, gs (-τ⁻¹) (ζ k ᵥ* τ⁻¹) (((R : ℚ)⁻¹ • zm m) k) =
      ∑ n : κ → ι → Fin (R * R), (I ^ (Fintype.card ι * p) * V⁻¹ * φ (rep R n)) *
        ∏ k, T n k (m k) := by
    intro m
    have hm : IntM ((R : ℚ) • (R : ℚ)⁻¹ • zm m) := by
      rw [smul_smul, mul_inv_cancel₀ hR0, one_smul]; exact (intM_iff _).2 ⟨m, rfl⟩
    rw [ft_eq hR h hm, ← hV, ← mul_assoc, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hT, Finset.prod_mul_distrib, pr, ech_sum, mul_assoc]
    rfl
  simp only [hl]
  rw [Summable.tsum_finsetSum fun n _ =>
    ((tsum_pi_prod κ _ (T n) (hTs n)).1.of_norm.mul_left _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [tsum_mul_left, (tsum_pi_prod κ _ (T n) (hTs n)).2]
  have hr := (tsum_pi_prod κ _ (fun k (m : ι → ℤ) => gs τ (ζ k) (rep R n k + (R : ℚ) • zv m))
    (fun k => (hrow _ _).1)).2
  have hr' : ∑' m : κ → ι → ℤ, ∏ k, gs τ (ζ k) ((rep R n + (R : ℚ) • zm m) k) =
      ∏ k, ∑' m : ι → ℤ, gs τ (ζ k) (rep R n k + (R : ℚ) • zv m) := hr
  have hp2 : Fintype.card κ / 2 = p := by omega
  have hprod : cexp (π * I * ∑ k, ζ k ⬝ᵥ τ⁻¹ *ᵥ ζ k) *
      ∏ k, ∑' m : ι → ℤ, gs τ (ζ k) (rep R n k + (R : ℚ) • zv m) =
      c ^ (p + p) * ∏ k, ∑' m, T n k m := by
    rw [Finset.mul_sum, Complex.exp_sum, ← Finset.prod_mul_distrib, ← hp, ← Finset.card_univ,
      ← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => (hrow _ _).2.2
  rw [hr', hp2, ← hconst]
  linear_combination (-(τ.det ^ p * φ (rep R n))) * hprod

theorem exists_trans_J : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι],
    Even (Fintype.card κ) → ∃ ω : (Matrix κ ι ℚ → ℂ) → (Matrix κ ι ℚ → ℂ), ∀ φ, IsSB φ →
      IsSB (ω φ) ∧ TransS (Matrix.J ι ℚ) φ (ω φ) ∧
        ∀ φ', IsSB φ' → ip (ω φ) (ω φ') = ip φ φ' := by
  intro κ ι _ _ _ ⟨p, hp⟩
  refine ⟨fun φ y => I ^ (Fintype.card ι * p) * ft φ y, fun φ ⟨R, hR, h⟩ =>
    ⟨⟨R, hR, ft_level hR h _⟩, trans_J hp hR h, fun φ' ⟨S, hS, h'⟩ => ?_⟩⟩
  refine plancherel (Nat.mul_pos hR hS) (level_mul h S) (by rw [mul_comm]; exact level_mul h' R) _ ?_
  rw [map_pow, ← mul_pow]; simp

end

end GlobalTheory.SW.FourierJ
